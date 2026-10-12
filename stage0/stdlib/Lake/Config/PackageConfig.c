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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___boxed(lean_object*, lean_object*);
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
static uint8_t l_Lake_PackageConfig_instConfigInfo___closed__13;
static lean_once_cell_t l_Lake_PackageConfig_instConfigInfo___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_PackageConfig_instConfigInfo___closed__14;
static lean_once_cell_t l_Lake_PackageConfig_instConfigInfo___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_instConfigInfo___closed__15;
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
lean_object* l_Lake_instInhabitedPackageConfig_default___redArg(){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___redArg___closed__8, &l_Lake_instInhabitedPackageConfig_default___redArg___closed__8_once, _init_l_Lake_instInhabitedPackageConfig_default___redArg___closed__8);
return v___x_46_;
}
}
LEAN_EXPORT void l_Lake_instInhabitedPackageConfig_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_47_;
v_res_47_ = l_Lake_instInhabitedPackageConfig_default___redArg();
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___boxed(lean_object* v___dummy_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lake_instInhabitedPackageConfig_default___redArg();
return v_res_49_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageConfig_default___closed__0(void){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lake_instInhabitedPackageConfig_default___redArg();
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default(lean_object* v_p_51_, lean_object* v_n_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___closed__0, &l_Lake_instInhabitedPackageConfig_default___closed__0_once, _init_l_Lake_instInhabitedPackageConfig_default___closed__0);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___boxed(lean_object* v_p_54_, lean_object* v_n_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_instInhabitedPackageConfig_default(v_p_54_, v_n_55_);
lean_dec(v_n_55_);
lean_dec(v_p_54_);
return v_res_56_;
}
}
lean_object* l_Lake_instInhabitedPackageConfig___redArg(){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___closed__0, &l_Lake_instInhabitedPackageConfig_default___closed__0_once, _init_l_Lake_instInhabitedPackageConfig_default___closed__0);
return v___x_58_;
}
}
LEAN_EXPORT void l_Lake_instInhabitedPackageConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_59_;
v_res_59_ = l_Lake_instInhabitedPackageConfig___redArg();
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___redArg___boxed(lean_object* v___dummy_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lake_instInhabitedPackageConfig___redArg();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig(lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___closed__0, &l_Lake_instInhabitedPackageConfig_default___closed__0_once, _init_l_Lake_instInhabitedPackageConfig_default___closed__0);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___boxed(lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lake_instInhabitedPackageConfig(v_a_65_, v_a_66_);
lean_dec(v_a_66_);
lean_dec(v_a_65_);
return v_res_67_;
}
}
uint8_t l_Lake_PackageConfig_bootstrap___proj___redArg___lam__0(lean_object* v_cfg_68_){
_start:
{
uint8_t v_bootstrap_69_; 
v_bootstrap_69_ = lean_ctor_get_uint8(v_cfg_68_, sizeof(void*)*28);
return v_bootstrap_69_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_bootstrap___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_68_ = stack[0].m_obj;
uint8_t v_res_70_;
v_res_70_ = l_Lake_PackageConfig_bootstrap___proj___redArg___lam__0(v_cfg_68_);
stack->m_num = v_res_70_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__0___boxed(lean_object* v_cfg_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Lake_PackageConfig_bootstrap___proj___redArg___lam__0(v_cfg_71_);
lean_dec_ref(v_cfg_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1(uint8_t v_val_74_, lean_object* v_cfg_75_){
_start:
{
lean_object* v_toWorkspaceConfig_76_; lean_object* v_toLeanConfig_77_; lean_object* v_extraDepTargets_78_; uint8_t v_precompileModules_79_; lean_object* v_moreGlobalServerArgs_80_; lean_object* v_srcDir_81_; lean_object* v_buildDir_82_; lean_object* v_leanLibDir_83_; lean_object* v_nativeLibDir_84_; lean_object* v_binDir_85_; lean_object* v_irDir_86_; lean_object* v_releaseRepo_87_; lean_object* v_buildArchive_88_; uint8_t v_preferReleaseBuild_89_; lean_object* v_testDriver_90_; lean_object* v_testDriverArgs_91_; lean_object* v_lintDriver_92_; lean_object* v_lintDriverArgs_93_; lean_object* v_version_94_; lean_object* v_versionTags_95_; lean_object* v_description_96_; lean_object* v_keywords_97_; lean_object* v_homepage_98_; lean_object* v_license_99_; lean_object* v_licenseFiles_100_; lean_object* v_readmeFile_101_; uint8_t v_reservoir_102_; lean_object* v_enableArtifactCache_x3f_103_; lean_object* v_restoreAllArtifacts_x3f_104_; uint8_t v_libPrefixOnWindows_105_; uint8_t v_allowImportAll_106_; lean_object* v_builtinLint_x3f_107_; lean_object* v_checks_108_; uint8_t v_fixedToolchain_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
v_toWorkspaceConfig_76_ = lean_ctor_get(v_cfg_75_, 0);
v_toLeanConfig_77_ = lean_ctor_get(v_cfg_75_, 1);
v_extraDepTargets_78_ = lean_ctor_get(v_cfg_75_, 2);
v_precompileModules_79_ = lean_ctor_get_uint8(v_cfg_75_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_80_ = lean_ctor_get(v_cfg_75_, 3);
v_srcDir_81_ = lean_ctor_get(v_cfg_75_, 4);
v_buildDir_82_ = lean_ctor_get(v_cfg_75_, 5);
v_leanLibDir_83_ = lean_ctor_get(v_cfg_75_, 6);
v_nativeLibDir_84_ = lean_ctor_get(v_cfg_75_, 7);
v_binDir_85_ = lean_ctor_get(v_cfg_75_, 8);
v_irDir_86_ = lean_ctor_get(v_cfg_75_, 9);
v_releaseRepo_87_ = lean_ctor_get(v_cfg_75_, 10);
v_buildArchive_88_ = lean_ctor_get(v_cfg_75_, 11);
v_preferReleaseBuild_89_ = lean_ctor_get_uint8(v_cfg_75_, sizeof(void*)*28 + 2);
v_testDriver_90_ = lean_ctor_get(v_cfg_75_, 12);
v_testDriverArgs_91_ = lean_ctor_get(v_cfg_75_, 13);
v_lintDriver_92_ = lean_ctor_get(v_cfg_75_, 14);
v_lintDriverArgs_93_ = lean_ctor_get(v_cfg_75_, 15);
v_version_94_ = lean_ctor_get(v_cfg_75_, 16);
v_versionTags_95_ = lean_ctor_get(v_cfg_75_, 17);
v_description_96_ = lean_ctor_get(v_cfg_75_, 18);
v_keywords_97_ = lean_ctor_get(v_cfg_75_, 19);
v_homepage_98_ = lean_ctor_get(v_cfg_75_, 20);
v_license_99_ = lean_ctor_get(v_cfg_75_, 21);
v_licenseFiles_100_ = lean_ctor_get(v_cfg_75_, 22);
v_readmeFile_101_ = lean_ctor_get(v_cfg_75_, 23);
v_reservoir_102_ = lean_ctor_get_uint8(v_cfg_75_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_103_ = lean_ctor_get(v_cfg_75_, 24);
v_restoreAllArtifacts_x3f_104_ = lean_ctor_get(v_cfg_75_, 25);
v_libPrefixOnWindows_105_ = lean_ctor_get_uint8(v_cfg_75_, sizeof(void*)*28 + 4);
v_allowImportAll_106_ = lean_ctor_get_uint8(v_cfg_75_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_107_ = lean_ctor_get(v_cfg_75_, 26);
v_checks_108_ = lean_ctor_get(v_cfg_75_, 27);
v_fixedToolchain_109_ = lean_ctor_get_uint8(v_cfg_75_, sizeof(void*)*28 + 6);
v_isSharedCheck_116_ = !lean_is_exclusive(v_cfg_75_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v_cfg_75_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_checks_108_);
lean_inc(v_builtinLint_x3f_107_);
lean_inc(v_restoreAllArtifacts_x3f_104_);
lean_inc(v_enableArtifactCache_x3f_103_);
lean_inc(v_readmeFile_101_);
lean_inc(v_licenseFiles_100_);
lean_inc(v_license_99_);
lean_inc(v_homepage_98_);
lean_inc(v_keywords_97_);
lean_inc(v_description_96_);
lean_inc(v_versionTags_95_);
lean_inc(v_version_94_);
lean_inc(v_lintDriverArgs_93_);
lean_inc(v_lintDriver_92_);
lean_inc(v_testDriverArgs_91_);
lean_inc(v_testDriver_90_);
lean_inc(v_buildArchive_88_);
lean_inc(v_releaseRepo_87_);
lean_inc(v_irDir_86_);
lean_inc(v_binDir_85_);
lean_inc(v_nativeLibDir_84_);
lean_inc(v_leanLibDir_83_);
lean_inc(v_buildDir_82_);
lean_inc(v_srcDir_81_);
lean_inc(v_moreGlobalServerArgs_80_);
lean_inc(v_extraDepTargets_78_);
lean_inc(v_toLeanConfig_77_);
lean_inc(v_toWorkspaceConfig_76_);
lean_dec(v_cfg_75_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_toWorkspaceConfig_76_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_toLeanConfig_77_);
lean_ctor_set(v_reuseFailAlloc_115_, 2, v_extraDepTargets_78_);
lean_ctor_set(v_reuseFailAlloc_115_, 3, v_moreGlobalServerArgs_80_);
lean_ctor_set(v_reuseFailAlloc_115_, 4, v_srcDir_81_);
lean_ctor_set(v_reuseFailAlloc_115_, 5, v_buildDir_82_);
lean_ctor_set(v_reuseFailAlloc_115_, 6, v_leanLibDir_83_);
lean_ctor_set(v_reuseFailAlloc_115_, 7, v_nativeLibDir_84_);
lean_ctor_set(v_reuseFailAlloc_115_, 8, v_binDir_85_);
lean_ctor_set(v_reuseFailAlloc_115_, 9, v_irDir_86_);
lean_ctor_set(v_reuseFailAlloc_115_, 10, v_releaseRepo_87_);
lean_ctor_set(v_reuseFailAlloc_115_, 11, v_buildArchive_88_);
lean_ctor_set(v_reuseFailAlloc_115_, 12, v_testDriver_90_);
lean_ctor_set(v_reuseFailAlloc_115_, 13, v_testDriverArgs_91_);
lean_ctor_set(v_reuseFailAlloc_115_, 14, v_lintDriver_92_);
lean_ctor_set(v_reuseFailAlloc_115_, 15, v_lintDriverArgs_93_);
lean_ctor_set(v_reuseFailAlloc_115_, 16, v_version_94_);
lean_ctor_set(v_reuseFailAlloc_115_, 17, v_versionTags_95_);
lean_ctor_set(v_reuseFailAlloc_115_, 18, v_description_96_);
lean_ctor_set(v_reuseFailAlloc_115_, 19, v_keywords_97_);
lean_ctor_set(v_reuseFailAlloc_115_, 20, v_homepage_98_);
lean_ctor_set(v_reuseFailAlloc_115_, 21, v_license_99_);
lean_ctor_set(v_reuseFailAlloc_115_, 22, v_licenseFiles_100_);
lean_ctor_set(v_reuseFailAlloc_115_, 23, v_readmeFile_101_);
lean_ctor_set(v_reuseFailAlloc_115_, 24, v_enableArtifactCache_x3f_103_);
lean_ctor_set(v_reuseFailAlloc_115_, 25, v_restoreAllArtifacts_x3f_104_);
lean_ctor_set(v_reuseFailAlloc_115_, 26, v_builtinLint_x3f_107_);
lean_ctor_set(v_reuseFailAlloc_115_, 27, v_checks_108_);
lean_ctor_set_uint8(v_reuseFailAlloc_115_, sizeof(void*)*28 + 1, v_precompileModules_79_);
lean_ctor_set_uint8(v_reuseFailAlloc_115_, sizeof(void*)*28 + 2, v_preferReleaseBuild_89_);
lean_ctor_set_uint8(v_reuseFailAlloc_115_, sizeof(void*)*28 + 3, v_reservoir_102_);
lean_ctor_set_uint8(v_reuseFailAlloc_115_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_105_);
lean_ctor_set_uint8(v_reuseFailAlloc_115_, sizeof(void*)*28 + 5, v_allowImportAll_106_);
lean_ctor_set_uint8(v_reuseFailAlloc_115_, sizeof(void*)*28 + 6, v_fixedToolchain_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*28, v_val_74_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT void l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_74_ = stack[0].m_num;
lean_object* v_cfg_75_ = stack[1].m_obj;
lean_object* v_res_117_;
v_res_117_ = l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1(v_val_74_, v_cfg_75_);
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1___boxed(lean_object* v_val_118_, lean_object* v_cfg_119_){
_start:
{
uint8_t v_val_143__boxed_120_; lean_object* v_res_121_; 
v_val_143__boxed_120_ = lean_unbox(v_val_118_);
v_res_121_ = l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1(v_val_143__boxed_120_, v_cfg_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__2(lean_object* v_f_122_, lean_object* v_cfg_123_){
_start:
{
lean_object* v_toWorkspaceConfig_124_; lean_object* v_toLeanConfig_125_; uint8_t v_bootstrap_126_; lean_object* v_extraDepTargets_127_; uint8_t v_precompileModules_128_; lean_object* v_moreGlobalServerArgs_129_; lean_object* v_srcDir_130_; lean_object* v_buildDir_131_; lean_object* v_leanLibDir_132_; lean_object* v_nativeLibDir_133_; lean_object* v_binDir_134_; lean_object* v_irDir_135_; lean_object* v_releaseRepo_136_; lean_object* v_buildArchive_137_; uint8_t v_preferReleaseBuild_138_; lean_object* v_testDriver_139_; lean_object* v_testDriverArgs_140_; lean_object* v_lintDriver_141_; lean_object* v_lintDriverArgs_142_; lean_object* v_version_143_; lean_object* v_versionTags_144_; lean_object* v_description_145_; lean_object* v_keywords_146_; lean_object* v_homepage_147_; lean_object* v_license_148_; lean_object* v_licenseFiles_149_; lean_object* v_readmeFile_150_; uint8_t v_reservoir_151_; lean_object* v_enableArtifactCache_x3f_152_; lean_object* v_restoreAllArtifacts_x3f_153_; uint8_t v_libPrefixOnWindows_154_; uint8_t v_allowImportAll_155_; lean_object* v_builtinLint_x3f_156_; lean_object* v_checks_157_; uint8_t v_fixedToolchain_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_168_; 
v_toWorkspaceConfig_124_ = lean_ctor_get(v_cfg_123_, 0);
v_toLeanConfig_125_ = lean_ctor_get(v_cfg_123_, 1);
v_bootstrap_126_ = lean_ctor_get_uint8(v_cfg_123_, sizeof(void*)*28);
v_extraDepTargets_127_ = lean_ctor_get(v_cfg_123_, 2);
v_precompileModules_128_ = lean_ctor_get_uint8(v_cfg_123_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_129_ = lean_ctor_get(v_cfg_123_, 3);
v_srcDir_130_ = lean_ctor_get(v_cfg_123_, 4);
v_buildDir_131_ = lean_ctor_get(v_cfg_123_, 5);
v_leanLibDir_132_ = lean_ctor_get(v_cfg_123_, 6);
v_nativeLibDir_133_ = lean_ctor_get(v_cfg_123_, 7);
v_binDir_134_ = lean_ctor_get(v_cfg_123_, 8);
v_irDir_135_ = lean_ctor_get(v_cfg_123_, 9);
v_releaseRepo_136_ = lean_ctor_get(v_cfg_123_, 10);
v_buildArchive_137_ = lean_ctor_get(v_cfg_123_, 11);
v_preferReleaseBuild_138_ = lean_ctor_get_uint8(v_cfg_123_, sizeof(void*)*28 + 2);
v_testDriver_139_ = lean_ctor_get(v_cfg_123_, 12);
v_testDriverArgs_140_ = lean_ctor_get(v_cfg_123_, 13);
v_lintDriver_141_ = lean_ctor_get(v_cfg_123_, 14);
v_lintDriverArgs_142_ = lean_ctor_get(v_cfg_123_, 15);
v_version_143_ = lean_ctor_get(v_cfg_123_, 16);
v_versionTags_144_ = lean_ctor_get(v_cfg_123_, 17);
v_description_145_ = lean_ctor_get(v_cfg_123_, 18);
v_keywords_146_ = lean_ctor_get(v_cfg_123_, 19);
v_homepage_147_ = lean_ctor_get(v_cfg_123_, 20);
v_license_148_ = lean_ctor_get(v_cfg_123_, 21);
v_licenseFiles_149_ = lean_ctor_get(v_cfg_123_, 22);
v_readmeFile_150_ = lean_ctor_get(v_cfg_123_, 23);
v_reservoir_151_ = lean_ctor_get_uint8(v_cfg_123_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_152_ = lean_ctor_get(v_cfg_123_, 24);
v_restoreAllArtifacts_x3f_153_ = lean_ctor_get(v_cfg_123_, 25);
v_libPrefixOnWindows_154_ = lean_ctor_get_uint8(v_cfg_123_, sizeof(void*)*28 + 4);
v_allowImportAll_155_ = lean_ctor_get_uint8(v_cfg_123_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_156_ = lean_ctor_get(v_cfg_123_, 26);
v_checks_157_ = lean_ctor_get(v_cfg_123_, 27);
v_fixedToolchain_158_ = lean_ctor_get_uint8(v_cfg_123_, sizeof(void*)*28 + 6);
v_isSharedCheck_168_ = !lean_is_exclusive(v_cfg_123_);
if (v_isSharedCheck_168_ == 0)
{
v___x_160_ = v_cfg_123_;
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_checks_157_);
lean_inc(v_builtinLint_x3f_156_);
lean_inc(v_restoreAllArtifacts_x3f_153_);
lean_inc(v_enableArtifactCache_x3f_152_);
lean_inc(v_readmeFile_150_);
lean_inc(v_licenseFiles_149_);
lean_inc(v_license_148_);
lean_inc(v_homepage_147_);
lean_inc(v_keywords_146_);
lean_inc(v_description_145_);
lean_inc(v_versionTags_144_);
lean_inc(v_version_143_);
lean_inc(v_lintDriverArgs_142_);
lean_inc(v_lintDriver_141_);
lean_inc(v_testDriverArgs_140_);
lean_inc(v_testDriver_139_);
lean_inc(v_buildArchive_137_);
lean_inc(v_releaseRepo_136_);
lean_inc(v_irDir_135_);
lean_inc(v_binDir_134_);
lean_inc(v_nativeLibDir_133_);
lean_inc(v_leanLibDir_132_);
lean_inc(v_buildDir_131_);
lean_inc(v_srcDir_130_);
lean_inc(v_moreGlobalServerArgs_129_);
lean_inc(v_extraDepTargets_127_);
lean_inc(v_toLeanConfig_125_);
lean_inc(v_toWorkspaceConfig_124_);
lean_dec(v_cfg_123_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_162_ = lean_box(v_bootstrap_126_);
v___x_163_ = lean_apply_1(v_f_122_, v___x_162_);
if (v_isShared_161_ == 0)
{
v___x_165_ = v___x_160_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_toWorkspaceConfig_124_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_toLeanConfig_125_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_extraDepTargets_127_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_moreGlobalServerArgs_129_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v_srcDir_130_);
lean_ctor_set(v_reuseFailAlloc_167_, 5, v_buildDir_131_);
lean_ctor_set(v_reuseFailAlloc_167_, 6, v_leanLibDir_132_);
lean_ctor_set(v_reuseFailAlloc_167_, 7, v_nativeLibDir_133_);
lean_ctor_set(v_reuseFailAlloc_167_, 8, v_binDir_134_);
lean_ctor_set(v_reuseFailAlloc_167_, 9, v_irDir_135_);
lean_ctor_set(v_reuseFailAlloc_167_, 10, v_releaseRepo_136_);
lean_ctor_set(v_reuseFailAlloc_167_, 11, v_buildArchive_137_);
lean_ctor_set(v_reuseFailAlloc_167_, 12, v_testDriver_139_);
lean_ctor_set(v_reuseFailAlloc_167_, 13, v_testDriverArgs_140_);
lean_ctor_set(v_reuseFailAlloc_167_, 14, v_lintDriver_141_);
lean_ctor_set(v_reuseFailAlloc_167_, 15, v_lintDriverArgs_142_);
lean_ctor_set(v_reuseFailAlloc_167_, 16, v_version_143_);
lean_ctor_set(v_reuseFailAlloc_167_, 17, v_versionTags_144_);
lean_ctor_set(v_reuseFailAlloc_167_, 18, v_description_145_);
lean_ctor_set(v_reuseFailAlloc_167_, 19, v_keywords_146_);
lean_ctor_set(v_reuseFailAlloc_167_, 20, v_homepage_147_);
lean_ctor_set(v_reuseFailAlloc_167_, 21, v_license_148_);
lean_ctor_set(v_reuseFailAlloc_167_, 22, v_licenseFiles_149_);
lean_ctor_set(v_reuseFailAlloc_167_, 23, v_readmeFile_150_);
lean_ctor_set(v_reuseFailAlloc_167_, 24, v_enableArtifactCache_x3f_152_);
lean_ctor_set(v_reuseFailAlloc_167_, 25, v_restoreAllArtifacts_x3f_153_);
lean_ctor_set(v_reuseFailAlloc_167_, 26, v_builtinLint_x3f_156_);
lean_ctor_set(v_reuseFailAlloc_167_, 27, v_checks_157_);
v___x_165_ = v_reuseFailAlloc_167_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
uint8_t v___x_166_; 
v___x_166_ = lean_unbox(v___x_163_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*28, v___x_166_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*28 + 1, v_precompileModules_128_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*28 + 2, v_preferReleaseBuild_138_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*28 + 3, v_reservoir_151_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_154_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*28 + 5, v_allowImportAll_155_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*28 + 6, v_fixedToolchain_158_);
return v___x_165_;
}
}
}
}
uint8_t l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3(lean_object* v_x_169_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_169_ = stack[0].m_obj;
uint8_t v_res_171_;
v_res_171_ = l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3(v_x_169_);
stack->m_num = v_res_171_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3___boxed(lean_object* v_x_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3(v_x_172_);
lean_dec_ref(v_x_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg(){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = ((lean_object*)(l_Lake_PackageConfig_bootstrap___proj___redArg___closed__4));
return v___x_185_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_bootstrap___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_186_;
v_res_186_ = l_Lake_PackageConfig_bootstrap___proj___redArg();
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___boxed(lean_object* v___dummy_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lake_PackageConfig_bootstrap___proj___redArg();
return v_res_188_;
}
}
static lean_object* _init_l_Lake_PackageConfig_bootstrap___proj___closed__0(void){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lake_PackageConfig_bootstrap___proj___redArg();
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object* v_p_190_, lean_object* v_n_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Lake_PackageConfig_bootstrap___proj___closed__0, &l_Lake_PackageConfig_bootstrap___proj___closed__0_once, _init_l_Lake_PackageConfig_bootstrap___proj___closed__0);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___boxed(lean_object* v_p_193_, lean_object* v_n_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lake_PackageConfig_bootstrap___proj(v_p_193_, v_n_194_);
lean_dec(v_n_194_);
lean_dec(v_p_193_);
return v_res_195_;
}
}
lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___redArg(){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_obj_once(&l_Lake_PackageConfig_bootstrap___proj___closed__0, &l_Lake_PackageConfig_bootstrap___proj___closed__0_once, _init_l_Lake_PackageConfig_bootstrap___proj___closed__0);
return v___x_197_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_bootstrap_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_198_;
v_res_198_ = l_Lake_PackageConfig_bootstrap_instConfigField___redArg();
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___redArg___boxed(lean_object* v___dummy_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_PackageConfig_bootstrap_instConfigField___redArg();
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField(lean_object* v_p_201_, lean_object* v_n_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_obj_once(&l_Lake_PackageConfig_bootstrap___proj___closed__0, &l_Lake_PackageConfig_bootstrap___proj___closed__0_once, _init_l_Lake_PackageConfig_bootstrap___proj___closed__0);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___boxed(lean_object* v_p_204_, lean_object* v_n_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lake_PackageConfig_bootstrap_instConfigField(v_p_204_, v_n_205_);
lean_dec(v_n_205_);
lean_dec(v_p_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0(lean_object* v_cfg_207_){
_start:
{
lean_object* v_extraDepTargets_208_; 
v_extraDepTargets_208_ = lean_ctor_get(v_cfg_207_, 2);
lean_inc_ref(v_extraDepTargets_208_);
return v_extraDepTargets_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0___boxed(lean_object* v_cfg_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0(v_cfg_209_);
lean_dec_ref(v_cfg_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__1(lean_object* v_val_211_, lean_object* v_cfg_212_){
_start:
{
lean_object* v_toWorkspaceConfig_213_; lean_object* v_toLeanConfig_214_; uint8_t v_bootstrap_215_; uint8_t v_precompileModules_216_; lean_object* v_moreGlobalServerArgs_217_; lean_object* v_srcDir_218_; lean_object* v_buildDir_219_; lean_object* v_leanLibDir_220_; lean_object* v_nativeLibDir_221_; lean_object* v_binDir_222_; lean_object* v_irDir_223_; lean_object* v_releaseRepo_224_; lean_object* v_buildArchive_225_; uint8_t v_preferReleaseBuild_226_; lean_object* v_testDriver_227_; lean_object* v_testDriverArgs_228_; lean_object* v_lintDriver_229_; lean_object* v_lintDriverArgs_230_; lean_object* v_version_231_; lean_object* v_versionTags_232_; lean_object* v_description_233_; lean_object* v_keywords_234_; lean_object* v_homepage_235_; lean_object* v_license_236_; lean_object* v_licenseFiles_237_; lean_object* v_readmeFile_238_; uint8_t v_reservoir_239_; lean_object* v_enableArtifactCache_x3f_240_; lean_object* v_restoreAllArtifacts_x3f_241_; uint8_t v_libPrefixOnWindows_242_; uint8_t v_allowImportAll_243_; lean_object* v_builtinLint_x3f_244_; lean_object* v_checks_245_; uint8_t v_fixedToolchain_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
v_toWorkspaceConfig_213_ = lean_ctor_get(v_cfg_212_, 0);
v_toLeanConfig_214_ = lean_ctor_get(v_cfg_212_, 1);
v_bootstrap_215_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*28);
v_precompileModules_216_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_217_ = lean_ctor_get(v_cfg_212_, 3);
v_srcDir_218_ = lean_ctor_get(v_cfg_212_, 4);
v_buildDir_219_ = lean_ctor_get(v_cfg_212_, 5);
v_leanLibDir_220_ = lean_ctor_get(v_cfg_212_, 6);
v_nativeLibDir_221_ = lean_ctor_get(v_cfg_212_, 7);
v_binDir_222_ = lean_ctor_get(v_cfg_212_, 8);
v_irDir_223_ = lean_ctor_get(v_cfg_212_, 9);
v_releaseRepo_224_ = lean_ctor_get(v_cfg_212_, 10);
v_buildArchive_225_ = lean_ctor_get(v_cfg_212_, 11);
v_preferReleaseBuild_226_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*28 + 2);
v_testDriver_227_ = lean_ctor_get(v_cfg_212_, 12);
v_testDriverArgs_228_ = lean_ctor_get(v_cfg_212_, 13);
v_lintDriver_229_ = lean_ctor_get(v_cfg_212_, 14);
v_lintDriverArgs_230_ = lean_ctor_get(v_cfg_212_, 15);
v_version_231_ = lean_ctor_get(v_cfg_212_, 16);
v_versionTags_232_ = lean_ctor_get(v_cfg_212_, 17);
v_description_233_ = lean_ctor_get(v_cfg_212_, 18);
v_keywords_234_ = lean_ctor_get(v_cfg_212_, 19);
v_homepage_235_ = lean_ctor_get(v_cfg_212_, 20);
v_license_236_ = lean_ctor_get(v_cfg_212_, 21);
v_licenseFiles_237_ = lean_ctor_get(v_cfg_212_, 22);
v_readmeFile_238_ = lean_ctor_get(v_cfg_212_, 23);
v_reservoir_239_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_240_ = lean_ctor_get(v_cfg_212_, 24);
v_restoreAllArtifacts_x3f_241_ = lean_ctor_get(v_cfg_212_, 25);
v_libPrefixOnWindows_242_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*28 + 4);
v_allowImportAll_243_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_244_ = lean_ctor_get(v_cfg_212_, 26);
v_checks_245_ = lean_ctor_get(v_cfg_212_, 27);
v_fixedToolchain_246_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*28 + 6);
v_isSharedCheck_253_ = !lean_is_exclusive(v_cfg_212_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; 
v_unused_254_ = lean_ctor_get(v_cfg_212_, 2);
lean_dec(v_unused_254_);
v___x_248_ = v_cfg_212_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_checks_245_);
lean_inc(v_builtinLint_x3f_244_);
lean_inc(v_restoreAllArtifacts_x3f_241_);
lean_inc(v_enableArtifactCache_x3f_240_);
lean_inc(v_readmeFile_238_);
lean_inc(v_licenseFiles_237_);
lean_inc(v_license_236_);
lean_inc(v_homepage_235_);
lean_inc(v_keywords_234_);
lean_inc(v_description_233_);
lean_inc(v_versionTags_232_);
lean_inc(v_version_231_);
lean_inc(v_lintDriverArgs_230_);
lean_inc(v_lintDriver_229_);
lean_inc(v_testDriverArgs_228_);
lean_inc(v_testDriver_227_);
lean_inc(v_buildArchive_225_);
lean_inc(v_releaseRepo_224_);
lean_inc(v_irDir_223_);
lean_inc(v_binDir_222_);
lean_inc(v_nativeLibDir_221_);
lean_inc(v_leanLibDir_220_);
lean_inc(v_buildDir_219_);
lean_inc(v_srcDir_218_);
lean_inc(v_moreGlobalServerArgs_217_);
lean_inc(v_toLeanConfig_214_);
lean_inc(v_toWorkspaceConfig_213_);
lean_dec(v_cfg_212_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 2, v_val_211_);
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_toWorkspaceConfig_213_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_toLeanConfig_214_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_val_211_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_moreGlobalServerArgs_217_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_srcDir_218_);
lean_ctor_set(v_reuseFailAlloc_252_, 5, v_buildDir_219_);
lean_ctor_set(v_reuseFailAlloc_252_, 6, v_leanLibDir_220_);
lean_ctor_set(v_reuseFailAlloc_252_, 7, v_nativeLibDir_221_);
lean_ctor_set(v_reuseFailAlloc_252_, 8, v_binDir_222_);
lean_ctor_set(v_reuseFailAlloc_252_, 9, v_irDir_223_);
lean_ctor_set(v_reuseFailAlloc_252_, 10, v_releaseRepo_224_);
lean_ctor_set(v_reuseFailAlloc_252_, 11, v_buildArchive_225_);
lean_ctor_set(v_reuseFailAlloc_252_, 12, v_testDriver_227_);
lean_ctor_set(v_reuseFailAlloc_252_, 13, v_testDriverArgs_228_);
lean_ctor_set(v_reuseFailAlloc_252_, 14, v_lintDriver_229_);
lean_ctor_set(v_reuseFailAlloc_252_, 15, v_lintDriverArgs_230_);
lean_ctor_set(v_reuseFailAlloc_252_, 16, v_version_231_);
lean_ctor_set(v_reuseFailAlloc_252_, 17, v_versionTags_232_);
lean_ctor_set(v_reuseFailAlloc_252_, 18, v_description_233_);
lean_ctor_set(v_reuseFailAlloc_252_, 19, v_keywords_234_);
lean_ctor_set(v_reuseFailAlloc_252_, 20, v_homepage_235_);
lean_ctor_set(v_reuseFailAlloc_252_, 21, v_license_236_);
lean_ctor_set(v_reuseFailAlloc_252_, 22, v_licenseFiles_237_);
lean_ctor_set(v_reuseFailAlloc_252_, 23, v_readmeFile_238_);
lean_ctor_set(v_reuseFailAlloc_252_, 24, v_enableArtifactCache_x3f_240_);
lean_ctor_set(v_reuseFailAlloc_252_, 25, v_restoreAllArtifacts_x3f_241_);
lean_ctor_set(v_reuseFailAlloc_252_, 26, v_builtinLint_x3f_244_);
lean_ctor_set(v_reuseFailAlloc_252_, 27, v_checks_245_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*28, v_bootstrap_215_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*28 + 1, v_precompileModules_216_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*28 + 2, v_preferReleaseBuild_226_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*28 + 3, v_reservoir_239_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_242_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*28 + 5, v_allowImportAll_243_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*28 + 6, v_fixedToolchain_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__2(lean_object* v_f_255_, lean_object* v_cfg_256_){
_start:
{
lean_object* v_toWorkspaceConfig_257_; lean_object* v_toLeanConfig_258_; uint8_t v_bootstrap_259_; lean_object* v_extraDepTargets_260_; uint8_t v_precompileModules_261_; lean_object* v_moreGlobalServerArgs_262_; lean_object* v_srcDir_263_; lean_object* v_buildDir_264_; lean_object* v_leanLibDir_265_; lean_object* v_nativeLibDir_266_; lean_object* v_binDir_267_; lean_object* v_irDir_268_; lean_object* v_releaseRepo_269_; lean_object* v_buildArchive_270_; uint8_t v_preferReleaseBuild_271_; lean_object* v_testDriver_272_; lean_object* v_testDriverArgs_273_; lean_object* v_lintDriver_274_; lean_object* v_lintDriverArgs_275_; lean_object* v_version_276_; lean_object* v_versionTags_277_; lean_object* v_description_278_; lean_object* v_keywords_279_; lean_object* v_homepage_280_; lean_object* v_license_281_; lean_object* v_licenseFiles_282_; lean_object* v_readmeFile_283_; uint8_t v_reservoir_284_; lean_object* v_enableArtifactCache_x3f_285_; lean_object* v_restoreAllArtifacts_x3f_286_; uint8_t v_libPrefixOnWindows_287_; uint8_t v_allowImportAll_288_; lean_object* v_builtinLint_x3f_289_; lean_object* v_checks_290_; uint8_t v_fixedToolchain_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
v_toWorkspaceConfig_257_ = lean_ctor_get(v_cfg_256_, 0);
v_toLeanConfig_258_ = lean_ctor_get(v_cfg_256_, 1);
v_bootstrap_259_ = lean_ctor_get_uint8(v_cfg_256_, sizeof(void*)*28);
v_extraDepTargets_260_ = lean_ctor_get(v_cfg_256_, 2);
v_precompileModules_261_ = lean_ctor_get_uint8(v_cfg_256_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_262_ = lean_ctor_get(v_cfg_256_, 3);
v_srcDir_263_ = lean_ctor_get(v_cfg_256_, 4);
v_buildDir_264_ = lean_ctor_get(v_cfg_256_, 5);
v_leanLibDir_265_ = lean_ctor_get(v_cfg_256_, 6);
v_nativeLibDir_266_ = lean_ctor_get(v_cfg_256_, 7);
v_binDir_267_ = lean_ctor_get(v_cfg_256_, 8);
v_irDir_268_ = lean_ctor_get(v_cfg_256_, 9);
v_releaseRepo_269_ = lean_ctor_get(v_cfg_256_, 10);
v_buildArchive_270_ = lean_ctor_get(v_cfg_256_, 11);
v_preferReleaseBuild_271_ = lean_ctor_get_uint8(v_cfg_256_, sizeof(void*)*28 + 2);
v_testDriver_272_ = lean_ctor_get(v_cfg_256_, 12);
v_testDriverArgs_273_ = lean_ctor_get(v_cfg_256_, 13);
v_lintDriver_274_ = lean_ctor_get(v_cfg_256_, 14);
v_lintDriverArgs_275_ = lean_ctor_get(v_cfg_256_, 15);
v_version_276_ = lean_ctor_get(v_cfg_256_, 16);
v_versionTags_277_ = lean_ctor_get(v_cfg_256_, 17);
v_description_278_ = lean_ctor_get(v_cfg_256_, 18);
v_keywords_279_ = lean_ctor_get(v_cfg_256_, 19);
v_homepage_280_ = lean_ctor_get(v_cfg_256_, 20);
v_license_281_ = lean_ctor_get(v_cfg_256_, 21);
v_licenseFiles_282_ = lean_ctor_get(v_cfg_256_, 22);
v_readmeFile_283_ = lean_ctor_get(v_cfg_256_, 23);
v_reservoir_284_ = lean_ctor_get_uint8(v_cfg_256_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_285_ = lean_ctor_get(v_cfg_256_, 24);
v_restoreAllArtifacts_x3f_286_ = lean_ctor_get(v_cfg_256_, 25);
v_libPrefixOnWindows_287_ = lean_ctor_get_uint8(v_cfg_256_, sizeof(void*)*28 + 4);
v_allowImportAll_288_ = lean_ctor_get_uint8(v_cfg_256_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_289_ = lean_ctor_get(v_cfg_256_, 26);
v_checks_290_ = lean_ctor_get(v_cfg_256_, 27);
v_fixedToolchain_291_ = lean_ctor_get_uint8(v_cfg_256_, sizeof(void*)*28 + 6);
v_isSharedCheck_299_ = !lean_is_exclusive(v_cfg_256_);
if (v_isSharedCheck_299_ == 0)
{
v___x_293_ = v_cfg_256_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_checks_290_);
lean_inc(v_builtinLint_x3f_289_);
lean_inc(v_restoreAllArtifacts_x3f_286_);
lean_inc(v_enableArtifactCache_x3f_285_);
lean_inc(v_readmeFile_283_);
lean_inc(v_licenseFiles_282_);
lean_inc(v_license_281_);
lean_inc(v_homepage_280_);
lean_inc(v_keywords_279_);
lean_inc(v_description_278_);
lean_inc(v_versionTags_277_);
lean_inc(v_version_276_);
lean_inc(v_lintDriverArgs_275_);
lean_inc(v_lintDriver_274_);
lean_inc(v_testDriverArgs_273_);
lean_inc(v_testDriver_272_);
lean_inc(v_buildArchive_270_);
lean_inc(v_releaseRepo_269_);
lean_inc(v_irDir_268_);
lean_inc(v_binDir_267_);
lean_inc(v_nativeLibDir_266_);
lean_inc(v_leanLibDir_265_);
lean_inc(v_buildDir_264_);
lean_inc(v_srcDir_263_);
lean_inc(v_moreGlobalServerArgs_262_);
lean_inc(v_extraDepTargets_260_);
lean_inc(v_toLeanConfig_258_);
lean_inc(v_toWorkspaceConfig_257_);
lean_dec(v_cfg_256_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_apply_1(v_f_255_, v_extraDepTargets_260_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 2, v___x_295_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_toWorkspaceConfig_257_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_toLeanConfig_258_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_moreGlobalServerArgs_262_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_srcDir_263_);
lean_ctor_set(v_reuseFailAlloc_298_, 5, v_buildDir_264_);
lean_ctor_set(v_reuseFailAlloc_298_, 6, v_leanLibDir_265_);
lean_ctor_set(v_reuseFailAlloc_298_, 7, v_nativeLibDir_266_);
lean_ctor_set(v_reuseFailAlloc_298_, 8, v_binDir_267_);
lean_ctor_set(v_reuseFailAlloc_298_, 9, v_irDir_268_);
lean_ctor_set(v_reuseFailAlloc_298_, 10, v_releaseRepo_269_);
lean_ctor_set(v_reuseFailAlloc_298_, 11, v_buildArchive_270_);
lean_ctor_set(v_reuseFailAlloc_298_, 12, v_testDriver_272_);
lean_ctor_set(v_reuseFailAlloc_298_, 13, v_testDriverArgs_273_);
lean_ctor_set(v_reuseFailAlloc_298_, 14, v_lintDriver_274_);
lean_ctor_set(v_reuseFailAlloc_298_, 15, v_lintDriverArgs_275_);
lean_ctor_set(v_reuseFailAlloc_298_, 16, v_version_276_);
lean_ctor_set(v_reuseFailAlloc_298_, 17, v_versionTags_277_);
lean_ctor_set(v_reuseFailAlloc_298_, 18, v_description_278_);
lean_ctor_set(v_reuseFailAlloc_298_, 19, v_keywords_279_);
lean_ctor_set(v_reuseFailAlloc_298_, 20, v_homepage_280_);
lean_ctor_set(v_reuseFailAlloc_298_, 21, v_license_281_);
lean_ctor_set(v_reuseFailAlloc_298_, 22, v_licenseFiles_282_);
lean_ctor_set(v_reuseFailAlloc_298_, 23, v_readmeFile_283_);
lean_ctor_set(v_reuseFailAlloc_298_, 24, v_enableArtifactCache_x3f_285_);
lean_ctor_set(v_reuseFailAlloc_298_, 25, v_restoreAllArtifacts_x3f_286_);
lean_ctor_set(v_reuseFailAlloc_298_, 26, v_builtinLint_x3f_289_);
lean_ctor_set(v_reuseFailAlloc_298_, 27, v_checks_290_);
lean_ctor_set_uint8(v_reuseFailAlloc_298_, sizeof(void*)*28, v_bootstrap_259_);
lean_ctor_set_uint8(v_reuseFailAlloc_298_, sizeof(void*)*28 + 1, v_precompileModules_261_);
lean_ctor_set_uint8(v_reuseFailAlloc_298_, sizeof(void*)*28 + 2, v_preferReleaseBuild_271_);
lean_ctor_set_uint8(v_reuseFailAlloc_298_, sizeof(void*)*28 + 3, v_reservoir_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_298_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_287_);
lean_ctor_set_uint8(v_reuseFailAlloc_298_, sizeof(void*)*28 + 5, v_allowImportAll_288_);
lean_ctor_set_uint8(v_reuseFailAlloc_298_, sizeof(void*)*28 + 6, v_fixedToolchain_291_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3(lean_object* v_x_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__0));
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3___boxed(lean_object* v_x_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3(v_x_302_);
lean_dec_ref(v_x_302_);
return v_res_303_;
}
}
lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg(){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__4));
return v___x_314_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_extraDepTargets___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_315_;
v_res_315_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg();
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___boxed(lean_object* v___dummy_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg();
return v_res_317_;
}
}
static lean_object* _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0(void){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg();
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object* v_p_319_, lean_object* v_n_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Lake_PackageConfig_extraDepTargets___proj___closed__0, &l_Lake_PackageConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object* v_p_322_, lean_object* v_n_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_322_, v_n_323_);
lean_dec(v_n_323_);
lean_dec(v_p_322_);
return v_res_324_;
}
}
lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg(){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_obj_once(&l_Lake_PackageConfig_extraDepTargets___proj___closed__0, &l_Lake_PackageConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0);
return v___x_326_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_327_;
v_res_327_ = l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg();
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg___boxed(lean_object* v___dummy_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg();
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object* v_p_330_, lean_object* v_n_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_obj_once(&l_Lake_PackageConfig_extraDepTargets___proj___closed__0, &l_Lake_PackageConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object* v_p_333_, lean_object* v_n_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lake_PackageConfig_extraDepTargets_instConfigField(v_p_333_, v_n_334_);
lean_dec(v_n_334_);
lean_dec(v_p_333_);
return v_res_335_;
}
}
uint8_t l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0(lean_object* v_cfg_336_){
_start:
{
uint8_t v_precompileModules_337_; 
v_precompileModules_337_ = lean_ctor_get_uint8(v_cfg_336_, sizeof(void*)*28 + 1);
return v_precompileModules_337_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_336_ = stack[0].m_obj;
uint8_t v_res_338_;
v_res_338_ = l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0(v_cfg_336_);
stack->m_num = v_res_338_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0___boxed(lean_object* v_cfg_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0(v_cfg_339_);
lean_dec_ref(v_cfg_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1(uint8_t v_val_342_, lean_object* v_cfg_343_){
_start:
{
lean_object* v_toWorkspaceConfig_344_; lean_object* v_toLeanConfig_345_; uint8_t v_bootstrap_346_; lean_object* v_extraDepTargets_347_; lean_object* v_moreGlobalServerArgs_348_; lean_object* v_srcDir_349_; lean_object* v_buildDir_350_; lean_object* v_leanLibDir_351_; lean_object* v_nativeLibDir_352_; lean_object* v_binDir_353_; lean_object* v_irDir_354_; lean_object* v_releaseRepo_355_; lean_object* v_buildArchive_356_; uint8_t v_preferReleaseBuild_357_; lean_object* v_testDriver_358_; lean_object* v_testDriverArgs_359_; lean_object* v_lintDriver_360_; lean_object* v_lintDriverArgs_361_; lean_object* v_version_362_; lean_object* v_versionTags_363_; lean_object* v_description_364_; lean_object* v_keywords_365_; lean_object* v_homepage_366_; lean_object* v_license_367_; lean_object* v_licenseFiles_368_; lean_object* v_readmeFile_369_; uint8_t v_reservoir_370_; lean_object* v_enableArtifactCache_x3f_371_; lean_object* v_restoreAllArtifacts_x3f_372_; uint8_t v_libPrefixOnWindows_373_; uint8_t v_allowImportAll_374_; lean_object* v_builtinLint_x3f_375_; lean_object* v_checks_376_; uint8_t v_fixedToolchain_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
v_toWorkspaceConfig_344_ = lean_ctor_get(v_cfg_343_, 0);
v_toLeanConfig_345_ = lean_ctor_get(v_cfg_343_, 1);
v_bootstrap_346_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*28);
v_extraDepTargets_347_ = lean_ctor_get(v_cfg_343_, 2);
v_moreGlobalServerArgs_348_ = lean_ctor_get(v_cfg_343_, 3);
v_srcDir_349_ = lean_ctor_get(v_cfg_343_, 4);
v_buildDir_350_ = lean_ctor_get(v_cfg_343_, 5);
v_leanLibDir_351_ = lean_ctor_get(v_cfg_343_, 6);
v_nativeLibDir_352_ = lean_ctor_get(v_cfg_343_, 7);
v_binDir_353_ = lean_ctor_get(v_cfg_343_, 8);
v_irDir_354_ = lean_ctor_get(v_cfg_343_, 9);
v_releaseRepo_355_ = lean_ctor_get(v_cfg_343_, 10);
v_buildArchive_356_ = lean_ctor_get(v_cfg_343_, 11);
v_preferReleaseBuild_357_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*28 + 2);
v_testDriver_358_ = lean_ctor_get(v_cfg_343_, 12);
v_testDriverArgs_359_ = lean_ctor_get(v_cfg_343_, 13);
v_lintDriver_360_ = lean_ctor_get(v_cfg_343_, 14);
v_lintDriverArgs_361_ = lean_ctor_get(v_cfg_343_, 15);
v_version_362_ = lean_ctor_get(v_cfg_343_, 16);
v_versionTags_363_ = lean_ctor_get(v_cfg_343_, 17);
v_description_364_ = lean_ctor_get(v_cfg_343_, 18);
v_keywords_365_ = lean_ctor_get(v_cfg_343_, 19);
v_homepage_366_ = lean_ctor_get(v_cfg_343_, 20);
v_license_367_ = lean_ctor_get(v_cfg_343_, 21);
v_licenseFiles_368_ = lean_ctor_get(v_cfg_343_, 22);
v_readmeFile_369_ = lean_ctor_get(v_cfg_343_, 23);
v_reservoir_370_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_371_ = lean_ctor_get(v_cfg_343_, 24);
v_restoreAllArtifacts_x3f_372_ = lean_ctor_get(v_cfg_343_, 25);
v_libPrefixOnWindows_373_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*28 + 4);
v_allowImportAll_374_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_375_ = lean_ctor_get(v_cfg_343_, 26);
v_checks_376_ = lean_ctor_get(v_cfg_343_, 27);
v_fixedToolchain_377_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*28 + 6);
v_isSharedCheck_384_ = !lean_is_exclusive(v_cfg_343_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v_cfg_343_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_checks_376_);
lean_inc(v_builtinLint_x3f_375_);
lean_inc(v_restoreAllArtifacts_x3f_372_);
lean_inc(v_enableArtifactCache_x3f_371_);
lean_inc(v_readmeFile_369_);
lean_inc(v_licenseFiles_368_);
lean_inc(v_license_367_);
lean_inc(v_homepage_366_);
lean_inc(v_keywords_365_);
lean_inc(v_description_364_);
lean_inc(v_versionTags_363_);
lean_inc(v_version_362_);
lean_inc(v_lintDriverArgs_361_);
lean_inc(v_lintDriver_360_);
lean_inc(v_testDriverArgs_359_);
lean_inc(v_testDriver_358_);
lean_inc(v_buildArchive_356_);
lean_inc(v_releaseRepo_355_);
lean_inc(v_irDir_354_);
lean_inc(v_binDir_353_);
lean_inc(v_nativeLibDir_352_);
lean_inc(v_leanLibDir_351_);
lean_inc(v_buildDir_350_);
lean_inc(v_srcDir_349_);
lean_inc(v_moreGlobalServerArgs_348_);
lean_inc(v_extraDepTargets_347_);
lean_inc(v_toLeanConfig_345_);
lean_inc(v_toWorkspaceConfig_344_);
lean_dec(v_cfg_343_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_toWorkspaceConfig_344_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_toLeanConfig_345_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_extraDepTargets_347_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v_moreGlobalServerArgs_348_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v_srcDir_349_);
lean_ctor_set(v_reuseFailAlloc_383_, 5, v_buildDir_350_);
lean_ctor_set(v_reuseFailAlloc_383_, 6, v_leanLibDir_351_);
lean_ctor_set(v_reuseFailAlloc_383_, 7, v_nativeLibDir_352_);
lean_ctor_set(v_reuseFailAlloc_383_, 8, v_binDir_353_);
lean_ctor_set(v_reuseFailAlloc_383_, 9, v_irDir_354_);
lean_ctor_set(v_reuseFailAlloc_383_, 10, v_releaseRepo_355_);
lean_ctor_set(v_reuseFailAlloc_383_, 11, v_buildArchive_356_);
lean_ctor_set(v_reuseFailAlloc_383_, 12, v_testDriver_358_);
lean_ctor_set(v_reuseFailAlloc_383_, 13, v_testDriverArgs_359_);
lean_ctor_set(v_reuseFailAlloc_383_, 14, v_lintDriver_360_);
lean_ctor_set(v_reuseFailAlloc_383_, 15, v_lintDriverArgs_361_);
lean_ctor_set(v_reuseFailAlloc_383_, 16, v_version_362_);
lean_ctor_set(v_reuseFailAlloc_383_, 17, v_versionTags_363_);
lean_ctor_set(v_reuseFailAlloc_383_, 18, v_description_364_);
lean_ctor_set(v_reuseFailAlloc_383_, 19, v_keywords_365_);
lean_ctor_set(v_reuseFailAlloc_383_, 20, v_homepage_366_);
lean_ctor_set(v_reuseFailAlloc_383_, 21, v_license_367_);
lean_ctor_set(v_reuseFailAlloc_383_, 22, v_licenseFiles_368_);
lean_ctor_set(v_reuseFailAlloc_383_, 23, v_readmeFile_369_);
lean_ctor_set(v_reuseFailAlloc_383_, 24, v_enableArtifactCache_x3f_371_);
lean_ctor_set(v_reuseFailAlloc_383_, 25, v_restoreAllArtifacts_x3f_372_);
lean_ctor_set(v_reuseFailAlloc_383_, 26, v_builtinLint_x3f_375_);
lean_ctor_set(v_reuseFailAlloc_383_, 27, v_checks_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_383_, sizeof(void*)*28, v_bootstrap_346_);
lean_ctor_set_uint8(v_reuseFailAlloc_383_, sizeof(void*)*28 + 2, v_preferReleaseBuild_357_);
lean_ctor_set_uint8(v_reuseFailAlloc_383_, sizeof(void*)*28 + 3, v_reservoir_370_);
lean_ctor_set_uint8(v_reuseFailAlloc_383_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_383_, sizeof(void*)*28 + 5, v_allowImportAll_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_383_, sizeof(void*)*28 + 6, v_fixedToolchain_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*28 + 1, v_val_342_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT void l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_342_ = stack[0].m_num;
lean_object* v_cfg_343_ = stack[1].m_obj;
lean_object* v_res_385_;
v_res_385_ = l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1(v_val_342_, v_cfg_343_);
stack->m_obj
 = v_res_385_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1___boxed(lean_object* v_val_386_, lean_object* v_cfg_387_){
_start:
{
uint8_t v_val_143__boxed_388_; lean_object* v_res_389_; 
v_val_143__boxed_388_ = lean_unbox(v_val_386_);
v_res_389_ = l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1(v_val_143__boxed_388_, v_cfg_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__2(lean_object* v_f_390_, lean_object* v_cfg_391_){
_start:
{
lean_object* v_toWorkspaceConfig_392_; lean_object* v_toLeanConfig_393_; uint8_t v_bootstrap_394_; lean_object* v_extraDepTargets_395_; uint8_t v_precompileModules_396_; lean_object* v_moreGlobalServerArgs_397_; lean_object* v_srcDir_398_; lean_object* v_buildDir_399_; lean_object* v_leanLibDir_400_; lean_object* v_nativeLibDir_401_; lean_object* v_binDir_402_; lean_object* v_irDir_403_; lean_object* v_releaseRepo_404_; lean_object* v_buildArchive_405_; uint8_t v_preferReleaseBuild_406_; lean_object* v_testDriver_407_; lean_object* v_testDriverArgs_408_; lean_object* v_lintDriver_409_; lean_object* v_lintDriverArgs_410_; lean_object* v_version_411_; lean_object* v_versionTags_412_; lean_object* v_description_413_; lean_object* v_keywords_414_; lean_object* v_homepage_415_; lean_object* v_license_416_; lean_object* v_licenseFiles_417_; lean_object* v_readmeFile_418_; uint8_t v_reservoir_419_; lean_object* v_enableArtifactCache_x3f_420_; lean_object* v_restoreAllArtifacts_x3f_421_; uint8_t v_libPrefixOnWindows_422_; uint8_t v_allowImportAll_423_; lean_object* v_builtinLint_x3f_424_; lean_object* v_checks_425_; uint8_t v_fixedToolchain_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_436_; 
v_toWorkspaceConfig_392_ = lean_ctor_get(v_cfg_391_, 0);
v_toLeanConfig_393_ = lean_ctor_get(v_cfg_391_, 1);
v_bootstrap_394_ = lean_ctor_get_uint8(v_cfg_391_, sizeof(void*)*28);
v_extraDepTargets_395_ = lean_ctor_get(v_cfg_391_, 2);
v_precompileModules_396_ = lean_ctor_get_uint8(v_cfg_391_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_397_ = lean_ctor_get(v_cfg_391_, 3);
v_srcDir_398_ = lean_ctor_get(v_cfg_391_, 4);
v_buildDir_399_ = lean_ctor_get(v_cfg_391_, 5);
v_leanLibDir_400_ = lean_ctor_get(v_cfg_391_, 6);
v_nativeLibDir_401_ = lean_ctor_get(v_cfg_391_, 7);
v_binDir_402_ = lean_ctor_get(v_cfg_391_, 8);
v_irDir_403_ = lean_ctor_get(v_cfg_391_, 9);
v_releaseRepo_404_ = lean_ctor_get(v_cfg_391_, 10);
v_buildArchive_405_ = lean_ctor_get(v_cfg_391_, 11);
v_preferReleaseBuild_406_ = lean_ctor_get_uint8(v_cfg_391_, sizeof(void*)*28 + 2);
v_testDriver_407_ = lean_ctor_get(v_cfg_391_, 12);
v_testDriverArgs_408_ = lean_ctor_get(v_cfg_391_, 13);
v_lintDriver_409_ = lean_ctor_get(v_cfg_391_, 14);
v_lintDriverArgs_410_ = lean_ctor_get(v_cfg_391_, 15);
v_version_411_ = lean_ctor_get(v_cfg_391_, 16);
v_versionTags_412_ = lean_ctor_get(v_cfg_391_, 17);
v_description_413_ = lean_ctor_get(v_cfg_391_, 18);
v_keywords_414_ = lean_ctor_get(v_cfg_391_, 19);
v_homepage_415_ = lean_ctor_get(v_cfg_391_, 20);
v_license_416_ = lean_ctor_get(v_cfg_391_, 21);
v_licenseFiles_417_ = lean_ctor_get(v_cfg_391_, 22);
v_readmeFile_418_ = lean_ctor_get(v_cfg_391_, 23);
v_reservoir_419_ = lean_ctor_get_uint8(v_cfg_391_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_420_ = lean_ctor_get(v_cfg_391_, 24);
v_restoreAllArtifacts_x3f_421_ = lean_ctor_get(v_cfg_391_, 25);
v_libPrefixOnWindows_422_ = lean_ctor_get_uint8(v_cfg_391_, sizeof(void*)*28 + 4);
v_allowImportAll_423_ = lean_ctor_get_uint8(v_cfg_391_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_424_ = lean_ctor_get(v_cfg_391_, 26);
v_checks_425_ = lean_ctor_get(v_cfg_391_, 27);
v_fixedToolchain_426_ = lean_ctor_get_uint8(v_cfg_391_, sizeof(void*)*28 + 6);
v_isSharedCheck_436_ = !lean_is_exclusive(v_cfg_391_);
if (v_isSharedCheck_436_ == 0)
{
v___x_428_ = v_cfg_391_;
v_isShared_429_ = v_isSharedCheck_436_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_checks_425_);
lean_inc(v_builtinLint_x3f_424_);
lean_inc(v_restoreAllArtifacts_x3f_421_);
lean_inc(v_enableArtifactCache_x3f_420_);
lean_inc(v_readmeFile_418_);
lean_inc(v_licenseFiles_417_);
lean_inc(v_license_416_);
lean_inc(v_homepage_415_);
lean_inc(v_keywords_414_);
lean_inc(v_description_413_);
lean_inc(v_versionTags_412_);
lean_inc(v_version_411_);
lean_inc(v_lintDriverArgs_410_);
lean_inc(v_lintDriver_409_);
lean_inc(v_testDriverArgs_408_);
lean_inc(v_testDriver_407_);
lean_inc(v_buildArchive_405_);
lean_inc(v_releaseRepo_404_);
lean_inc(v_irDir_403_);
lean_inc(v_binDir_402_);
lean_inc(v_nativeLibDir_401_);
lean_inc(v_leanLibDir_400_);
lean_inc(v_buildDir_399_);
lean_inc(v_srcDir_398_);
lean_inc(v_moreGlobalServerArgs_397_);
lean_inc(v_extraDepTargets_395_);
lean_inc(v_toLeanConfig_393_);
lean_inc(v_toWorkspaceConfig_392_);
lean_dec(v_cfg_391_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_436_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_430_ = lean_box(v_precompileModules_396_);
v___x_431_ = lean_apply_1(v_f_390_, v___x_430_);
if (v_isShared_429_ == 0)
{
v___x_433_ = v___x_428_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_toWorkspaceConfig_392_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_toLeanConfig_393_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_extraDepTargets_395_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_moreGlobalServerArgs_397_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_srcDir_398_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v_buildDir_399_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_leanLibDir_400_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_nativeLibDir_401_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_binDir_402_);
lean_ctor_set(v_reuseFailAlloc_435_, 9, v_irDir_403_);
lean_ctor_set(v_reuseFailAlloc_435_, 10, v_releaseRepo_404_);
lean_ctor_set(v_reuseFailAlloc_435_, 11, v_buildArchive_405_);
lean_ctor_set(v_reuseFailAlloc_435_, 12, v_testDriver_407_);
lean_ctor_set(v_reuseFailAlloc_435_, 13, v_testDriverArgs_408_);
lean_ctor_set(v_reuseFailAlloc_435_, 14, v_lintDriver_409_);
lean_ctor_set(v_reuseFailAlloc_435_, 15, v_lintDriverArgs_410_);
lean_ctor_set(v_reuseFailAlloc_435_, 16, v_version_411_);
lean_ctor_set(v_reuseFailAlloc_435_, 17, v_versionTags_412_);
lean_ctor_set(v_reuseFailAlloc_435_, 18, v_description_413_);
lean_ctor_set(v_reuseFailAlloc_435_, 19, v_keywords_414_);
lean_ctor_set(v_reuseFailAlloc_435_, 20, v_homepage_415_);
lean_ctor_set(v_reuseFailAlloc_435_, 21, v_license_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 22, v_licenseFiles_417_);
lean_ctor_set(v_reuseFailAlloc_435_, 23, v_readmeFile_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 24, v_enableArtifactCache_x3f_420_);
lean_ctor_set(v_reuseFailAlloc_435_, 25, v_restoreAllArtifacts_x3f_421_);
lean_ctor_set(v_reuseFailAlloc_435_, 26, v_builtinLint_x3f_424_);
lean_ctor_set(v_reuseFailAlloc_435_, 27, v_checks_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*28, v_bootstrap_394_);
v___x_433_ = v_reuseFailAlloc_435_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
uint8_t v___x_434_; 
v___x_434_ = lean_unbox(v___x_431_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*28 + 1, v___x_434_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*28 + 2, v_preferReleaseBuild_406_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*28 + 3, v_reservoir_419_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_422_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*28 + 5, v_allowImportAll_423_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*28 + 6, v_fixedToolchain_426_);
return v___x_433_;
}
}
}
}
lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg(){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = ((lean_object*)(l_Lake_PackageConfig_precompileModules___proj___redArg___closed__3));
return v___x_446_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_precompileModules___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_447_;
v_res_447_ = l_Lake_PackageConfig_precompileModules___proj___redArg();
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___boxed(lean_object* v___dummy_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lake_PackageConfig_precompileModules___proj___redArg();
return v_res_449_;
}
}
static lean_object* _init_l_Lake_PackageConfig_precompileModules___proj___closed__0(void){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lake_PackageConfig_precompileModules___proj___redArg();
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object* v_p_451_, lean_object* v_n_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = lean_obj_once(&l_Lake_PackageConfig_precompileModules___proj___closed__0, &l_Lake_PackageConfig_precompileModules___proj___closed__0_once, _init_l_Lake_PackageConfig_precompileModules___proj___closed__0);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object* v_p_454_, lean_object* v_n_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lake_PackageConfig_precompileModules___proj(v_p_454_, v_n_455_);
lean_dec(v_n_455_);
lean_dec(v_p_454_);
return v_res_456_;
}
}
lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___redArg(){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = lean_obj_once(&l_Lake_PackageConfig_precompileModules___proj___closed__0, &l_Lake_PackageConfig_precompileModules___proj___closed__0_once, _init_l_Lake_PackageConfig_precompileModules___proj___closed__0);
return v___x_458_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_precompileModules_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_459_;
v_res_459_ = l_Lake_PackageConfig_precompileModules_instConfigField___redArg();
stack->m_obj
 = v_res_459_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___redArg___boxed(lean_object* v___dummy_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lake_PackageConfig_precompileModules_instConfigField___redArg();
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object* v_p_462_, lean_object* v_n_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lean_obj_once(&l_Lake_PackageConfig_precompileModules___proj___closed__0, &l_Lake_PackageConfig_precompileModules___proj___closed__0_once, _init_l_Lake_PackageConfig_precompileModules___proj___closed__0);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object* v_p_465_, lean_object* v_n_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lake_PackageConfig_precompileModules_instConfigField(v_p_465_, v_n_466_);
lean_dec(v_n_466_);
lean_dec(v_p_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0(lean_object* v_cfg_468_){
_start:
{
lean_object* v_moreGlobalServerArgs_469_; 
v_moreGlobalServerArgs_469_ = lean_ctor_get(v_cfg_468_, 3);
lean_inc_ref(v_moreGlobalServerArgs_469_);
return v_moreGlobalServerArgs_469_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0___boxed(lean_object* v_cfg_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0(v_cfg_470_);
lean_dec_ref(v_cfg_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__1(lean_object* v_val_472_, lean_object* v_cfg_473_){
_start:
{
lean_object* v_toWorkspaceConfig_474_; lean_object* v_toLeanConfig_475_; uint8_t v_bootstrap_476_; lean_object* v_extraDepTargets_477_; uint8_t v_precompileModules_478_; lean_object* v_srcDir_479_; lean_object* v_buildDir_480_; lean_object* v_leanLibDir_481_; lean_object* v_nativeLibDir_482_; lean_object* v_binDir_483_; lean_object* v_irDir_484_; lean_object* v_releaseRepo_485_; lean_object* v_buildArchive_486_; uint8_t v_preferReleaseBuild_487_; lean_object* v_testDriver_488_; lean_object* v_testDriverArgs_489_; lean_object* v_lintDriver_490_; lean_object* v_lintDriverArgs_491_; lean_object* v_version_492_; lean_object* v_versionTags_493_; lean_object* v_description_494_; lean_object* v_keywords_495_; lean_object* v_homepage_496_; lean_object* v_license_497_; lean_object* v_licenseFiles_498_; lean_object* v_readmeFile_499_; uint8_t v_reservoir_500_; lean_object* v_enableArtifactCache_x3f_501_; lean_object* v_restoreAllArtifacts_x3f_502_; uint8_t v_libPrefixOnWindows_503_; uint8_t v_allowImportAll_504_; lean_object* v_builtinLint_x3f_505_; lean_object* v_checks_506_; uint8_t v_fixedToolchain_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_toWorkspaceConfig_474_ = lean_ctor_get(v_cfg_473_, 0);
v_toLeanConfig_475_ = lean_ctor_get(v_cfg_473_, 1);
v_bootstrap_476_ = lean_ctor_get_uint8(v_cfg_473_, sizeof(void*)*28);
v_extraDepTargets_477_ = lean_ctor_get(v_cfg_473_, 2);
v_precompileModules_478_ = lean_ctor_get_uint8(v_cfg_473_, sizeof(void*)*28 + 1);
v_srcDir_479_ = lean_ctor_get(v_cfg_473_, 4);
v_buildDir_480_ = lean_ctor_get(v_cfg_473_, 5);
v_leanLibDir_481_ = lean_ctor_get(v_cfg_473_, 6);
v_nativeLibDir_482_ = lean_ctor_get(v_cfg_473_, 7);
v_binDir_483_ = lean_ctor_get(v_cfg_473_, 8);
v_irDir_484_ = lean_ctor_get(v_cfg_473_, 9);
v_releaseRepo_485_ = lean_ctor_get(v_cfg_473_, 10);
v_buildArchive_486_ = lean_ctor_get(v_cfg_473_, 11);
v_preferReleaseBuild_487_ = lean_ctor_get_uint8(v_cfg_473_, sizeof(void*)*28 + 2);
v_testDriver_488_ = lean_ctor_get(v_cfg_473_, 12);
v_testDriverArgs_489_ = lean_ctor_get(v_cfg_473_, 13);
v_lintDriver_490_ = lean_ctor_get(v_cfg_473_, 14);
v_lintDriverArgs_491_ = lean_ctor_get(v_cfg_473_, 15);
v_version_492_ = lean_ctor_get(v_cfg_473_, 16);
v_versionTags_493_ = lean_ctor_get(v_cfg_473_, 17);
v_description_494_ = lean_ctor_get(v_cfg_473_, 18);
v_keywords_495_ = lean_ctor_get(v_cfg_473_, 19);
v_homepage_496_ = lean_ctor_get(v_cfg_473_, 20);
v_license_497_ = lean_ctor_get(v_cfg_473_, 21);
v_licenseFiles_498_ = lean_ctor_get(v_cfg_473_, 22);
v_readmeFile_499_ = lean_ctor_get(v_cfg_473_, 23);
v_reservoir_500_ = lean_ctor_get_uint8(v_cfg_473_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_501_ = lean_ctor_get(v_cfg_473_, 24);
v_restoreAllArtifacts_x3f_502_ = lean_ctor_get(v_cfg_473_, 25);
v_libPrefixOnWindows_503_ = lean_ctor_get_uint8(v_cfg_473_, sizeof(void*)*28 + 4);
v_allowImportAll_504_ = lean_ctor_get_uint8(v_cfg_473_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_505_ = lean_ctor_get(v_cfg_473_, 26);
v_checks_506_ = lean_ctor_get(v_cfg_473_, 27);
v_fixedToolchain_507_ = lean_ctor_get_uint8(v_cfg_473_, sizeof(void*)*28 + 6);
v_isSharedCheck_514_ = !lean_is_exclusive(v_cfg_473_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v_cfg_473_, 3);
lean_dec(v_unused_515_);
v___x_509_ = v_cfg_473_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_checks_506_);
lean_inc(v_builtinLint_x3f_505_);
lean_inc(v_restoreAllArtifacts_x3f_502_);
lean_inc(v_enableArtifactCache_x3f_501_);
lean_inc(v_readmeFile_499_);
lean_inc(v_licenseFiles_498_);
lean_inc(v_license_497_);
lean_inc(v_homepage_496_);
lean_inc(v_keywords_495_);
lean_inc(v_description_494_);
lean_inc(v_versionTags_493_);
lean_inc(v_version_492_);
lean_inc(v_lintDriverArgs_491_);
lean_inc(v_lintDriver_490_);
lean_inc(v_testDriverArgs_489_);
lean_inc(v_testDriver_488_);
lean_inc(v_buildArchive_486_);
lean_inc(v_releaseRepo_485_);
lean_inc(v_irDir_484_);
lean_inc(v_binDir_483_);
lean_inc(v_nativeLibDir_482_);
lean_inc(v_leanLibDir_481_);
lean_inc(v_buildDir_480_);
lean_inc(v_srcDir_479_);
lean_inc(v_extraDepTargets_477_);
lean_inc(v_toLeanConfig_475_);
lean_inc(v_toWorkspaceConfig_474_);
lean_dec(v_cfg_473_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 3, v_val_472_);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_toWorkspaceConfig_474_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_toLeanConfig_475_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_extraDepTargets_477_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v_val_472_);
lean_ctor_set(v_reuseFailAlloc_513_, 4, v_srcDir_479_);
lean_ctor_set(v_reuseFailAlloc_513_, 5, v_buildDir_480_);
lean_ctor_set(v_reuseFailAlloc_513_, 6, v_leanLibDir_481_);
lean_ctor_set(v_reuseFailAlloc_513_, 7, v_nativeLibDir_482_);
lean_ctor_set(v_reuseFailAlloc_513_, 8, v_binDir_483_);
lean_ctor_set(v_reuseFailAlloc_513_, 9, v_irDir_484_);
lean_ctor_set(v_reuseFailAlloc_513_, 10, v_releaseRepo_485_);
lean_ctor_set(v_reuseFailAlloc_513_, 11, v_buildArchive_486_);
lean_ctor_set(v_reuseFailAlloc_513_, 12, v_testDriver_488_);
lean_ctor_set(v_reuseFailAlloc_513_, 13, v_testDriverArgs_489_);
lean_ctor_set(v_reuseFailAlloc_513_, 14, v_lintDriver_490_);
lean_ctor_set(v_reuseFailAlloc_513_, 15, v_lintDriverArgs_491_);
lean_ctor_set(v_reuseFailAlloc_513_, 16, v_version_492_);
lean_ctor_set(v_reuseFailAlloc_513_, 17, v_versionTags_493_);
lean_ctor_set(v_reuseFailAlloc_513_, 18, v_description_494_);
lean_ctor_set(v_reuseFailAlloc_513_, 19, v_keywords_495_);
lean_ctor_set(v_reuseFailAlloc_513_, 20, v_homepage_496_);
lean_ctor_set(v_reuseFailAlloc_513_, 21, v_license_497_);
lean_ctor_set(v_reuseFailAlloc_513_, 22, v_licenseFiles_498_);
lean_ctor_set(v_reuseFailAlloc_513_, 23, v_readmeFile_499_);
lean_ctor_set(v_reuseFailAlloc_513_, 24, v_enableArtifactCache_x3f_501_);
lean_ctor_set(v_reuseFailAlloc_513_, 25, v_restoreAllArtifacts_x3f_502_);
lean_ctor_set(v_reuseFailAlloc_513_, 26, v_builtinLint_x3f_505_);
lean_ctor_set(v_reuseFailAlloc_513_, 27, v_checks_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_513_, sizeof(void*)*28, v_bootstrap_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_513_, sizeof(void*)*28 + 1, v_precompileModules_478_);
lean_ctor_set_uint8(v_reuseFailAlloc_513_, sizeof(void*)*28 + 2, v_preferReleaseBuild_487_);
lean_ctor_set_uint8(v_reuseFailAlloc_513_, sizeof(void*)*28 + 3, v_reservoir_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_513_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_513_, sizeof(void*)*28 + 5, v_allowImportAll_504_);
lean_ctor_set_uint8(v_reuseFailAlloc_513_, sizeof(void*)*28 + 6, v_fixedToolchain_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__2(lean_object* v_f_516_, lean_object* v_cfg_517_){
_start:
{
lean_object* v_toWorkspaceConfig_518_; lean_object* v_toLeanConfig_519_; uint8_t v_bootstrap_520_; lean_object* v_extraDepTargets_521_; uint8_t v_precompileModules_522_; lean_object* v_moreGlobalServerArgs_523_; lean_object* v_srcDir_524_; lean_object* v_buildDir_525_; lean_object* v_leanLibDir_526_; lean_object* v_nativeLibDir_527_; lean_object* v_binDir_528_; lean_object* v_irDir_529_; lean_object* v_releaseRepo_530_; lean_object* v_buildArchive_531_; uint8_t v_preferReleaseBuild_532_; lean_object* v_testDriver_533_; lean_object* v_testDriverArgs_534_; lean_object* v_lintDriver_535_; lean_object* v_lintDriverArgs_536_; lean_object* v_version_537_; lean_object* v_versionTags_538_; lean_object* v_description_539_; lean_object* v_keywords_540_; lean_object* v_homepage_541_; lean_object* v_license_542_; lean_object* v_licenseFiles_543_; lean_object* v_readmeFile_544_; uint8_t v_reservoir_545_; lean_object* v_enableArtifactCache_x3f_546_; lean_object* v_restoreAllArtifacts_x3f_547_; uint8_t v_libPrefixOnWindows_548_; uint8_t v_allowImportAll_549_; lean_object* v_builtinLint_x3f_550_; lean_object* v_checks_551_; uint8_t v_fixedToolchain_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_560_; 
v_toWorkspaceConfig_518_ = lean_ctor_get(v_cfg_517_, 0);
v_toLeanConfig_519_ = lean_ctor_get(v_cfg_517_, 1);
v_bootstrap_520_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*28);
v_extraDepTargets_521_ = lean_ctor_get(v_cfg_517_, 2);
v_precompileModules_522_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_523_ = lean_ctor_get(v_cfg_517_, 3);
v_srcDir_524_ = lean_ctor_get(v_cfg_517_, 4);
v_buildDir_525_ = lean_ctor_get(v_cfg_517_, 5);
v_leanLibDir_526_ = lean_ctor_get(v_cfg_517_, 6);
v_nativeLibDir_527_ = lean_ctor_get(v_cfg_517_, 7);
v_binDir_528_ = lean_ctor_get(v_cfg_517_, 8);
v_irDir_529_ = lean_ctor_get(v_cfg_517_, 9);
v_releaseRepo_530_ = lean_ctor_get(v_cfg_517_, 10);
v_buildArchive_531_ = lean_ctor_get(v_cfg_517_, 11);
v_preferReleaseBuild_532_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*28 + 2);
v_testDriver_533_ = lean_ctor_get(v_cfg_517_, 12);
v_testDriverArgs_534_ = lean_ctor_get(v_cfg_517_, 13);
v_lintDriver_535_ = lean_ctor_get(v_cfg_517_, 14);
v_lintDriverArgs_536_ = lean_ctor_get(v_cfg_517_, 15);
v_version_537_ = lean_ctor_get(v_cfg_517_, 16);
v_versionTags_538_ = lean_ctor_get(v_cfg_517_, 17);
v_description_539_ = lean_ctor_get(v_cfg_517_, 18);
v_keywords_540_ = lean_ctor_get(v_cfg_517_, 19);
v_homepage_541_ = lean_ctor_get(v_cfg_517_, 20);
v_license_542_ = lean_ctor_get(v_cfg_517_, 21);
v_licenseFiles_543_ = lean_ctor_get(v_cfg_517_, 22);
v_readmeFile_544_ = lean_ctor_get(v_cfg_517_, 23);
v_reservoir_545_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_546_ = lean_ctor_get(v_cfg_517_, 24);
v_restoreAllArtifacts_x3f_547_ = lean_ctor_get(v_cfg_517_, 25);
v_libPrefixOnWindows_548_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*28 + 4);
v_allowImportAll_549_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_550_ = lean_ctor_get(v_cfg_517_, 26);
v_checks_551_ = lean_ctor_get(v_cfg_517_, 27);
v_fixedToolchain_552_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*28 + 6);
v_isSharedCheck_560_ = !lean_is_exclusive(v_cfg_517_);
if (v_isSharedCheck_560_ == 0)
{
v___x_554_ = v_cfg_517_;
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_checks_551_);
lean_inc(v_builtinLint_x3f_550_);
lean_inc(v_restoreAllArtifacts_x3f_547_);
lean_inc(v_enableArtifactCache_x3f_546_);
lean_inc(v_readmeFile_544_);
lean_inc(v_licenseFiles_543_);
lean_inc(v_license_542_);
lean_inc(v_homepage_541_);
lean_inc(v_keywords_540_);
lean_inc(v_description_539_);
lean_inc(v_versionTags_538_);
lean_inc(v_version_537_);
lean_inc(v_lintDriverArgs_536_);
lean_inc(v_lintDriver_535_);
lean_inc(v_testDriverArgs_534_);
lean_inc(v_testDriver_533_);
lean_inc(v_buildArchive_531_);
lean_inc(v_releaseRepo_530_);
lean_inc(v_irDir_529_);
lean_inc(v_binDir_528_);
lean_inc(v_nativeLibDir_527_);
lean_inc(v_leanLibDir_526_);
lean_inc(v_buildDir_525_);
lean_inc(v_srcDir_524_);
lean_inc(v_moreGlobalServerArgs_523_);
lean_inc(v_extraDepTargets_521_);
lean_inc(v_toLeanConfig_519_);
lean_inc(v_toWorkspaceConfig_518_);
lean_dec(v_cfg_517_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = lean_apply_1(v_f_516_, v_moreGlobalServerArgs_523_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 3, v___x_556_);
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_toWorkspaceConfig_518_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_toLeanConfig_519_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_extraDepTargets_521_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_srcDir_524_);
lean_ctor_set(v_reuseFailAlloc_559_, 5, v_buildDir_525_);
lean_ctor_set(v_reuseFailAlloc_559_, 6, v_leanLibDir_526_);
lean_ctor_set(v_reuseFailAlloc_559_, 7, v_nativeLibDir_527_);
lean_ctor_set(v_reuseFailAlloc_559_, 8, v_binDir_528_);
lean_ctor_set(v_reuseFailAlloc_559_, 9, v_irDir_529_);
lean_ctor_set(v_reuseFailAlloc_559_, 10, v_releaseRepo_530_);
lean_ctor_set(v_reuseFailAlloc_559_, 11, v_buildArchive_531_);
lean_ctor_set(v_reuseFailAlloc_559_, 12, v_testDriver_533_);
lean_ctor_set(v_reuseFailAlloc_559_, 13, v_testDriverArgs_534_);
lean_ctor_set(v_reuseFailAlloc_559_, 14, v_lintDriver_535_);
lean_ctor_set(v_reuseFailAlloc_559_, 15, v_lintDriverArgs_536_);
lean_ctor_set(v_reuseFailAlloc_559_, 16, v_version_537_);
lean_ctor_set(v_reuseFailAlloc_559_, 17, v_versionTags_538_);
lean_ctor_set(v_reuseFailAlloc_559_, 18, v_description_539_);
lean_ctor_set(v_reuseFailAlloc_559_, 19, v_keywords_540_);
lean_ctor_set(v_reuseFailAlloc_559_, 20, v_homepage_541_);
lean_ctor_set(v_reuseFailAlloc_559_, 21, v_license_542_);
lean_ctor_set(v_reuseFailAlloc_559_, 22, v_licenseFiles_543_);
lean_ctor_set(v_reuseFailAlloc_559_, 23, v_readmeFile_544_);
lean_ctor_set(v_reuseFailAlloc_559_, 24, v_enableArtifactCache_x3f_546_);
lean_ctor_set(v_reuseFailAlloc_559_, 25, v_restoreAllArtifacts_x3f_547_);
lean_ctor_set(v_reuseFailAlloc_559_, 26, v_builtinLint_x3f_550_);
lean_ctor_set(v_reuseFailAlloc_559_, 27, v_checks_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_559_, sizeof(void*)*28, v_bootstrap_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_559_, sizeof(void*)*28 + 1, v_precompileModules_522_);
lean_ctor_set_uint8(v_reuseFailAlloc_559_, sizeof(void*)*28 + 2, v_preferReleaseBuild_532_);
lean_ctor_set_uint8(v_reuseFailAlloc_559_, sizeof(void*)*28 + 3, v_reservoir_545_);
lean_ctor_set_uint8(v_reuseFailAlloc_559_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_548_);
lean_ctor_set_uint8(v_reuseFailAlloc_559_, sizeof(void*)*28 + 5, v_allowImportAll_549_);
lean_ctor_set_uint8(v_reuseFailAlloc_559_, sizeof(void*)*28 + 6, v_fixedToolchain_552_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3(lean_object* v_x_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3___closed__0));
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3___boxed(lean_object* v_x_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3(v_x_565_);
lean_dec_ref(v_x_565_);
return v_res_566_;
}
}
lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg(){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__4));
return v___x_577_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_578_;
v_res_578_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg();
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___boxed(lean_object* v___dummy_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg();
return v_res_580_;
}
}
static lean_object* _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0(void){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg();
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object* v_p_582_, lean_object* v_n_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object* v_p_585_, lean_object* v_n_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_585_, v_n_586_);
lean_dec(v_n_586_);
lean_dec(v_p_585_);
return v_res_587_;
}
}
lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_589_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_590_;
v_res_590_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg();
stack->m_obj
 = v_res_590_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg___boxed(lean_object* v___dummy_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg();
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object* v_p_593_, lean_object* v_n_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object* v_p_596_, lean_object* v_n_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(v_p_596_, v_n_597_);
lean_dec(v_n_597_);
lean_dec(v_p_596_);
return v_res_598_;
}
}
lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_600_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_601_;
v_res_601_ = l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg();
stack->m_obj
 = v_res_601_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg___boxed(lean_object* v___dummy_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg();
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object* v_p_604_, lean_object* v_n_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object* v_p_607_, lean_object* v_n_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lake_PackageConfig_moreServerArgs_instConfigField(v_p_607_, v_n_608_);
lean_dec(v_n_608_);
lean_dec(v_p_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__0(lean_object* v_cfg_610_){
_start:
{
lean_object* v_srcDir_611_; 
v_srcDir_611_ = lean_ctor_get(v_cfg_610_, 4);
lean_inc_ref(v_srcDir_611_);
return v_srcDir_611_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lake_PackageConfig_srcDir___proj___redArg___lam__0(v_cfg_612_);
lean_dec_ref(v_cfg_612_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__1(lean_object* v_val_614_, lean_object* v_cfg_615_){
_start:
{
lean_object* v_toWorkspaceConfig_616_; lean_object* v_toLeanConfig_617_; uint8_t v_bootstrap_618_; lean_object* v_extraDepTargets_619_; uint8_t v_precompileModules_620_; lean_object* v_moreGlobalServerArgs_621_; lean_object* v_buildDir_622_; lean_object* v_leanLibDir_623_; lean_object* v_nativeLibDir_624_; lean_object* v_binDir_625_; lean_object* v_irDir_626_; lean_object* v_releaseRepo_627_; lean_object* v_buildArchive_628_; uint8_t v_preferReleaseBuild_629_; lean_object* v_testDriver_630_; lean_object* v_testDriverArgs_631_; lean_object* v_lintDriver_632_; lean_object* v_lintDriverArgs_633_; lean_object* v_version_634_; lean_object* v_versionTags_635_; lean_object* v_description_636_; lean_object* v_keywords_637_; lean_object* v_homepage_638_; lean_object* v_license_639_; lean_object* v_licenseFiles_640_; lean_object* v_readmeFile_641_; uint8_t v_reservoir_642_; lean_object* v_enableArtifactCache_x3f_643_; lean_object* v_restoreAllArtifacts_x3f_644_; uint8_t v_libPrefixOnWindows_645_; uint8_t v_allowImportAll_646_; lean_object* v_builtinLint_x3f_647_; lean_object* v_checks_648_; uint8_t v_fixedToolchain_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
v_toWorkspaceConfig_616_ = lean_ctor_get(v_cfg_615_, 0);
v_toLeanConfig_617_ = lean_ctor_get(v_cfg_615_, 1);
v_bootstrap_618_ = lean_ctor_get_uint8(v_cfg_615_, sizeof(void*)*28);
v_extraDepTargets_619_ = lean_ctor_get(v_cfg_615_, 2);
v_precompileModules_620_ = lean_ctor_get_uint8(v_cfg_615_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_621_ = lean_ctor_get(v_cfg_615_, 3);
v_buildDir_622_ = lean_ctor_get(v_cfg_615_, 5);
v_leanLibDir_623_ = lean_ctor_get(v_cfg_615_, 6);
v_nativeLibDir_624_ = lean_ctor_get(v_cfg_615_, 7);
v_binDir_625_ = lean_ctor_get(v_cfg_615_, 8);
v_irDir_626_ = lean_ctor_get(v_cfg_615_, 9);
v_releaseRepo_627_ = lean_ctor_get(v_cfg_615_, 10);
v_buildArchive_628_ = lean_ctor_get(v_cfg_615_, 11);
v_preferReleaseBuild_629_ = lean_ctor_get_uint8(v_cfg_615_, sizeof(void*)*28 + 2);
v_testDriver_630_ = lean_ctor_get(v_cfg_615_, 12);
v_testDriverArgs_631_ = lean_ctor_get(v_cfg_615_, 13);
v_lintDriver_632_ = lean_ctor_get(v_cfg_615_, 14);
v_lintDriverArgs_633_ = lean_ctor_get(v_cfg_615_, 15);
v_version_634_ = lean_ctor_get(v_cfg_615_, 16);
v_versionTags_635_ = lean_ctor_get(v_cfg_615_, 17);
v_description_636_ = lean_ctor_get(v_cfg_615_, 18);
v_keywords_637_ = lean_ctor_get(v_cfg_615_, 19);
v_homepage_638_ = lean_ctor_get(v_cfg_615_, 20);
v_license_639_ = lean_ctor_get(v_cfg_615_, 21);
v_licenseFiles_640_ = lean_ctor_get(v_cfg_615_, 22);
v_readmeFile_641_ = lean_ctor_get(v_cfg_615_, 23);
v_reservoir_642_ = lean_ctor_get_uint8(v_cfg_615_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_643_ = lean_ctor_get(v_cfg_615_, 24);
v_restoreAllArtifacts_x3f_644_ = lean_ctor_get(v_cfg_615_, 25);
v_libPrefixOnWindows_645_ = lean_ctor_get_uint8(v_cfg_615_, sizeof(void*)*28 + 4);
v_allowImportAll_646_ = lean_ctor_get_uint8(v_cfg_615_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_647_ = lean_ctor_get(v_cfg_615_, 26);
v_checks_648_ = lean_ctor_get(v_cfg_615_, 27);
v_fixedToolchain_649_ = lean_ctor_get_uint8(v_cfg_615_, sizeof(void*)*28 + 6);
v_isSharedCheck_656_ = !lean_is_exclusive(v_cfg_615_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v_cfg_615_, 4);
lean_dec(v_unused_657_);
v___x_651_ = v_cfg_615_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_checks_648_);
lean_inc(v_builtinLint_x3f_647_);
lean_inc(v_restoreAllArtifacts_x3f_644_);
lean_inc(v_enableArtifactCache_x3f_643_);
lean_inc(v_readmeFile_641_);
lean_inc(v_licenseFiles_640_);
lean_inc(v_license_639_);
lean_inc(v_homepage_638_);
lean_inc(v_keywords_637_);
lean_inc(v_description_636_);
lean_inc(v_versionTags_635_);
lean_inc(v_version_634_);
lean_inc(v_lintDriverArgs_633_);
lean_inc(v_lintDriver_632_);
lean_inc(v_testDriverArgs_631_);
lean_inc(v_testDriver_630_);
lean_inc(v_buildArchive_628_);
lean_inc(v_releaseRepo_627_);
lean_inc(v_irDir_626_);
lean_inc(v_binDir_625_);
lean_inc(v_nativeLibDir_624_);
lean_inc(v_leanLibDir_623_);
lean_inc(v_buildDir_622_);
lean_inc(v_moreGlobalServerArgs_621_);
lean_inc(v_extraDepTargets_619_);
lean_inc(v_toLeanConfig_617_);
lean_inc(v_toWorkspaceConfig_616_);
lean_dec(v_cfg_615_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v_val_614_);
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_toWorkspaceConfig_616_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_toLeanConfig_617_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_extraDepTargets_619_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_moreGlobalServerArgs_621_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v_val_614_);
lean_ctor_set(v_reuseFailAlloc_655_, 5, v_buildDir_622_);
lean_ctor_set(v_reuseFailAlloc_655_, 6, v_leanLibDir_623_);
lean_ctor_set(v_reuseFailAlloc_655_, 7, v_nativeLibDir_624_);
lean_ctor_set(v_reuseFailAlloc_655_, 8, v_binDir_625_);
lean_ctor_set(v_reuseFailAlloc_655_, 9, v_irDir_626_);
lean_ctor_set(v_reuseFailAlloc_655_, 10, v_releaseRepo_627_);
lean_ctor_set(v_reuseFailAlloc_655_, 11, v_buildArchive_628_);
lean_ctor_set(v_reuseFailAlloc_655_, 12, v_testDriver_630_);
lean_ctor_set(v_reuseFailAlloc_655_, 13, v_testDriverArgs_631_);
lean_ctor_set(v_reuseFailAlloc_655_, 14, v_lintDriver_632_);
lean_ctor_set(v_reuseFailAlloc_655_, 15, v_lintDriverArgs_633_);
lean_ctor_set(v_reuseFailAlloc_655_, 16, v_version_634_);
lean_ctor_set(v_reuseFailAlloc_655_, 17, v_versionTags_635_);
lean_ctor_set(v_reuseFailAlloc_655_, 18, v_description_636_);
lean_ctor_set(v_reuseFailAlloc_655_, 19, v_keywords_637_);
lean_ctor_set(v_reuseFailAlloc_655_, 20, v_homepage_638_);
lean_ctor_set(v_reuseFailAlloc_655_, 21, v_license_639_);
lean_ctor_set(v_reuseFailAlloc_655_, 22, v_licenseFiles_640_);
lean_ctor_set(v_reuseFailAlloc_655_, 23, v_readmeFile_641_);
lean_ctor_set(v_reuseFailAlloc_655_, 24, v_enableArtifactCache_x3f_643_);
lean_ctor_set(v_reuseFailAlloc_655_, 25, v_restoreAllArtifacts_x3f_644_);
lean_ctor_set(v_reuseFailAlloc_655_, 26, v_builtinLint_x3f_647_);
lean_ctor_set(v_reuseFailAlloc_655_, 27, v_checks_648_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*28, v_bootstrap_618_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*28 + 1, v_precompileModules_620_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*28 + 2, v_preferReleaseBuild_629_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*28 + 3, v_reservoir_642_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_645_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*28 + 5, v_allowImportAll_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*28 + 6, v_fixedToolchain_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__2(lean_object* v_f_658_, lean_object* v_cfg_659_){
_start:
{
lean_object* v_toWorkspaceConfig_660_; lean_object* v_toLeanConfig_661_; uint8_t v_bootstrap_662_; lean_object* v_extraDepTargets_663_; uint8_t v_precompileModules_664_; lean_object* v_moreGlobalServerArgs_665_; lean_object* v_srcDir_666_; lean_object* v_buildDir_667_; lean_object* v_leanLibDir_668_; lean_object* v_nativeLibDir_669_; lean_object* v_binDir_670_; lean_object* v_irDir_671_; lean_object* v_releaseRepo_672_; lean_object* v_buildArchive_673_; uint8_t v_preferReleaseBuild_674_; lean_object* v_testDriver_675_; lean_object* v_testDriverArgs_676_; lean_object* v_lintDriver_677_; lean_object* v_lintDriverArgs_678_; lean_object* v_version_679_; lean_object* v_versionTags_680_; lean_object* v_description_681_; lean_object* v_keywords_682_; lean_object* v_homepage_683_; lean_object* v_license_684_; lean_object* v_licenseFiles_685_; lean_object* v_readmeFile_686_; uint8_t v_reservoir_687_; lean_object* v_enableArtifactCache_x3f_688_; lean_object* v_restoreAllArtifacts_x3f_689_; uint8_t v_libPrefixOnWindows_690_; uint8_t v_allowImportAll_691_; lean_object* v_builtinLint_x3f_692_; lean_object* v_checks_693_; uint8_t v_fixedToolchain_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_702_; 
v_toWorkspaceConfig_660_ = lean_ctor_get(v_cfg_659_, 0);
v_toLeanConfig_661_ = lean_ctor_get(v_cfg_659_, 1);
v_bootstrap_662_ = lean_ctor_get_uint8(v_cfg_659_, sizeof(void*)*28);
v_extraDepTargets_663_ = lean_ctor_get(v_cfg_659_, 2);
v_precompileModules_664_ = lean_ctor_get_uint8(v_cfg_659_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_665_ = lean_ctor_get(v_cfg_659_, 3);
v_srcDir_666_ = lean_ctor_get(v_cfg_659_, 4);
v_buildDir_667_ = lean_ctor_get(v_cfg_659_, 5);
v_leanLibDir_668_ = lean_ctor_get(v_cfg_659_, 6);
v_nativeLibDir_669_ = lean_ctor_get(v_cfg_659_, 7);
v_binDir_670_ = lean_ctor_get(v_cfg_659_, 8);
v_irDir_671_ = lean_ctor_get(v_cfg_659_, 9);
v_releaseRepo_672_ = lean_ctor_get(v_cfg_659_, 10);
v_buildArchive_673_ = lean_ctor_get(v_cfg_659_, 11);
v_preferReleaseBuild_674_ = lean_ctor_get_uint8(v_cfg_659_, sizeof(void*)*28 + 2);
v_testDriver_675_ = lean_ctor_get(v_cfg_659_, 12);
v_testDriverArgs_676_ = lean_ctor_get(v_cfg_659_, 13);
v_lintDriver_677_ = lean_ctor_get(v_cfg_659_, 14);
v_lintDriverArgs_678_ = lean_ctor_get(v_cfg_659_, 15);
v_version_679_ = lean_ctor_get(v_cfg_659_, 16);
v_versionTags_680_ = lean_ctor_get(v_cfg_659_, 17);
v_description_681_ = lean_ctor_get(v_cfg_659_, 18);
v_keywords_682_ = lean_ctor_get(v_cfg_659_, 19);
v_homepage_683_ = lean_ctor_get(v_cfg_659_, 20);
v_license_684_ = lean_ctor_get(v_cfg_659_, 21);
v_licenseFiles_685_ = lean_ctor_get(v_cfg_659_, 22);
v_readmeFile_686_ = lean_ctor_get(v_cfg_659_, 23);
v_reservoir_687_ = lean_ctor_get_uint8(v_cfg_659_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_688_ = lean_ctor_get(v_cfg_659_, 24);
v_restoreAllArtifacts_x3f_689_ = lean_ctor_get(v_cfg_659_, 25);
v_libPrefixOnWindows_690_ = lean_ctor_get_uint8(v_cfg_659_, sizeof(void*)*28 + 4);
v_allowImportAll_691_ = lean_ctor_get_uint8(v_cfg_659_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_692_ = lean_ctor_get(v_cfg_659_, 26);
v_checks_693_ = lean_ctor_get(v_cfg_659_, 27);
v_fixedToolchain_694_ = lean_ctor_get_uint8(v_cfg_659_, sizeof(void*)*28 + 6);
v_isSharedCheck_702_ = !lean_is_exclusive(v_cfg_659_);
if (v_isSharedCheck_702_ == 0)
{
v___x_696_ = v_cfg_659_;
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_checks_693_);
lean_inc(v_builtinLint_x3f_692_);
lean_inc(v_restoreAllArtifacts_x3f_689_);
lean_inc(v_enableArtifactCache_x3f_688_);
lean_inc(v_readmeFile_686_);
lean_inc(v_licenseFiles_685_);
lean_inc(v_license_684_);
lean_inc(v_homepage_683_);
lean_inc(v_keywords_682_);
lean_inc(v_description_681_);
lean_inc(v_versionTags_680_);
lean_inc(v_version_679_);
lean_inc(v_lintDriverArgs_678_);
lean_inc(v_lintDriver_677_);
lean_inc(v_testDriverArgs_676_);
lean_inc(v_testDriver_675_);
lean_inc(v_buildArchive_673_);
lean_inc(v_releaseRepo_672_);
lean_inc(v_irDir_671_);
lean_inc(v_binDir_670_);
lean_inc(v_nativeLibDir_669_);
lean_inc(v_leanLibDir_668_);
lean_inc(v_buildDir_667_);
lean_inc(v_srcDir_666_);
lean_inc(v_moreGlobalServerArgs_665_);
lean_inc(v_extraDepTargets_663_);
lean_inc(v_toLeanConfig_661_);
lean_inc(v_toWorkspaceConfig_660_);
lean_dec(v_cfg_659_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_apply_1(v_f_658_, v_srcDir_666_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 4, v___x_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_toWorkspaceConfig_660_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_toLeanConfig_661_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_extraDepTargets_663_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_moreGlobalServerArgs_665_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_701_, 5, v_buildDir_667_);
lean_ctor_set(v_reuseFailAlloc_701_, 6, v_leanLibDir_668_);
lean_ctor_set(v_reuseFailAlloc_701_, 7, v_nativeLibDir_669_);
lean_ctor_set(v_reuseFailAlloc_701_, 8, v_binDir_670_);
lean_ctor_set(v_reuseFailAlloc_701_, 9, v_irDir_671_);
lean_ctor_set(v_reuseFailAlloc_701_, 10, v_releaseRepo_672_);
lean_ctor_set(v_reuseFailAlloc_701_, 11, v_buildArchive_673_);
lean_ctor_set(v_reuseFailAlloc_701_, 12, v_testDriver_675_);
lean_ctor_set(v_reuseFailAlloc_701_, 13, v_testDriverArgs_676_);
lean_ctor_set(v_reuseFailAlloc_701_, 14, v_lintDriver_677_);
lean_ctor_set(v_reuseFailAlloc_701_, 15, v_lintDriverArgs_678_);
lean_ctor_set(v_reuseFailAlloc_701_, 16, v_version_679_);
lean_ctor_set(v_reuseFailAlloc_701_, 17, v_versionTags_680_);
lean_ctor_set(v_reuseFailAlloc_701_, 18, v_description_681_);
lean_ctor_set(v_reuseFailAlloc_701_, 19, v_keywords_682_);
lean_ctor_set(v_reuseFailAlloc_701_, 20, v_homepage_683_);
lean_ctor_set(v_reuseFailAlloc_701_, 21, v_license_684_);
lean_ctor_set(v_reuseFailAlloc_701_, 22, v_licenseFiles_685_);
lean_ctor_set(v_reuseFailAlloc_701_, 23, v_readmeFile_686_);
lean_ctor_set(v_reuseFailAlloc_701_, 24, v_enableArtifactCache_x3f_688_);
lean_ctor_set(v_reuseFailAlloc_701_, 25, v_restoreAllArtifacts_x3f_689_);
lean_ctor_set(v_reuseFailAlloc_701_, 26, v_builtinLint_x3f_692_);
lean_ctor_set(v_reuseFailAlloc_701_, 27, v_checks_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*28, v_bootstrap_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*28 + 1, v_precompileModules_664_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*28 + 2, v_preferReleaseBuild_674_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*28 + 3, v_reservoir_687_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_690_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*28 + 5, v_allowImportAll_691_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*28 + 6, v_fixedToolchain_694_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__3(lean_object* v_x_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__1));
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__3___boxed(lean_object* v_x_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lake_PackageConfig_srcDir___proj___redArg___lam__3(v_x_705_);
lean_dec_ref(v_x_705_);
return v_res_706_;
}
}
lean_object* l_Lake_PackageConfig_srcDir___proj___redArg(){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___redArg___closed__4));
return v___x_717_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_srcDir___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_718_;
v_res_718_ = l_Lake_PackageConfig_srcDir___proj___redArg();
stack->m_obj
 = v_res_718_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___boxed(lean_object* v___dummy_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lake_PackageConfig_srcDir___proj___redArg();
return v_res_720_;
}
}
static lean_object* _init_l_Lake_PackageConfig_srcDir___proj___closed__0(void){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lake_PackageConfig_srcDir___proj___redArg();
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object* v_p_722_, lean_object* v_n_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_obj_once(&l_Lake_PackageConfig_srcDir___proj___closed__0, &l_Lake_PackageConfig_srcDir___proj___closed__0_once, _init_l_Lake_PackageConfig_srcDir___proj___closed__0);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object* v_p_725_, lean_object* v_n_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lake_PackageConfig_srcDir___proj(v_p_725_, v_n_726_);
lean_dec(v_n_726_);
lean_dec(v_p_725_);
return v_res_727_;
}
}
lean_object* l_Lake_PackageConfig_srcDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_obj_once(&l_Lake_PackageConfig_srcDir___proj___closed__0, &l_Lake_PackageConfig_srcDir___proj___closed__0_once, _init_l_Lake_PackageConfig_srcDir___proj___closed__0);
return v___x_729_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_srcDir_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_730_;
v_res_730_ = l_Lake_PackageConfig_srcDir_instConfigField___redArg();
stack->m_obj
 = v_res_730_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___redArg___boxed(lean_object* v___dummy_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lake_PackageConfig_srcDir_instConfigField___redArg();
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object* v_p_733_, lean_object* v_n_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_obj_once(&l_Lake_PackageConfig_srcDir___proj___closed__0, &l_Lake_PackageConfig_srcDir___proj___closed__0_once, _init_l_Lake_PackageConfig_srcDir___proj___closed__0);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object* v_p_736_, lean_object* v_n_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lake_PackageConfig_srcDir_instConfigField(v_p_736_, v_n_737_);
lean_dec(v_n_737_);
lean_dec(v_p_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__0(lean_object* v_cfg_739_){
_start:
{
lean_object* v_buildDir_740_; 
v_buildDir_740_ = lean_ctor_get(v_cfg_739_, 5);
lean_inc_ref(v_buildDir_740_);
return v_buildDir_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lake_PackageConfig_buildDir___proj___redArg___lam__0(v_cfg_741_);
lean_dec_ref(v_cfg_741_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__1(lean_object* v_val_743_, lean_object* v_cfg_744_){
_start:
{
lean_object* v_toWorkspaceConfig_745_; lean_object* v_toLeanConfig_746_; uint8_t v_bootstrap_747_; lean_object* v_extraDepTargets_748_; uint8_t v_precompileModules_749_; lean_object* v_moreGlobalServerArgs_750_; lean_object* v_srcDir_751_; lean_object* v_leanLibDir_752_; lean_object* v_nativeLibDir_753_; lean_object* v_binDir_754_; lean_object* v_irDir_755_; lean_object* v_releaseRepo_756_; lean_object* v_buildArchive_757_; uint8_t v_preferReleaseBuild_758_; lean_object* v_testDriver_759_; lean_object* v_testDriverArgs_760_; lean_object* v_lintDriver_761_; lean_object* v_lintDriverArgs_762_; lean_object* v_version_763_; lean_object* v_versionTags_764_; lean_object* v_description_765_; lean_object* v_keywords_766_; lean_object* v_homepage_767_; lean_object* v_license_768_; lean_object* v_licenseFiles_769_; lean_object* v_readmeFile_770_; uint8_t v_reservoir_771_; lean_object* v_enableArtifactCache_x3f_772_; lean_object* v_restoreAllArtifacts_x3f_773_; uint8_t v_libPrefixOnWindows_774_; uint8_t v_allowImportAll_775_; lean_object* v_builtinLint_x3f_776_; lean_object* v_checks_777_; uint8_t v_fixedToolchain_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_toWorkspaceConfig_745_ = lean_ctor_get(v_cfg_744_, 0);
v_toLeanConfig_746_ = lean_ctor_get(v_cfg_744_, 1);
v_bootstrap_747_ = lean_ctor_get_uint8(v_cfg_744_, sizeof(void*)*28);
v_extraDepTargets_748_ = lean_ctor_get(v_cfg_744_, 2);
v_precompileModules_749_ = lean_ctor_get_uint8(v_cfg_744_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_750_ = lean_ctor_get(v_cfg_744_, 3);
v_srcDir_751_ = lean_ctor_get(v_cfg_744_, 4);
v_leanLibDir_752_ = lean_ctor_get(v_cfg_744_, 6);
v_nativeLibDir_753_ = lean_ctor_get(v_cfg_744_, 7);
v_binDir_754_ = lean_ctor_get(v_cfg_744_, 8);
v_irDir_755_ = lean_ctor_get(v_cfg_744_, 9);
v_releaseRepo_756_ = lean_ctor_get(v_cfg_744_, 10);
v_buildArchive_757_ = lean_ctor_get(v_cfg_744_, 11);
v_preferReleaseBuild_758_ = lean_ctor_get_uint8(v_cfg_744_, sizeof(void*)*28 + 2);
v_testDriver_759_ = lean_ctor_get(v_cfg_744_, 12);
v_testDriverArgs_760_ = lean_ctor_get(v_cfg_744_, 13);
v_lintDriver_761_ = lean_ctor_get(v_cfg_744_, 14);
v_lintDriverArgs_762_ = lean_ctor_get(v_cfg_744_, 15);
v_version_763_ = lean_ctor_get(v_cfg_744_, 16);
v_versionTags_764_ = lean_ctor_get(v_cfg_744_, 17);
v_description_765_ = lean_ctor_get(v_cfg_744_, 18);
v_keywords_766_ = lean_ctor_get(v_cfg_744_, 19);
v_homepage_767_ = lean_ctor_get(v_cfg_744_, 20);
v_license_768_ = lean_ctor_get(v_cfg_744_, 21);
v_licenseFiles_769_ = lean_ctor_get(v_cfg_744_, 22);
v_readmeFile_770_ = lean_ctor_get(v_cfg_744_, 23);
v_reservoir_771_ = lean_ctor_get_uint8(v_cfg_744_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_772_ = lean_ctor_get(v_cfg_744_, 24);
v_restoreAllArtifacts_x3f_773_ = lean_ctor_get(v_cfg_744_, 25);
v_libPrefixOnWindows_774_ = lean_ctor_get_uint8(v_cfg_744_, sizeof(void*)*28 + 4);
v_allowImportAll_775_ = lean_ctor_get_uint8(v_cfg_744_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_776_ = lean_ctor_get(v_cfg_744_, 26);
v_checks_777_ = lean_ctor_get(v_cfg_744_, 27);
v_fixedToolchain_778_ = lean_ctor_get_uint8(v_cfg_744_, sizeof(void*)*28 + 6);
v_isSharedCheck_785_ = !lean_is_exclusive(v_cfg_744_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_cfg_744_, 5);
lean_dec(v_unused_786_);
v___x_780_ = v_cfg_744_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_checks_777_);
lean_inc(v_builtinLint_x3f_776_);
lean_inc(v_restoreAllArtifacts_x3f_773_);
lean_inc(v_enableArtifactCache_x3f_772_);
lean_inc(v_readmeFile_770_);
lean_inc(v_licenseFiles_769_);
lean_inc(v_license_768_);
lean_inc(v_homepage_767_);
lean_inc(v_keywords_766_);
lean_inc(v_description_765_);
lean_inc(v_versionTags_764_);
lean_inc(v_version_763_);
lean_inc(v_lintDriverArgs_762_);
lean_inc(v_lintDriver_761_);
lean_inc(v_testDriverArgs_760_);
lean_inc(v_testDriver_759_);
lean_inc(v_buildArchive_757_);
lean_inc(v_releaseRepo_756_);
lean_inc(v_irDir_755_);
lean_inc(v_binDir_754_);
lean_inc(v_nativeLibDir_753_);
lean_inc(v_leanLibDir_752_);
lean_inc(v_srcDir_751_);
lean_inc(v_moreGlobalServerArgs_750_);
lean_inc(v_extraDepTargets_748_);
lean_inc(v_toLeanConfig_746_);
lean_inc(v_toWorkspaceConfig_745_);
lean_dec(v_cfg_744_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 5, v_val_743_);
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_toWorkspaceConfig_745_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_toLeanConfig_746_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_extraDepTargets_748_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_moreGlobalServerArgs_750_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_srcDir_751_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v_val_743_);
lean_ctor_set(v_reuseFailAlloc_784_, 6, v_leanLibDir_752_);
lean_ctor_set(v_reuseFailAlloc_784_, 7, v_nativeLibDir_753_);
lean_ctor_set(v_reuseFailAlloc_784_, 8, v_binDir_754_);
lean_ctor_set(v_reuseFailAlloc_784_, 9, v_irDir_755_);
lean_ctor_set(v_reuseFailAlloc_784_, 10, v_releaseRepo_756_);
lean_ctor_set(v_reuseFailAlloc_784_, 11, v_buildArchive_757_);
lean_ctor_set(v_reuseFailAlloc_784_, 12, v_testDriver_759_);
lean_ctor_set(v_reuseFailAlloc_784_, 13, v_testDriverArgs_760_);
lean_ctor_set(v_reuseFailAlloc_784_, 14, v_lintDriver_761_);
lean_ctor_set(v_reuseFailAlloc_784_, 15, v_lintDriverArgs_762_);
lean_ctor_set(v_reuseFailAlloc_784_, 16, v_version_763_);
lean_ctor_set(v_reuseFailAlloc_784_, 17, v_versionTags_764_);
lean_ctor_set(v_reuseFailAlloc_784_, 18, v_description_765_);
lean_ctor_set(v_reuseFailAlloc_784_, 19, v_keywords_766_);
lean_ctor_set(v_reuseFailAlloc_784_, 20, v_homepage_767_);
lean_ctor_set(v_reuseFailAlloc_784_, 21, v_license_768_);
lean_ctor_set(v_reuseFailAlloc_784_, 22, v_licenseFiles_769_);
lean_ctor_set(v_reuseFailAlloc_784_, 23, v_readmeFile_770_);
lean_ctor_set(v_reuseFailAlloc_784_, 24, v_enableArtifactCache_x3f_772_);
lean_ctor_set(v_reuseFailAlloc_784_, 25, v_restoreAllArtifacts_x3f_773_);
lean_ctor_set(v_reuseFailAlloc_784_, 26, v_builtinLint_x3f_776_);
lean_ctor_set(v_reuseFailAlloc_784_, 27, v_checks_777_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*28, v_bootstrap_747_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*28 + 1, v_precompileModules_749_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*28 + 2, v_preferReleaseBuild_758_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*28 + 3, v_reservoir_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*28 + 5, v_allowImportAll_775_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*28 + 6, v_fixedToolchain_778_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__2(lean_object* v_f_787_, lean_object* v_cfg_788_){
_start:
{
lean_object* v_toWorkspaceConfig_789_; lean_object* v_toLeanConfig_790_; uint8_t v_bootstrap_791_; lean_object* v_extraDepTargets_792_; uint8_t v_precompileModules_793_; lean_object* v_moreGlobalServerArgs_794_; lean_object* v_srcDir_795_; lean_object* v_buildDir_796_; lean_object* v_leanLibDir_797_; lean_object* v_nativeLibDir_798_; lean_object* v_binDir_799_; lean_object* v_irDir_800_; lean_object* v_releaseRepo_801_; lean_object* v_buildArchive_802_; uint8_t v_preferReleaseBuild_803_; lean_object* v_testDriver_804_; lean_object* v_testDriverArgs_805_; lean_object* v_lintDriver_806_; lean_object* v_lintDriverArgs_807_; lean_object* v_version_808_; lean_object* v_versionTags_809_; lean_object* v_description_810_; lean_object* v_keywords_811_; lean_object* v_homepage_812_; lean_object* v_license_813_; lean_object* v_licenseFiles_814_; lean_object* v_readmeFile_815_; uint8_t v_reservoir_816_; lean_object* v_enableArtifactCache_x3f_817_; lean_object* v_restoreAllArtifacts_x3f_818_; uint8_t v_libPrefixOnWindows_819_; uint8_t v_allowImportAll_820_; lean_object* v_builtinLint_x3f_821_; lean_object* v_checks_822_; uint8_t v_fixedToolchain_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_831_; 
v_toWorkspaceConfig_789_ = lean_ctor_get(v_cfg_788_, 0);
v_toLeanConfig_790_ = lean_ctor_get(v_cfg_788_, 1);
v_bootstrap_791_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*28);
v_extraDepTargets_792_ = lean_ctor_get(v_cfg_788_, 2);
v_precompileModules_793_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_794_ = lean_ctor_get(v_cfg_788_, 3);
v_srcDir_795_ = lean_ctor_get(v_cfg_788_, 4);
v_buildDir_796_ = lean_ctor_get(v_cfg_788_, 5);
v_leanLibDir_797_ = lean_ctor_get(v_cfg_788_, 6);
v_nativeLibDir_798_ = lean_ctor_get(v_cfg_788_, 7);
v_binDir_799_ = lean_ctor_get(v_cfg_788_, 8);
v_irDir_800_ = lean_ctor_get(v_cfg_788_, 9);
v_releaseRepo_801_ = lean_ctor_get(v_cfg_788_, 10);
v_buildArchive_802_ = lean_ctor_get(v_cfg_788_, 11);
v_preferReleaseBuild_803_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*28 + 2);
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
v_reservoir_816_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_817_ = lean_ctor_get(v_cfg_788_, 24);
v_restoreAllArtifacts_x3f_818_ = lean_ctor_get(v_cfg_788_, 25);
v_libPrefixOnWindows_819_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*28 + 4);
v_allowImportAll_820_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_821_ = lean_ctor_get(v_cfg_788_, 26);
v_checks_822_ = lean_ctor_get(v_cfg_788_, 27);
v_fixedToolchain_823_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*28 + 6);
v_isSharedCheck_831_ = !lean_is_exclusive(v_cfg_788_);
if (v_isSharedCheck_831_ == 0)
{
v___x_825_ = v_cfg_788_;
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_checks_822_);
lean_inc(v_builtinLint_x3f_821_);
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
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_apply_1(v_f_787_, v_buildDir_796_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 5, v___x_827_);
v___x_829_ = v___x_825_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_toWorkspaceConfig_789_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_toLeanConfig_790_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_extraDepTargets_792_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v_moreGlobalServerArgs_794_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v_srcDir_795_);
lean_ctor_set(v_reuseFailAlloc_830_, 5, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_830_, 6, v_leanLibDir_797_);
lean_ctor_set(v_reuseFailAlloc_830_, 7, v_nativeLibDir_798_);
lean_ctor_set(v_reuseFailAlloc_830_, 8, v_binDir_799_);
lean_ctor_set(v_reuseFailAlloc_830_, 9, v_irDir_800_);
lean_ctor_set(v_reuseFailAlloc_830_, 10, v_releaseRepo_801_);
lean_ctor_set(v_reuseFailAlloc_830_, 11, v_buildArchive_802_);
lean_ctor_set(v_reuseFailAlloc_830_, 12, v_testDriver_804_);
lean_ctor_set(v_reuseFailAlloc_830_, 13, v_testDriverArgs_805_);
lean_ctor_set(v_reuseFailAlloc_830_, 14, v_lintDriver_806_);
lean_ctor_set(v_reuseFailAlloc_830_, 15, v_lintDriverArgs_807_);
lean_ctor_set(v_reuseFailAlloc_830_, 16, v_version_808_);
lean_ctor_set(v_reuseFailAlloc_830_, 17, v_versionTags_809_);
lean_ctor_set(v_reuseFailAlloc_830_, 18, v_description_810_);
lean_ctor_set(v_reuseFailAlloc_830_, 19, v_keywords_811_);
lean_ctor_set(v_reuseFailAlloc_830_, 20, v_homepage_812_);
lean_ctor_set(v_reuseFailAlloc_830_, 21, v_license_813_);
lean_ctor_set(v_reuseFailAlloc_830_, 22, v_licenseFiles_814_);
lean_ctor_set(v_reuseFailAlloc_830_, 23, v_readmeFile_815_);
lean_ctor_set(v_reuseFailAlloc_830_, 24, v_enableArtifactCache_x3f_817_);
lean_ctor_set(v_reuseFailAlloc_830_, 25, v_restoreAllArtifacts_x3f_818_);
lean_ctor_set(v_reuseFailAlloc_830_, 26, v_builtinLint_x3f_821_);
lean_ctor_set(v_reuseFailAlloc_830_, 27, v_checks_822_);
lean_ctor_set_uint8(v_reuseFailAlloc_830_, sizeof(void*)*28, v_bootstrap_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_830_, sizeof(void*)*28 + 1, v_precompileModules_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_830_, sizeof(void*)*28 + 2, v_preferReleaseBuild_803_);
lean_ctor_set_uint8(v_reuseFailAlloc_830_, sizeof(void*)*28 + 3, v_reservoir_816_);
lean_ctor_set_uint8(v_reuseFailAlloc_830_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_819_);
lean_ctor_set_uint8(v_reuseFailAlloc_830_, sizeof(void*)*28 + 5, v_allowImportAll_820_);
lean_ctor_set_uint8(v_reuseFailAlloc_830_, sizeof(void*)*28 + 6, v_fixedToolchain_823_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__3(lean_object* v_x_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lake_defaultBuildDir;
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__3___boxed(lean_object* v_x_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lake_PackageConfig_buildDir___proj___redArg___lam__3(v_x_834_);
lean_dec_ref(v_x_834_);
return v_res_835_;
}
}
lean_object* l_Lake_PackageConfig_buildDir___proj___redArg(){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = ((lean_object*)(l_Lake_PackageConfig_buildDir___proj___redArg___closed__4));
return v___x_846_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_buildDir___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_847_;
v_res_847_ = l_Lake_PackageConfig_buildDir___proj___redArg();
stack->m_obj
 = v_res_847_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___boxed(lean_object* v___dummy_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lake_PackageConfig_buildDir___proj___redArg();
return v_res_849_;
}
}
static lean_object* _init_l_Lake_PackageConfig_buildDir___proj___closed__0(void){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lake_PackageConfig_buildDir___proj___redArg();
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object* v_p_851_, lean_object* v_n_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_obj_once(&l_Lake_PackageConfig_buildDir___proj___closed__0, &l_Lake_PackageConfig_buildDir___proj___closed__0_once, _init_l_Lake_PackageConfig_buildDir___proj___closed__0);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object* v_p_854_, lean_object* v_n_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lake_PackageConfig_buildDir___proj(v_p_854_, v_n_855_);
lean_dec(v_n_855_);
lean_dec(v_p_854_);
return v_res_856_;
}
}
lean_object* l_Lake_PackageConfig_buildDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = lean_obj_once(&l_Lake_PackageConfig_buildDir___proj___closed__0, &l_Lake_PackageConfig_buildDir___proj___closed__0_once, _init_l_Lake_PackageConfig_buildDir___proj___closed__0);
return v___x_858_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_buildDir_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_859_;
v_res_859_ = l_Lake_PackageConfig_buildDir_instConfigField___redArg();
stack->m_obj
 = v_res_859_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___redArg___boxed(lean_object* v___dummy_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lake_PackageConfig_buildDir_instConfigField___redArg();
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object* v_p_862_, lean_object* v_n_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = lean_obj_once(&l_Lake_PackageConfig_buildDir___proj___closed__0, &l_Lake_PackageConfig_buildDir___proj___closed__0_once, _init_l_Lake_PackageConfig_buildDir___proj___closed__0);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object* v_p_865_, lean_object* v_n_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lake_PackageConfig_buildDir_instConfigField(v_p_865_, v_n_866_);
lean_dec(v_n_866_);
lean_dec(v_p_865_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0(lean_object* v_cfg_868_){
_start:
{
lean_object* v_leanLibDir_869_; 
v_leanLibDir_869_ = lean_ctor_get(v_cfg_868_, 6);
lean_inc_ref(v_leanLibDir_869_);
return v_leanLibDir_869_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0(v_cfg_870_);
lean_dec_ref(v_cfg_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__1(lean_object* v_val_872_, lean_object* v_cfg_873_){
_start:
{
lean_object* v_toWorkspaceConfig_874_; lean_object* v_toLeanConfig_875_; uint8_t v_bootstrap_876_; lean_object* v_extraDepTargets_877_; uint8_t v_precompileModules_878_; lean_object* v_moreGlobalServerArgs_879_; lean_object* v_srcDir_880_; lean_object* v_buildDir_881_; lean_object* v_nativeLibDir_882_; lean_object* v_binDir_883_; lean_object* v_irDir_884_; lean_object* v_releaseRepo_885_; lean_object* v_buildArchive_886_; uint8_t v_preferReleaseBuild_887_; lean_object* v_testDriver_888_; lean_object* v_testDriverArgs_889_; lean_object* v_lintDriver_890_; lean_object* v_lintDriverArgs_891_; lean_object* v_version_892_; lean_object* v_versionTags_893_; lean_object* v_description_894_; lean_object* v_keywords_895_; lean_object* v_homepage_896_; lean_object* v_license_897_; lean_object* v_licenseFiles_898_; lean_object* v_readmeFile_899_; uint8_t v_reservoir_900_; lean_object* v_enableArtifactCache_x3f_901_; lean_object* v_restoreAllArtifacts_x3f_902_; uint8_t v_libPrefixOnWindows_903_; uint8_t v_allowImportAll_904_; lean_object* v_builtinLint_x3f_905_; lean_object* v_checks_906_; uint8_t v_fixedToolchain_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_toWorkspaceConfig_874_ = lean_ctor_get(v_cfg_873_, 0);
v_toLeanConfig_875_ = lean_ctor_get(v_cfg_873_, 1);
v_bootstrap_876_ = lean_ctor_get_uint8(v_cfg_873_, sizeof(void*)*28);
v_extraDepTargets_877_ = lean_ctor_get(v_cfg_873_, 2);
v_precompileModules_878_ = lean_ctor_get_uint8(v_cfg_873_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_879_ = lean_ctor_get(v_cfg_873_, 3);
v_srcDir_880_ = lean_ctor_get(v_cfg_873_, 4);
v_buildDir_881_ = lean_ctor_get(v_cfg_873_, 5);
v_nativeLibDir_882_ = lean_ctor_get(v_cfg_873_, 7);
v_binDir_883_ = lean_ctor_get(v_cfg_873_, 8);
v_irDir_884_ = lean_ctor_get(v_cfg_873_, 9);
v_releaseRepo_885_ = lean_ctor_get(v_cfg_873_, 10);
v_buildArchive_886_ = lean_ctor_get(v_cfg_873_, 11);
v_preferReleaseBuild_887_ = lean_ctor_get_uint8(v_cfg_873_, sizeof(void*)*28 + 2);
v_testDriver_888_ = lean_ctor_get(v_cfg_873_, 12);
v_testDriverArgs_889_ = lean_ctor_get(v_cfg_873_, 13);
v_lintDriver_890_ = lean_ctor_get(v_cfg_873_, 14);
v_lintDriverArgs_891_ = lean_ctor_get(v_cfg_873_, 15);
v_version_892_ = lean_ctor_get(v_cfg_873_, 16);
v_versionTags_893_ = lean_ctor_get(v_cfg_873_, 17);
v_description_894_ = lean_ctor_get(v_cfg_873_, 18);
v_keywords_895_ = lean_ctor_get(v_cfg_873_, 19);
v_homepage_896_ = lean_ctor_get(v_cfg_873_, 20);
v_license_897_ = lean_ctor_get(v_cfg_873_, 21);
v_licenseFiles_898_ = lean_ctor_get(v_cfg_873_, 22);
v_readmeFile_899_ = lean_ctor_get(v_cfg_873_, 23);
v_reservoir_900_ = lean_ctor_get_uint8(v_cfg_873_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_901_ = lean_ctor_get(v_cfg_873_, 24);
v_restoreAllArtifacts_x3f_902_ = lean_ctor_get(v_cfg_873_, 25);
v_libPrefixOnWindows_903_ = lean_ctor_get_uint8(v_cfg_873_, sizeof(void*)*28 + 4);
v_allowImportAll_904_ = lean_ctor_get_uint8(v_cfg_873_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_905_ = lean_ctor_get(v_cfg_873_, 26);
v_checks_906_ = lean_ctor_get(v_cfg_873_, 27);
v_fixedToolchain_907_ = lean_ctor_get_uint8(v_cfg_873_, sizeof(void*)*28 + 6);
v_isSharedCheck_914_ = !lean_is_exclusive(v_cfg_873_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v_cfg_873_, 6);
lean_dec(v_unused_915_);
v___x_909_ = v_cfg_873_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_checks_906_);
lean_inc(v_builtinLint_x3f_905_);
lean_inc(v_restoreAllArtifacts_x3f_902_);
lean_inc(v_enableArtifactCache_x3f_901_);
lean_inc(v_readmeFile_899_);
lean_inc(v_licenseFiles_898_);
lean_inc(v_license_897_);
lean_inc(v_homepage_896_);
lean_inc(v_keywords_895_);
lean_inc(v_description_894_);
lean_inc(v_versionTags_893_);
lean_inc(v_version_892_);
lean_inc(v_lintDriverArgs_891_);
lean_inc(v_lintDriver_890_);
lean_inc(v_testDriverArgs_889_);
lean_inc(v_testDriver_888_);
lean_inc(v_buildArchive_886_);
lean_inc(v_releaseRepo_885_);
lean_inc(v_irDir_884_);
lean_inc(v_binDir_883_);
lean_inc(v_nativeLibDir_882_);
lean_inc(v_buildDir_881_);
lean_inc(v_srcDir_880_);
lean_inc(v_moreGlobalServerArgs_879_);
lean_inc(v_extraDepTargets_877_);
lean_inc(v_toLeanConfig_875_);
lean_inc(v_toWorkspaceConfig_874_);
lean_dec(v_cfg_873_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 6, v_val_872_);
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_toWorkspaceConfig_874_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_toLeanConfig_875_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_extraDepTargets_877_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_moreGlobalServerArgs_879_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_srcDir_880_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v_buildDir_881_);
lean_ctor_set(v_reuseFailAlloc_913_, 6, v_val_872_);
lean_ctor_set(v_reuseFailAlloc_913_, 7, v_nativeLibDir_882_);
lean_ctor_set(v_reuseFailAlloc_913_, 8, v_binDir_883_);
lean_ctor_set(v_reuseFailAlloc_913_, 9, v_irDir_884_);
lean_ctor_set(v_reuseFailAlloc_913_, 10, v_releaseRepo_885_);
lean_ctor_set(v_reuseFailAlloc_913_, 11, v_buildArchive_886_);
lean_ctor_set(v_reuseFailAlloc_913_, 12, v_testDriver_888_);
lean_ctor_set(v_reuseFailAlloc_913_, 13, v_testDriverArgs_889_);
lean_ctor_set(v_reuseFailAlloc_913_, 14, v_lintDriver_890_);
lean_ctor_set(v_reuseFailAlloc_913_, 15, v_lintDriverArgs_891_);
lean_ctor_set(v_reuseFailAlloc_913_, 16, v_version_892_);
lean_ctor_set(v_reuseFailAlloc_913_, 17, v_versionTags_893_);
lean_ctor_set(v_reuseFailAlloc_913_, 18, v_description_894_);
lean_ctor_set(v_reuseFailAlloc_913_, 19, v_keywords_895_);
lean_ctor_set(v_reuseFailAlloc_913_, 20, v_homepage_896_);
lean_ctor_set(v_reuseFailAlloc_913_, 21, v_license_897_);
lean_ctor_set(v_reuseFailAlloc_913_, 22, v_licenseFiles_898_);
lean_ctor_set(v_reuseFailAlloc_913_, 23, v_readmeFile_899_);
lean_ctor_set(v_reuseFailAlloc_913_, 24, v_enableArtifactCache_x3f_901_);
lean_ctor_set(v_reuseFailAlloc_913_, 25, v_restoreAllArtifacts_x3f_902_);
lean_ctor_set(v_reuseFailAlloc_913_, 26, v_builtinLint_x3f_905_);
lean_ctor_set(v_reuseFailAlloc_913_, 27, v_checks_906_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*28, v_bootstrap_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*28 + 1, v_precompileModules_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*28 + 2, v_preferReleaseBuild_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*28 + 3, v_reservoir_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*28 + 5, v_allowImportAll_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*28 + 6, v_fixedToolchain_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__2(lean_object* v_f_916_, lean_object* v_cfg_917_){
_start:
{
lean_object* v_toWorkspaceConfig_918_; lean_object* v_toLeanConfig_919_; uint8_t v_bootstrap_920_; lean_object* v_extraDepTargets_921_; uint8_t v_precompileModules_922_; lean_object* v_moreGlobalServerArgs_923_; lean_object* v_srcDir_924_; lean_object* v_buildDir_925_; lean_object* v_leanLibDir_926_; lean_object* v_nativeLibDir_927_; lean_object* v_binDir_928_; lean_object* v_irDir_929_; lean_object* v_releaseRepo_930_; lean_object* v_buildArchive_931_; uint8_t v_preferReleaseBuild_932_; lean_object* v_testDriver_933_; lean_object* v_testDriverArgs_934_; lean_object* v_lintDriver_935_; lean_object* v_lintDriverArgs_936_; lean_object* v_version_937_; lean_object* v_versionTags_938_; lean_object* v_description_939_; lean_object* v_keywords_940_; lean_object* v_homepage_941_; lean_object* v_license_942_; lean_object* v_licenseFiles_943_; lean_object* v_readmeFile_944_; uint8_t v_reservoir_945_; lean_object* v_enableArtifactCache_x3f_946_; lean_object* v_restoreAllArtifacts_x3f_947_; uint8_t v_libPrefixOnWindows_948_; uint8_t v_allowImportAll_949_; lean_object* v_builtinLint_x3f_950_; lean_object* v_checks_951_; uint8_t v_fixedToolchain_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_960_; 
v_toWorkspaceConfig_918_ = lean_ctor_get(v_cfg_917_, 0);
v_toLeanConfig_919_ = lean_ctor_get(v_cfg_917_, 1);
v_bootstrap_920_ = lean_ctor_get_uint8(v_cfg_917_, sizeof(void*)*28);
v_extraDepTargets_921_ = lean_ctor_get(v_cfg_917_, 2);
v_precompileModules_922_ = lean_ctor_get_uint8(v_cfg_917_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_923_ = lean_ctor_get(v_cfg_917_, 3);
v_srcDir_924_ = lean_ctor_get(v_cfg_917_, 4);
v_buildDir_925_ = lean_ctor_get(v_cfg_917_, 5);
v_leanLibDir_926_ = lean_ctor_get(v_cfg_917_, 6);
v_nativeLibDir_927_ = lean_ctor_get(v_cfg_917_, 7);
v_binDir_928_ = lean_ctor_get(v_cfg_917_, 8);
v_irDir_929_ = lean_ctor_get(v_cfg_917_, 9);
v_releaseRepo_930_ = lean_ctor_get(v_cfg_917_, 10);
v_buildArchive_931_ = lean_ctor_get(v_cfg_917_, 11);
v_preferReleaseBuild_932_ = lean_ctor_get_uint8(v_cfg_917_, sizeof(void*)*28 + 2);
v_testDriver_933_ = lean_ctor_get(v_cfg_917_, 12);
v_testDriverArgs_934_ = lean_ctor_get(v_cfg_917_, 13);
v_lintDriver_935_ = lean_ctor_get(v_cfg_917_, 14);
v_lintDriverArgs_936_ = lean_ctor_get(v_cfg_917_, 15);
v_version_937_ = lean_ctor_get(v_cfg_917_, 16);
v_versionTags_938_ = lean_ctor_get(v_cfg_917_, 17);
v_description_939_ = lean_ctor_get(v_cfg_917_, 18);
v_keywords_940_ = lean_ctor_get(v_cfg_917_, 19);
v_homepage_941_ = lean_ctor_get(v_cfg_917_, 20);
v_license_942_ = lean_ctor_get(v_cfg_917_, 21);
v_licenseFiles_943_ = lean_ctor_get(v_cfg_917_, 22);
v_readmeFile_944_ = lean_ctor_get(v_cfg_917_, 23);
v_reservoir_945_ = lean_ctor_get_uint8(v_cfg_917_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_946_ = lean_ctor_get(v_cfg_917_, 24);
v_restoreAllArtifacts_x3f_947_ = lean_ctor_get(v_cfg_917_, 25);
v_libPrefixOnWindows_948_ = lean_ctor_get_uint8(v_cfg_917_, sizeof(void*)*28 + 4);
v_allowImportAll_949_ = lean_ctor_get_uint8(v_cfg_917_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_950_ = lean_ctor_get(v_cfg_917_, 26);
v_checks_951_ = lean_ctor_get(v_cfg_917_, 27);
v_fixedToolchain_952_ = lean_ctor_get_uint8(v_cfg_917_, sizeof(void*)*28 + 6);
v_isSharedCheck_960_ = !lean_is_exclusive(v_cfg_917_);
if (v_isSharedCheck_960_ == 0)
{
v___x_954_ = v_cfg_917_;
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_checks_951_);
lean_inc(v_builtinLint_x3f_950_);
lean_inc(v_restoreAllArtifacts_x3f_947_);
lean_inc(v_enableArtifactCache_x3f_946_);
lean_inc(v_readmeFile_944_);
lean_inc(v_licenseFiles_943_);
lean_inc(v_license_942_);
lean_inc(v_homepage_941_);
lean_inc(v_keywords_940_);
lean_inc(v_description_939_);
lean_inc(v_versionTags_938_);
lean_inc(v_version_937_);
lean_inc(v_lintDriverArgs_936_);
lean_inc(v_lintDriver_935_);
lean_inc(v_testDriverArgs_934_);
lean_inc(v_testDriver_933_);
lean_inc(v_buildArchive_931_);
lean_inc(v_releaseRepo_930_);
lean_inc(v_irDir_929_);
lean_inc(v_binDir_928_);
lean_inc(v_nativeLibDir_927_);
lean_inc(v_leanLibDir_926_);
lean_inc(v_buildDir_925_);
lean_inc(v_srcDir_924_);
lean_inc(v_moreGlobalServerArgs_923_);
lean_inc(v_extraDepTargets_921_);
lean_inc(v_toLeanConfig_919_);
lean_inc(v_toWorkspaceConfig_918_);
lean_dec(v_cfg_917_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = lean_apply_1(v_f_916_, v_leanLibDir_926_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 6, v___x_956_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_toWorkspaceConfig_918_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_toLeanConfig_919_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_extraDepTargets_921_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_moreGlobalServerArgs_923_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_srcDir_924_);
lean_ctor_set(v_reuseFailAlloc_959_, 5, v_buildDir_925_);
lean_ctor_set(v_reuseFailAlloc_959_, 6, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_959_, 7, v_nativeLibDir_927_);
lean_ctor_set(v_reuseFailAlloc_959_, 8, v_binDir_928_);
lean_ctor_set(v_reuseFailAlloc_959_, 9, v_irDir_929_);
lean_ctor_set(v_reuseFailAlloc_959_, 10, v_releaseRepo_930_);
lean_ctor_set(v_reuseFailAlloc_959_, 11, v_buildArchive_931_);
lean_ctor_set(v_reuseFailAlloc_959_, 12, v_testDriver_933_);
lean_ctor_set(v_reuseFailAlloc_959_, 13, v_testDriverArgs_934_);
lean_ctor_set(v_reuseFailAlloc_959_, 14, v_lintDriver_935_);
lean_ctor_set(v_reuseFailAlloc_959_, 15, v_lintDriverArgs_936_);
lean_ctor_set(v_reuseFailAlloc_959_, 16, v_version_937_);
lean_ctor_set(v_reuseFailAlloc_959_, 17, v_versionTags_938_);
lean_ctor_set(v_reuseFailAlloc_959_, 18, v_description_939_);
lean_ctor_set(v_reuseFailAlloc_959_, 19, v_keywords_940_);
lean_ctor_set(v_reuseFailAlloc_959_, 20, v_homepage_941_);
lean_ctor_set(v_reuseFailAlloc_959_, 21, v_license_942_);
lean_ctor_set(v_reuseFailAlloc_959_, 22, v_licenseFiles_943_);
lean_ctor_set(v_reuseFailAlloc_959_, 23, v_readmeFile_944_);
lean_ctor_set(v_reuseFailAlloc_959_, 24, v_enableArtifactCache_x3f_946_);
lean_ctor_set(v_reuseFailAlloc_959_, 25, v_restoreAllArtifacts_x3f_947_);
lean_ctor_set(v_reuseFailAlloc_959_, 26, v_builtinLint_x3f_950_);
lean_ctor_set(v_reuseFailAlloc_959_, 27, v_checks_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*28, v_bootstrap_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*28 + 1, v_precompileModules_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*28 + 2, v_preferReleaseBuild_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*28 + 3, v_reservoir_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_948_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*28 + 5, v_allowImportAll_949_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*28 + 6, v_fixedToolchain_952_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3(lean_object* v_x_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lake_defaultLeanLibDir;
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3___boxed(lean_object* v_x_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3(v_x_963_);
lean_dec_ref(v_x_963_);
return v_res_964_;
}
}
lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg(){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__4));
return v___x_975_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_leanLibDir___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_976_;
v_res_976_ = l_Lake_PackageConfig_leanLibDir___proj___redArg();
stack->m_obj
 = v_res_976_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___boxed(lean_object* v___dummy_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lake_PackageConfig_leanLibDir___proj___redArg();
return v_res_978_;
}
}
static lean_object* _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0(void){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lake_PackageConfig_leanLibDir___proj___redArg();
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object* v_p_980_, lean_object* v_n_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = lean_obj_once(&l_Lake_PackageConfig_leanLibDir___proj___closed__0, &l_Lake_PackageConfig_leanLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object* v_p_983_, lean_object* v_n_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_983_, v_n_984_);
lean_dec(v_n_984_);
lean_dec(v_p_983_);
return v_res_985_;
}
}
lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_obj_once(&l_Lake_PackageConfig_leanLibDir___proj___closed__0, &l_Lake_PackageConfig_leanLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0);
return v___x_987_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_leanLibDir_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_988_;
v_res_988_ = l_Lake_PackageConfig_leanLibDir_instConfigField___redArg();
stack->m_obj
 = v_res_988_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___redArg___boxed(lean_object* v___dummy_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lake_PackageConfig_leanLibDir_instConfigField___redArg();
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object* v_p_991_, lean_object* v_n_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = lean_obj_once(&l_Lake_PackageConfig_leanLibDir___proj___closed__0, &l_Lake_PackageConfig_leanLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object* v_p_994_, lean_object* v_n_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lake_PackageConfig_leanLibDir_instConfigField(v_p_994_, v_n_995_);
lean_dec(v_n_995_);
lean_dec(v_p_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0(lean_object* v_cfg_997_){
_start:
{
lean_object* v_nativeLibDir_998_; 
v_nativeLibDir_998_ = lean_ctor_get(v_cfg_997_, 7);
lean_inc_ref(v_nativeLibDir_998_);
return v_nativeLibDir_998_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0(v_cfg_999_);
lean_dec_ref(v_cfg_999_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__1(lean_object* v_val_1001_, lean_object* v_cfg_1002_){
_start:
{
lean_object* v_toWorkspaceConfig_1003_; lean_object* v_toLeanConfig_1004_; uint8_t v_bootstrap_1005_; lean_object* v_extraDepTargets_1006_; uint8_t v_precompileModules_1007_; lean_object* v_moreGlobalServerArgs_1008_; lean_object* v_srcDir_1009_; lean_object* v_buildDir_1010_; lean_object* v_leanLibDir_1011_; lean_object* v_binDir_1012_; lean_object* v_irDir_1013_; lean_object* v_releaseRepo_1014_; lean_object* v_buildArchive_1015_; uint8_t v_preferReleaseBuild_1016_; lean_object* v_testDriver_1017_; lean_object* v_testDriverArgs_1018_; lean_object* v_lintDriver_1019_; lean_object* v_lintDriverArgs_1020_; lean_object* v_version_1021_; lean_object* v_versionTags_1022_; lean_object* v_description_1023_; lean_object* v_keywords_1024_; lean_object* v_homepage_1025_; lean_object* v_license_1026_; lean_object* v_licenseFiles_1027_; lean_object* v_readmeFile_1028_; uint8_t v_reservoir_1029_; lean_object* v_enableArtifactCache_x3f_1030_; lean_object* v_restoreAllArtifacts_x3f_1031_; uint8_t v_libPrefixOnWindows_1032_; uint8_t v_allowImportAll_1033_; lean_object* v_builtinLint_x3f_1034_; lean_object* v_checks_1035_; uint8_t v_fixedToolchain_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_toWorkspaceConfig_1003_ = lean_ctor_get(v_cfg_1002_, 0);
v_toLeanConfig_1004_ = lean_ctor_get(v_cfg_1002_, 1);
v_bootstrap_1005_ = lean_ctor_get_uint8(v_cfg_1002_, sizeof(void*)*28);
v_extraDepTargets_1006_ = lean_ctor_get(v_cfg_1002_, 2);
v_precompileModules_1007_ = lean_ctor_get_uint8(v_cfg_1002_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1008_ = lean_ctor_get(v_cfg_1002_, 3);
v_srcDir_1009_ = lean_ctor_get(v_cfg_1002_, 4);
v_buildDir_1010_ = lean_ctor_get(v_cfg_1002_, 5);
v_leanLibDir_1011_ = lean_ctor_get(v_cfg_1002_, 6);
v_binDir_1012_ = lean_ctor_get(v_cfg_1002_, 8);
v_irDir_1013_ = lean_ctor_get(v_cfg_1002_, 9);
v_releaseRepo_1014_ = lean_ctor_get(v_cfg_1002_, 10);
v_buildArchive_1015_ = lean_ctor_get(v_cfg_1002_, 11);
v_preferReleaseBuild_1016_ = lean_ctor_get_uint8(v_cfg_1002_, sizeof(void*)*28 + 2);
v_testDriver_1017_ = lean_ctor_get(v_cfg_1002_, 12);
v_testDriverArgs_1018_ = lean_ctor_get(v_cfg_1002_, 13);
v_lintDriver_1019_ = lean_ctor_get(v_cfg_1002_, 14);
v_lintDriverArgs_1020_ = lean_ctor_get(v_cfg_1002_, 15);
v_version_1021_ = lean_ctor_get(v_cfg_1002_, 16);
v_versionTags_1022_ = lean_ctor_get(v_cfg_1002_, 17);
v_description_1023_ = lean_ctor_get(v_cfg_1002_, 18);
v_keywords_1024_ = lean_ctor_get(v_cfg_1002_, 19);
v_homepage_1025_ = lean_ctor_get(v_cfg_1002_, 20);
v_license_1026_ = lean_ctor_get(v_cfg_1002_, 21);
v_licenseFiles_1027_ = lean_ctor_get(v_cfg_1002_, 22);
v_readmeFile_1028_ = lean_ctor_get(v_cfg_1002_, 23);
v_reservoir_1029_ = lean_ctor_get_uint8(v_cfg_1002_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1030_ = lean_ctor_get(v_cfg_1002_, 24);
v_restoreAllArtifacts_x3f_1031_ = lean_ctor_get(v_cfg_1002_, 25);
v_libPrefixOnWindows_1032_ = lean_ctor_get_uint8(v_cfg_1002_, sizeof(void*)*28 + 4);
v_allowImportAll_1033_ = lean_ctor_get_uint8(v_cfg_1002_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1034_ = lean_ctor_get(v_cfg_1002_, 26);
v_checks_1035_ = lean_ctor_get(v_cfg_1002_, 27);
v_fixedToolchain_1036_ = lean_ctor_get_uint8(v_cfg_1002_, sizeof(void*)*28 + 6);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_cfg_1002_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v_cfg_1002_, 7);
lean_dec(v_unused_1044_);
v___x_1038_ = v_cfg_1002_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_checks_1035_);
lean_inc(v_builtinLint_x3f_1034_);
lean_inc(v_restoreAllArtifacts_x3f_1031_);
lean_inc(v_enableArtifactCache_x3f_1030_);
lean_inc(v_readmeFile_1028_);
lean_inc(v_licenseFiles_1027_);
lean_inc(v_license_1026_);
lean_inc(v_homepage_1025_);
lean_inc(v_keywords_1024_);
lean_inc(v_description_1023_);
lean_inc(v_versionTags_1022_);
lean_inc(v_version_1021_);
lean_inc(v_lintDriverArgs_1020_);
lean_inc(v_lintDriver_1019_);
lean_inc(v_testDriverArgs_1018_);
lean_inc(v_testDriver_1017_);
lean_inc(v_buildArchive_1015_);
lean_inc(v_releaseRepo_1014_);
lean_inc(v_irDir_1013_);
lean_inc(v_binDir_1012_);
lean_inc(v_leanLibDir_1011_);
lean_inc(v_buildDir_1010_);
lean_inc(v_srcDir_1009_);
lean_inc(v_moreGlobalServerArgs_1008_);
lean_inc(v_extraDepTargets_1006_);
lean_inc(v_toLeanConfig_1004_);
lean_inc(v_toWorkspaceConfig_1003_);
lean_dec(v_cfg_1002_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 7, v_val_1001_);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_toWorkspaceConfig_1003_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_toLeanConfig_1004_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_extraDepTargets_1006_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_moreGlobalServerArgs_1008_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_srcDir_1009_);
lean_ctor_set(v_reuseFailAlloc_1042_, 5, v_buildDir_1010_);
lean_ctor_set(v_reuseFailAlloc_1042_, 6, v_leanLibDir_1011_);
lean_ctor_set(v_reuseFailAlloc_1042_, 7, v_val_1001_);
lean_ctor_set(v_reuseFailAlloc_1042_, 8, v_binDir_1012_);
lean_ctor_set(v_reuseFailAlloc_1042_, 9, v_irDir_1013_);
lean_ctor_set(v_reuseFailAlloc_1042_, 10, v_releaseRepo_1014_);
lean_ctor_set(v_reuseFailAlloc_1042_, 11, v_buildArchive_1015_);
lean_ctor_set(v_reuseFailAlloc_1042_, 12, v_testDriver_1017_);
lean_ctor_set(v_reuseFailAlloc_1042_, 13, v_testDriverArgs_1018_);
lean_ctor_set(v_reuseFailAlloc_1042_, 14, v_lintDriver_1019_);
lean_ctor_set(v_reuseFailAlloc_1042_, 15, v_lintDriverArgs_1020_);
lean_ctor_set(v_reuseFailAlloc_1042_, 16, v_version_1021_);
lean_ctor_set(v_reuseFailAlloc_1042_, 17, v_versionTags_1022_);
lean_ctor_set(v_reuseFailAlloc_1042_, 18, v_description_1023_);
lean_ctor_set(v_reuseFailAlloc_1042_, 19, v_keywords_1024_);
lean_ctor_set(v_reuseFailAlloc_1042_, 20, v_homepage_1025_);
lean_ctor_set(v_reuseFailAlloc_1042_, 21, v_license_1026_);
lean_ctor_set(v_reuseFailAlloc_1042_, 22, v_licenseFiles_1027_);
lean_ctor_set(v_reuseFailAlloc_1042_, 23, v_readmeFile_1028_);
lean_ctor_set(v_reuseFailAlloc_1042_, 24, v_enableArtifactCache_x3f_1030_);
lean_ctor_set(v_reuseFailAlloc_1042_, 25, v_restoreAllArtifacts_x3f_1031_);
lean_ctor_set(v_reuseFailAlloc_1042_, 26, v_builtinLint_x3f_1034_);
lean_ctor_set(v_reuseFailAlloc_1042_, 27, v_checks_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*28, v_bootstrap_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*28 + 1, v_precompileModules_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*28 + 3, v_reservoir_1029_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1032_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*28 + 5, v_allowImportAll_1033_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*28 + 6, v_fixedToolchain_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__2(lean_object* v_f_1045_, lean_object* v_cfg_1046_){
_start:
{
lean_object* v_toWorkspaceConfig_1047_; lean_object* v_toLeanConfig_1048_; uint8_t v_bootstrap_1049_; lean_object* v_extraDepTargets_1050_; uint8_t v_precompileModules_1051_; lean_object* v_moreGlobalServerArgs_1052_; lean_object* v_srcDir_1053_; lean_object* v_buildDir_1054_; lean_object* v_leanLibDir_1055_; lean_object* v_nativeLibDir_1056_; lean_object* v_binDir_1057_; lean_object* v_irDir_1058_; lean_object* v_releaseRepo_1059_; lean_object* v_buildArchive_1060_; uint8_t v_preferReleaseBuild_1061_; lean_object* v_testDriver_1062_; lean_object* v_testDriverArgs_1063_; lean_object* v_lintDriver_1064_; lean_object* v_lintDriverArgs_1065_; lean_object* v_version_1066_; lean_object* v_versionTags_1067_; lean_object* v_description_1068_; lean_object* v_keywords_1069_; lean_object* v_homepage_1070_; lean_object* v_license_1071_; lean_object* v_licenseFiles_1072_; lean_object* v_readmeFile_1073_; uint8_t v_reservoir_1074_; lean_object* v_enableArtifactCache_x3f_1075_; lean_object* v_restoreAllArtifacts_x3f_1076_; uint8_t v_libPrefixOnWindows_1077_; uint8_t v_allowImportAll_1078_; lean_object* v_builtinLint_x3f_1079_; lean_object* v_checks_1080_; uint8_t v_fixedToolchain_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1089_; 
v_toWorkspaceConfig_1047_ = lean_ctor_get(v_cfg_1046_, 0);
v_toLeanConfig_1048_ = lean_ctor_get(v_cfg_1046_, 1);
v_bootstrap_1049_ = lean_ctor_get_uint8(v_cfg_1046_, sizeof(void*)*28);
v_extraDepTargets_1050_ = lean_ctor_get(v_cfg_1046_, 2);
v_precompileModules_1051_ = lean_ctor_get_uint8(v_cfg_1046_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1052_ = lean_ctor_get(v_cfg_1046_, 3);
v_srcDir_1053_ = lean_ctor_get(v_cfg_1046_, 4);
v_buildDir_1054_ = lean_ctor_get(v_cfg_1046_, 5);
v_leanLibDir_1055_ = lean_ctor_get(v_cfg_1046_, 6);
v_nativeLibDir_1056_ = lean_ctor_get(v_cfg_1046_, 7);
v_binDir_1057_ = lean_ctor_get(v_cfg_1046_, 8);
v_irDir_1058_ = lean_ctor_get(v_cfg_1046_, 9);
v_releaseRepo_1059_ = lean_ctor_get(v_cfg_1046_, 10);
v_buildArchive_1060_ = lean_ctor_get(v_cfg_1046_, 11);
v_preferReleaseBuild_1061_ = lean_ctor_get_uint8(v_cfg_1046_, sizeof(void*)*28 + 2);
v_testDriver_1062_ = lean_ctor_get(v_cfg_1046_, 12);
v_testDriverArgs_1063_ = lean_ctor_get(v_cfg_1046_, 13);
v_lintDriver_1064_ = lean_ctor_get(v_cfg_1046_, 14);
v_lintDriverArgs_1065_ = lean_ctor_get(v_cfg_1046_, 15);
v_version_1066_ = lean_ctor_get(v_cfg_1046_, 16);
v_versionTags_1067_ = lean_ctor_get(v_cfg_1046_, 17);
v_description_1068_ = lean_ctor_get(v_cfg_1046_, 18);
v_keywords_1069_ = lean_ctor_get(v_cfg_1046_, 19);
v_homepage_1070_ = lean_ctor_get(v_cfg_1046_, 20);
v_license_1071_ = lean_ctor_get(v_cfg_1046_, 21);
v_licenseFiles_1072_ = lean_ctor_get(v_cfg_1046_, 22);
v_readmeFile_1073_ = lean_ctor_get(v_cfg_1046_, 23);
v_reservoir_1074_ = lean_ctor_get_uint8(v_cfg_1046_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1075_ = lean_ctor_get(v_cfg_1046_, 24);
v_restoreAllArtifacts_x3f_1076_ = lean_ctor_get(v_cfg_1046_, 25);
v_libPrefixOnWindows_1077_ = lean_ctor_get_uint8(v_cfg_1046_, sizeof(void*)*28 + 4);
v_allowImportAll_1078_ = lean_ctor_get_uint8(v_cfg_1046_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1079_ = lean_ctor_get(v_cfg_1046_, 26);
v_checks_1080_ = lean_ctor_get(v_cfg_1046_, 27);
v_fixedToolchain_1081_ = lean_ctor_get_uint8(v_cfg_1046_, sizeof(void*)*28 + 6);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_cfg_1046_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1083_ = v_cfg_1046_;
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_checks_1080_);
lean_inc(v_builtinLint_x3f_1079_);
lean_inc(v_restoreAllArtifacts_x3f_1076_);
lean_inc(v_enableArtifactCache_x3f_1075_);
lean_inc(v_readmeFile_1073_);
lean_inc(v_licenseFiles_1072_);
lean_inc(v_license_1071_);
lean_inc(v_homepage_1070_);
lean_inc(v_keywords_1069_);
lean_inc(v_description_1068_);
lean_inc(v_versionTags_1067_);
lean_inc(v_version_1066_);
lean_inc(v_lintDriverArgs_1065_);
lean_inc(v_lintDriver_1064_);
lean_inc(v_testDriverArgs_1063_);
lean_inc(v_testDriver_1062_);
lean_inc(v_buildArchive_1060_);
lean_inc(v_releaseRepo_1059_);
lean_inc(v_irDir_1058_);
lean_inc(v_binDir_1057_);
lean_inc(v_nativeLibDir_1056_);
lean_inc(v_leanLibDir_1055_);
lean_inc(v_buildDir_1054_);
lean_inc(v_srcDir_1053_);
lean_inc(v_moreGlobalServerArgs_1052_);
lean_inc(v_extraDepTargets_1050_);
lean_inc(v_toLeanConfig_1048_);
lean_inc(v_toWorkspaceConfig_1047_);
lean_dec(v_cfg_1046_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_apply_1(v_f_1045_, v_nativeLibDir_1056_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 7, v___x_1085_);
v___x_1087_ = v___x_1083_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_toWorkspaceConfig_1047_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_toLeanConfig_1048_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_extraDepTargets_1050_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_moreGlobalServerArgs_1052_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_srcDir_1053_);
lean_ctor_set(v_reuseFailAlloc_1088_, 5, v_buildDir_1054_);
lean_ctor_set(v_reuseFailAlloc_1088_, 6, v_leanLibDir_1055_);
lean_ctor_set(v_reuseFailAlloc_1088_, 7, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1088_, 8, v_binDir_1057_);
lean_ctor_set(v_reuseFailAlloc_1088_, 9, v_irDir_1058_);
lean_ctor_set(v_reuseFailAlloc_1088_, 10, v_releaseRepo_1059_);
lean_ctor_set(v_reuseFailAlloc_1088_, 11, v_buildArchive_1060_);
lean_ctor_set(v_reuseFailAlloc_1088_, 12, v_testDriver_1062_);
lean_ctor_set(v_reuseFailAlloc_1088_, 13, v_testDriverArgs_1063_);
lean_ctor_set(v_reuseFailAlloc_1088_, 14, v_lintDriver_1064_);
lean_ctor_set(v_reuseFailAlloc_1088_, 15, v_lintDriverArgs_1065_);
lean_ctor_set(v_reuseFailAlloc_1088_, 16, v_version_1066_);
lean_ctor_set(v_reuseFailAlloc_1088_, 17, v_versionTags_1067_);
lean_ctor_set(v_reuseFailAlloc_1088_, 18, v_description_1068_);
lean_ctor_set(v_reuseFailAlloc_1088_, 19, v_keywords_1069_);
lean_ctor_set(v_reuseFailAlloc_1088_, 20, v_homepage_1070_);
lean_ctor_set(v_reuseFailAlloc_1088_, 21, v_license_1071_);
lean_ctor_set(v_reuseFailAlloc_1088_, 22, v_licenseFiles_1072_);
lean_ctor_set(v_reuseFailAlloc_1088_, 23, v_readmeFile_1073_);
lean_ctor_set(v_reuseFailAlloc_1088_, 24, v_enableArtifactCache_x3f_1075_);
lean_ctor_set(v_reuseFailAlloc_1088_, 25, v_restoreAllArtifacts_x3f_1076_);
lean_ctor_set(v_reuseFailAlloc_1088_, 26, v_builtinLint_x3f_1079_);
lean_ctor_set(v_reuseFailAlloc_1088_, 27, v_checks_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*28, v_bootstrap_1049_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*28 + 1, v_precompileModules_1051_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1061_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*28 + 3, v_reservoir_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1077_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*28 + 5, v_allowImportAll_1078_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*28 + 6, v_fixedToolchain_1081_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3(lean_object* v_x_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lake_defaultNativeLibDir;
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3___boxed(lean_object* v_x_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3(v_x_1092_);
lean_dec_ref(v_x_1092_);
return v_res_1093_;
}
}
lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg(){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = ((lean_object*)(l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__4));
return v___x_1104_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_nativeLibDir___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1105_;
v_res_1105_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg();
stack->m_obj
 = v_res_1105_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___boxed(lean_object* v___dummy_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg();
return v_res_1107_;
}
}
static lean_object* _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0(void){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg();
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object* v_p_1109_, lean_object* v_n_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_obj_once(&l_Lake_PackageConfig_nativeLibDir___proj___closed__0, &l_Lake_PackageConfig_nativeLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object* v_p_1112_, lean_object* v_n_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_1112_, v_n_1113_);
lean_dec(v_n_1113_);
lean_dec(v_p_1112_);
return v_res_1114_;
}
}
lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_obj_once(&l_Lake_PackageConfig_nativeLibDir___proj___closed__0, &l_Lake_PackageConfig_nativeLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0);
return v___x_1116_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1117_;
v_res_1117_ = l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg();
stack->m_obj
 = v_res_1117_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg___boxed(lean_object* v___dummy_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg();
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object* v_p_1120_, lean_object* v_n_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_obj_once(&l_Lake_PackageConfig_nativeLibDir___proj___closed__0, &l_Lake_PackageConfig_nativeLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object* v_p_1123_, lean_object* v_n_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lake_PackageConfig_nativeLibDir_instConfigField(v_p_1123_, v_n_1124_);
lean_dec(v_n_1124_);
lean_dec(v_p_1123_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__0(lean_object* v_cfg_1126_){
_start:
{
lean_object* v_binDir_1127_; 
v_binDir_1127_ = lean_ctor_get(v_cfg_1126_, 8);
lean_inc_ref(v_binDir_1127_);
return v_binDir_1127_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lake_PackageConfig_binDir___proj___redArg___lam__0(v_cfg_1128_);
lean_dec_ref(v_cfg_1128_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__1(lean_object* v_val_1130_, lean_object* v_cfg_1131_){
_start:
{
lean_object* v_toWorkspaceConfig_1132_; lean_object* v_toLeanConfig_1133_; uint8_t v_bootstrap_1134_; lean_object* v_extraDepTargets_1135_; uint8_t v_precompileModules_1136_; lean_object* v_moreGlobalServerArgs_1137_; lean_object* v_srcDir_1138_; lean_object* v_buildDir_1139_; lean_object* v_leanLibDir_1140_; lean_object* v_nativeLibDir_1141_; lean_object* v_irDir_1142_; lean_object* v_releaseRepo_1143_; lean_object* v_buildArchive_1144_; uint8_t v_preferReleaseBuild_1145_; lean_object* v_testDriver_1146_; lean_object* v_testDriverArgs_1147_; lean_object* v_lintDriver_1148_; lean_object* v_lintDriverArgs_1149_; lean_object* v_version_1150_; lean_object* v_versionTags_1151_; lean_object* v_description_1152_; lean_object* v_keywords_1153_; lean_object* v_homepage_1154_; lean_object* v_license_1155_; lean_object* v_licenseFiles_1156_; lean_object* v_readmeFile_1157_; uint8_t v_reservoir_1158_; lean_object* v_enableArtifactCache_x3f_1159_; lean_object* v_restoreAllArtifacts_x3f_1160_; uint8_t v_libPrefixOnWindows_1161_; uint8_t v_allowImportAll_1162_; lean_object* v_builtinLint_x3f_1163_; lean_object* v_checks_1164_; uint8_t v_fixedToolchain_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_toWorkspaceConfig_1132_ = lean_ctor_get(v_cfg_1131_, 0);
v_toLeanConfig_1133_ = lean_ctor_get(v_cfg_1131_, 1);
v_bootstrap_1134_ = lean_ctor_get_uint8(v_cfg_1131_, sizeof(void*)*28);
v_extraDepTargets_1135_ = lean_ctor_get(v_cfg_1131_, 2);
v_precompileModules_1136_ = lean_ctor_get_uint8(v_cfg_1131_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1137_ = lean_ctor_get(v_cfg_1131_, 3);
v_srcDir_1138_ = lean_ctor_get(v_cfg_1131_, 4);
v_buildDir_1139_ = lean_ctor_get(v_cfg_1131_, 5);
v_leanLibDir_1140_ = lean_ctor_get(v_cfg_1131_, 6);
v_nativeLibDir_1141_ = lean_ctor_get(v_cfg_1131_, 7);
v_irDir_1142_ = lean_ctor_get(v_cfg_1131_, 9);
v_releaseRepo_1143_ = lean_ctor_get(v_cfg_1131_, 10);
v_buildArchive_1144_ = lean_ctor_get(v_cfg_1131_, 11);
v_preferReleaseBuild_1145_ = lean_ctor_get_uint8(v_cfg_1131_, sizeof(void*)*28 + 2);
v_testDriver_1146_ = lean_ctor_get(v_cfg_1131_, 12);
v_testDriverArgs_1147_ = lean_ctor_get(v_cfg_1131_, 13);
v_lintDriver_1148_ = lean_ctor_get(v_cfg_1131_, 14);
v_lintDriverArgs_1149_ = lean_ctor_get(v_cfg_1131_, 15);
v_version_1150_ = lean_ctor_get(v_cfg_1131_, 16);
v_versionTags_1151_ = lean_ctor_get(v_cfg_1131_, 17);
v_description_1152_ = lean_ctor_get(v_cfg_1131_, 18);
v_keywords_1153_ = lean_ctor_get(v_cfg_1131_, 19);
v_homepage_1154_ = lean_ctor_get(v_cfg_1131_, 20);
v_license_1155_ = lean_ctor_get(v_cfg_1131_, 21);
v_licenseFiles_1156_ = lean_ctor_get(v_cfg_1131_, 22);
v_readmeFile_1157_ = lean_ctor_get(v_cfg_1131_, 23);
v_reservoir_1158_ = lean_ctor_get_uint8(v_cfg_1131_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1159_ = lean_ctor_get(v_cfg_1131_, 24);
v_restoreAllArtifacts_x3f_1160_ = lean_ctor_get(v_cfg_1131_, 25);
v_libPrefixOnWindows_1161_ = lean_ctor_get_uint8(v_cfg_1131_, sizeof(void*)*28 + 4);
v_allowImportAll_1162_ = lean_ctor_get_uint8(v_cfg_1131_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1163_ = lean_ctor_get(v_cfg_1131_, 26);
v_checks_1164_ = lean_ctor_get(v_cfg_1131_, 27);
v_fixedToolchain_1165_ = lean_ctor_get_uint8(v_cfg_1131_, sizeof(void*)*28 + 6);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_cfg_1131_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v_cfg_1131_, 8);
lean_dec(v_unused_1173_);
v___x_1167_ = v_cfg_1131_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_checks_1164_);
lean_inc(v_builtinLint_x3f_1163_);
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
lean_inc(v_nativeLibDir_1141_);
lean_inc(v_leanLibDir_1140_);
lean_inc(v_buildDir_1139_);
lean_inc(v_srcDir_1138_);
lean_inc(v_moreGlobalServerArgs_1137_);
lean_inc(v_extraDepTargets_1135_);
lean_inc(v_toLeanConfig_1133_);
lean_inc(v_toWorkspaceConfig_1132_);
lean_dec(v_cfg_1131_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 8, v_val_1130_);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_toWorkspaceConfig_1132_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_toLeanConfig_1133_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_extraDepTargets_1135_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v_moreGlobalServerArgs_1137_);
lean_ctor_set(v_reuseFailAlloc_1171_, 4, v_srcDir_1138_);
lean_ctor_set(v_reuseFailAlloc_1171_, 5, v_buildDir_1139_);
lean_ctor_set(v_reuseFailAlloc_1171_, 6, v_leanLibDir_1140_);
lean_ctor_set(v_reuseFailAlloc_1171_, 7, v_nativeLibDir_1141_);
lean_ctor_set(v_reuseFailAlloc_1171_, 8, v_val_1130_);
lean_ctor_set(v_reuseFailAlloc_1171_, 9, v_irDir_1142_);
lean_ctor_set(v_reuseFailAlloc_1171_, 10, v_releaseRepo_1143_);
lean_ctor_set(v_reuseFailAlloc_1171_, 11, v_buildArchive_1144_);
lean_ctor_set(v_reuseFailAlloc_1171_, 12, v_testDriver_1146_);
lean_ctor_set(v_reuseFailAlloc_1171_, 13, v_testDriverArgs_1147_);
lean_ctor_set(v_reuseFailAlloc_1171_, 14, v_lintDriver_1148_);
lean_ctor_set(v_reuseFailAlloc_1171_, 15, v_lintDriverArgs_1149_);
lean_ctor_set(v_reuseFailAlloc_1171_, 16, v_version_1150_);
lean_ctor_set(v_reuseFailAlloc_1171_, 17, v_versionTags_1151_);
lean_ctor_set(v_reuseFailAlloc_1171_, 18, v_description_1152_);
lean_ctor_set(v_reuseFailAlloc_1171_, 19, v_keywords_1153_);
lean_ctor_set(v_reuseFailAlloc_1171_, 20, v_homepage_1154_);
lean_ctor_set(v_reuseFailAlloc_1171_, 21, v_license_1155_);
lean_ctor_set(v_reuseFailAlloc_1171_, 22, v_licenseFiles_1156_);
lean_ctor_set(v_reuseFailAlloc_1171_, 23, v_readmeFile_1157_);
lean_ctor_set(v_reuseFailAlloc_1171_, 24, v_enableArtifactCache_x3f_1159_);
lean_ctor_set(v_reuseFailAlloc_1171_, 25, v_restoreAllArtifacts_x3f_1160_);
lean_ctor_set(v_reuseFailAlloc_1171_, 26, v_builtinLint_x3f_1163_);
lean_ctor_set(v_reuseFailAlloc_1171_, 27, v_checks_1164_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*28, v_bootstrap_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*28 + 1, v_precompileModules_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1145_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*28 + 3, v_reservoir_1158_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1161_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*28 + 5, v_allowImportAll_1162_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*28 + 6, v_fixedToolchain_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__2(lean_object* v_f_1174_, lean_object* v_cfg_1175_){
_start:
{
lean_object* v_toWorkspaceConfig_1176_; lean_object* v_toLeanConfig_1177_; uint8_t v_bootstrap_1178_; lean_object* v_extraDepTargets_1179_; uint8_t v_precompileModules_1180_; lean_object* v_moreGlobalServerArgs_1181_; lean_object* v_srcDir_1182_; lean_object* v_buildDir_1183_; lean_object* v_leanLibDir_1184_; lean_object* v_nativeLibDir_1185_; lean_object* v_binDir_1186_; lean_object* v_irDir_1187_; lean_object* v_releaseRepo_1188_; lean_object* v_buildArchive_1189_; uint8_t v_preferReleaseBuild_1190_; lean_object* v_testDriver_1191_; lean_object* v_testDriverArgs_1192_; lean_object* v_lintDriver_1193_; lean_object* v_lintDriverArgs_1194_; lean_object* v_version_1195_; lean_object* v_versionTags_1196_; lean_object* v_description_1197_; lean_object* v_keywords_1198_; lean_object* v_homepage_1199_; lean_object* v_license_1200_; lean_object* v_licenseFiles_1201_; lean_object* v_readmeFile_1202_; uint8_t v_reservoir_1203_; lean_object* v_enableArtifactCache_x3f_1204_; lean_object* v_restoreAllArtifacts_x3f_1205_; uint8_t v_libPrefixOnWindows_1206_; uint8_t v_allowImportAll_1207_; lean_object* v_builtinLint_x3f_1208_; lean_object* v_checks_1209_; uint8_t v_fixedToolchain_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1218_; 
v_toWorkspaceConfig_1176_ = lean_ctor_get(v_cfg_1175_, 0);
v_toLeanConfig_1177_ = lean_ctor_get(v_cfg_1175_, 1);
v_bootstrap_1178_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*28);
v_extraDepTargets_1179_ = lean_ctor_get(v_cfg_1175_, 2);
v_precompileModules_1180_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1181_ = lean_ctor_get(v_cfg_1175_, 3);
v_srcDir_1182_ = lean_ctor_get(v_cfg_1175_, 4);
v_buildDir_1183_ = lean_ctor_get(v_cfg_1175_, 5);
v_leanLibDir_1184_ = lean_ctor_get(v_cfg_1175_, 6);
v_nativeLibDir_1185_ = lean_ctor_get(v_cfg_1175_, 7);
v_binDir_1186_ = lean_ctor_get(v_cfg_1175_, 8);
v_irDir_1187_ = lean_ctor_get(v_cfg_1175_, 9);
v_releaseRepo_1188_ = lean_ctor_get(v_cfg_1175_, 10);
v_buildArchive_1189_ = lean_ctor_get(v_cfg_1175_, 11);
v_preferReleaseBuild_1190_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*28 + 2);
v_testDriver_1191_ = lean_ctor_get(v_cfg_1175_, 12);
v_testDriverArgs_1192_ = lean_ctor_get(v_cfg_1175_, 13);
v_lintDriver_1193_ = lean_ctor_get(v_cfg_1175_, 14);
v_lintDriverArgs_1194_ = lean_ctor_get(v_cfg_1175_, 15);
v_version_1195_ = lean_ctor_get(v_cfg_1175_, 16);
v_versionTags_1196_ = lean_ctor_get(v_cfg_1175_, 17);
v_description_1197_ = lean_ctor_get(v_cfg_1175_, 18);
v_keywords_1198_ = lean_ctor_get(v_cfg_1175_, 19);
v_homepage_1199_ = lean_ctor_get(v_cfg_1175_, 20);
v_license_1200_ = lean_ctor_get(v_cfg_1175_, 21);
v_licenseFiles_1201_ = lean_ctor_get(v_cfg_1175_, 22);
v_readmeFile_1202_ = lean_ctor_get(v_cfg_1175_, 23);
v_reservoir_1203_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1204_ = lean_ctor_get(v_cfg_1175_, 24);
v_restoreAllArtifacts_x3f_1205_ = lean_ctor_get(v_cfg_1175_, 25);
v_libPrefixOnWindows_1206_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*28 + 4);
v_allowImportAll_1207_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1208_ = lean_ctor_get(v_cfg_1175_, 26);
v_checks_1209_ = lean_ctor_get(v_cfg_1175_, 27);
v_fixedToolchain_1210_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*28 + 6);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_cfg_1175_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1212_ = v_cfg_1175_;
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_checks_1209_);
lean_inc(v_builtinLint_x3f_1208_);
lean_inc(v_restoreAllArtifacts_x3f_1205_);
lean_inc(v_enableArtifactCache_x3f_1204_);
lean_inc(v_readmeFile_1202_);
lean_inc(v_licenseFiles_1201_);
lean_inc(v_license_1200_);
lean_inc(v_homepage_1199_);
lean_inc(v_keywords_1198_);
lean_inc(v_description_1197_);
lean_inc(v_versionTags_1196_);
lean_inc(v_version_1195_);
lean_inc(v_lintDriverArgs_1194_);
lean_inc(v_lintDriver_1193_);
lean_inc(v_testDriverArgs_1192_);
lean_inc(v_testDriver_1191_);
lean_inc(v_buildArchive_1189_);
lean_inc(v_releaseRepo_1188_);
lean_inc(v_irDir_1187_);
lean_inc(v_binDir_1186_);
lean_inc(v_nativeLibDir_1185_);
lean_inc(v_leanLibDir_1184_);
lean_inc(v_buildDir_1183_);
lean_inc(v_srcDir_1182_);
lean_inc(v_moreGlobalServerArgs_1181_);
lean_inc(v_extraDepTargets_1179_);
lean_inc(v_toLeanConfig_1177_);
lean_inc(v_toWorkspaceConfig_1176_);
lean_dec(v_cfg_1175_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = lean_apply_1(v_f_1174_, v_binDir_1186_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 8, v___x_1214_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_toWorkspaceConfig_1176_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_toLeanConfig_1177_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_extraDepTargets_1179_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_moreGlobalServerArgs_1181_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v_srcDir_1182_);
lean_ctor_set(v_reuseFailAlloc_1217_, 5, v_buildDir_1183_);
lean_ctor_set(v_reuseFailAlloc_1217_, 6, v_leanLibDir_1184_);
lean_ctor_set(v_reuseFailAlloc_1217_, 7, v_nativeLibDir_1185_);
lean_ctor_set(v_reuseFailAlloc_1217_, 8, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1217_, 9, v_irDir_1187_);
lean_ctor_set(v_reuseFailAlloc_1217_, 10, v_releaseRepo_1188_);
lean_ctor_set(v_reuseFailAlloc_1217_, 11, v_buildArchive_1189_);
lean_ctor_set(v_reuseFailAlloc_1217_, 12, v_testDriver_1191_);
lean_ctor_set(v_reuseFailAlloc_1217_, 13, v_testDriverArgs_1192_);
lean_ctor_set(v_reuseFailAlloc_1217_, 14, v_lintDriver_1193_);
lean_ctor_set(v_reuseFailAlloc_1217_, 15, v_lintDriverArgs_1194_);
lean_ctor_set(v_reuseFailAlloc_1217_, 16, v_version_1195_);
lean_ctor_set(v_reuseFailAlloc_1217_, 17, v_versionTags_1196_);
lean_ctor_set(v_reuseFailAlloc_1217_, 18, v_description_1197_);
lean_ctor_set(v_reuseFailAlloc_1217_, 19, v_keywords_1198_);
lean_ctor_set(v_reuseFailAlloc_1217_, 20, v_homepage_1199_);
lean_ctor_set(v_reuseFailAlloc_1217_, 21, v_license_1200_);
lean_ctor_set(v_reuseFailAlloc_1217_, 22, v_licenseFiles_1201_);
lean_ctor_set(v_reuseFailAlloc_1217_, 23, v_readmeFile_1202_);
lean_ctor_set(v_reuseFailAlloc_1217_, 24, v_enableArtifactCache_x3f_1204_);
lean_ctor_set(v_reuseFailAlloc_1217_, 25, v_restoreAllArtifacts_x3f_1205_);
lean_ctor_set(v_reuseFailAlloc_1217_, 26, v_builtinLint_x3f_1208_);
lean_ctor_set(v_reuseFailAlloc_1217_, 27, v_checks_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*28, v_bootstrap_1178_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*28 + 1, v_precompileModules_1180_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*28 + 3, v_reservoir_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*28 + 5, v_allowImportAll_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*28 + 6, v_fixedToolchain_1210_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__3(lean_object* v_x_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lake_defaultBinDir;
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__3___boxed(lean_object* v_x_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lake_PackageConfig_binDir___proj___redArg___lam__3(v_x_1221_);
lean_dec_ref(v_x_1221_);
return v_res_1222_;
}
}
lean_object* l_Lake_PackageConfig_binDir___proj___redArg(){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = ((lean_object*)(l_Lake_PackageConfig_binDir___proj___redArg___closed__4));
return v___x_1233_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_binDir___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1234_;
v_res_1234_ = l_Lake_PackageConfig_binDir___proj___redArg();
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___boxed(lean_object* v___dummy_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lake_PackageConfig_binDir___proj___redArg();
return v_res_1236_;
}
}
static lean_object* _init_l_Lake_PackageConfig_binDir___proj___closed__0(void){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lake_PackageConfig_binDir___proj___redArg();
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object* v_p_1238_, lean_object* v_n_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_obj_once(&l_Lake_PackageConfig_binDir___proj___closed__0, &l_Lake_PackageConfig_binDir___proj___closed__0_once, _init_l_Lake_PackageConfig_binDir___proj___closed__0);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object* v_p_1241_, lean_object* v_n_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lake_PackageConfig_binDir___proj(v_p_1241_, v_n_1242_);
lean_dec(v_n_1242_);
lean_dec(v_p_1241_);
return v_res_1243_;
}
}
lean_object* l_Lake_PackageConfig_binDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_obj_once(&l_Lake_PackageConfig_binDir___proj___closed__0, &l_Lake_PackageConfig_binDir___proj___closed__0_once, _init_l_Lake_PackageConfig_binDir___proj___closed__0);
return v___x_1245_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_binDir_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1246_;
v_res_1246_ = l_Lake_PackageConfig_binDir_instConfigField___redArg();
stack->m_obj
 = v_res_1246_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___redArg___boxed(lean_object* v___dummy_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lake_PackageConfig_binDir_instConfigField___redArg();
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object* v_p_1249_, lean_object* v_n_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_obj_once(&l_Lake_PackageConfig_binDir___proj___closed__0, &l_Lake_PackageConfig_binDir___proj___closed__0_once, _init_l_Lake_PackageConfig_binDir___proj___closed__0);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object* v_p_1252_, lean_object* v_n_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lake_PackageConfig_binDir_instConfigField(v_p_1252_, v_n_1253_);
lean_dec(v_n_1253_);
lean_dec(v_p_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__0(lean_object* v_cfg_1255_){
_start:
{
lean_object* v_irDir_1256_; 
v_irDir_1256_ = lean_ctor_get(v_cfg_1255_, 9);
lean_inc_ref(v_irDir_1256_);
return v_irDir_1256_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lake_PackageConfig_irDir___proj___redArg___lam__0(v_cfg_1257_);
lean_dec_ref(v_cfg_1257_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__1(lean_object* v_val_1259_, lean_object* v_cfg_1260_){
_start:
{
lean_object* v_toWorkspaceConfig_1261_; lean_object* v_toLeanConfig_1262_; uint8_t v_bootstrap_1263_; lean_object* v_extraDepTargets_1264_; uint8_t v_precompileModules_1265_; lean_object* v_moreGlobalServerArgs_1266_; lean_object* v_srcDir_1267_; lean_object* v_buildDir_1268_; lean_object* v_leanLibDir_1269_; lean_object* v_nativeLibDir_1270_; lean_object* v_binDir_1271_; lean_object* v_releaseRepo_1272_; lean_object* v_buildArchive_1273_; uint8_t v_preferReleaseBuild_1274_; lean_object* v_testDriver_1275_; lean_object* v_testDriverArgs_1276_; lean_object* v_lintDriver_1277_; lean_object* v_lintDriverArgs_1278_; lean_object* v_version_1279_; lean_object* v_versionTags_1280_; lean_object* v_description_1281_; lean_object* v_keywords_1282_; lean_object* v_homepage_1283_; lean_object* v_license_1284_; lean_object* v_licenseFiles_1285_; lean_object* v_readmeFile_1286_; uint8_t v_reservoir_1287_; lean_object* v_enableArtifactCache_x3f_1288_; lean_object* v_restoreAllArtifacts_x3f_1289_; uint8_t v_libPrefixOnWindows_1290_; uint8_t v_allowImportAll_1291_; lean_object* v_builtinLint_x3f_1292_; lean_object* v_checks_1293_; uint8_t v_fixedToolchain_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_toWorkspaceConfig_1261_ = lean_ctor_get(v_cfg_1260_, 0);
v_toLeanConfig_1262_ = lean_ctor_get(v_cfg_1260_, 1);
v_bootstrap_1263_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*28);
v_extraDepTargets_1264_ = lean_ctor_get(v_cfg_1260_, 2);
v_precompileModules_1265_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1266_ = lean_ctor_get(v_cfg_1260_, 3);
v_srcDir_1267_ = lean_ctor_get(v_cfg_1260_, 4);
v_buildDir_1268_ = lean_ctor_get(v_cfg_1260_, 5);
v_leanLibDir_1269_ = lean_ctor_get(v_cfg_1260_, 6);
v_nativeLibDir_1270_ = lean_ctor_get(v_cfg_1260_, 7);
v_binDir_1271_ = lean_ctor_get(v_cfg_1260_, 8);
v_releaseRepo_1272_ = lean_ctor_get(v_cfg_1260_, 10);
v_buildArchive_1273_ = lean_ctor_get(v_cfg_1260_, 11);
v_preferReleaseBuild_1274_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*28 + 2);
v_testDriver_1275_ = lean_ctor_get(v_cfg_1260_, 12);
v_testDriverArgs_1276_ = lean_ctor_get(v_cfg_1260_, 13);
v_lintDriver_1277_ = lean_ctor_get(v_cfg_1260_, 14);
v_lintDriverArgs_1278_ = lean_ctor_get(v_cfg_1260_, 15);
v_version_1279_ = lean_ctor_get(v_cfg_1260_, 16);
v_versionTags_1280_ = lean_ctor_get(v_cfg_1260_, 17);
v_description_1281_ = lean_ctor_get(v_cfg_1260_, 18);
v_keywords_1282_ = lean_ctor_get(v_cfg_1260_, 19);
v_homepage_1283_ = lean_ctor_get(v_cfg_1260_, 20);
v_license_1284_ = lean_ctor_get(v_cfg_1260_, 21);
v_licenseFiles_1285_ = lean_ctor_get(v_cfg_1260_, 22);
v_readmeFile_1286_ = lean_ctor_get(v_cfg_1260_, 23);
v_reservoir_1287_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1288_ = lean_ctor_get(v_cfg_1260_, 24);
v_restoreAllArtifacts_x3f_1289_ = lean_ctor_get(v_cfg_1260_, 25);
v_libPrefixOnWindows_1290_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*28 + 4);
v_allowImportAll_1291_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1292_ = lean_ctor_get(v_cfg_1260_, 26);
v_checks_1293_ = lean_ctor_get(v_cfg_1260_, 27);
v_fixedToolchain_1294_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*28 + 6);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_cfg_1260_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v_cfg_1260_, 9);
lean_dec(v_unused_1302_);
v___x_1296_ = v_cfg_1260_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_checks_1293_);
lean_inc(v_builtinLint_x3f_1292_);
lean_inc(v_restoreAllArtifacts_x3f_1289_);
lean_inc(v_enableArtifactCache_x3f_1288_);
lean_inc(v_readmeFile_1286_);
lean_inc(v_licenseFiles_1285_);
lean_inc(v_license_1284_);
lean_inc(v_homepage_1283_);
lean_inc(v_keywords_1282_);
lean_inc(v_description_1281_);
lean_inc(v_versionTags_1280_);
lean_inc(v_version_1279_);
lean_inc(v_lintDriverArgs_1278_);
lean_inc(v_lintDriver_1277_);
lean_inc(v_testDriverArgs_1276_);
lean_inc(v_testDriver_1275_);
lean_inc(v_buildArchive_1273_);
lean_inc(v_releaseRepo_1272_);
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
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 9, v_val_1259_);
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_toWorkspaceConfig_1261_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_toLeanConfig_1262_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v_extraDepTargets_1264_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v_moreGlobalServerArgs_1266_);
lean_ctor_set(v_reuseFailAlloc_1300_, 4, v_srcDir_1267_);
lean_ctor_set(v_reuseFailAlloc_1300_, 5, v_buildDir_1268_);
lean_ctor_set(v_reuseFailAlloc_1300_, 6, v_leanLibDir_1269_);
lean_ctor_set(v_reuseFailAlloc_1300_, 7, v_nativeLibDir_1270_);
lean_ctor_set(v_reuseFailAlloc_1300_, 8, v_binDir_1271_);
lean_ctor_set(v_reuseFailAlloc_1300_, 9, v_val_1259_);
lean_ctor_set(v_reuseFailAlloc_1300_, 10, v_releaseRepo_1272_);
lean_ctor_set(v_reuseFailAlloc_1300_, 11, v_buildArchive_1273_);
lean_ctor_set(v_reuseFailAlloc_1300_, 12, v_testDriver_1275_);
lean_ctor_set(v_reuseFailAlloc_1300_, 13, v_testDriverArgs_1276_);
lean_ctor_set(v_reuseFailAlloc_1300_, 14, v_lintDriver_1277_);
lean_ctor_set(v_reuseFailAlloc_1300_, 15, v_lintDriverArgs_1278_);
lean_ctor_set(v_reuseFailAlloc_1300_, 16, v_version_1279_);
lean_ctor_set(v_reuseFailAlloc_1300_, 17, v_versionTags_1280_);
lean_ctor_set(v_reuseFailAlloc_1300_, 18, v_description_1281_);
lean_ctor_set(v_reuseFailAlloc_1300_, 19, v_keywords_1282_);
lean_ctor_set(v_reuseFailAlloc_1300_, 20, v_homepage_1283_);
lean_ctor_set(v_reuseFailAlloc_1300_, 21, v_license_1284_);
lean_ctor_set(v_reuseFailAlloc_1300_, 22, v_licenseFiles_1285_);
lean_ctor_set(v_reuseFailAlloc_1300_, 23, v_readmeFile_1286_);
lean_ctor_set(v_reuseFailAlloc_1300_, 24, v_enableArtifactCache_x3f_1288_);
lean_ctor_set(v_reuseFailAlloc_1300_, 25, v_restoreAllArtifacts_x3f_1289_);
lean_ctor_set(v_reuseFailAlloc_1300_, 26, v_builtinLint_x3f_1292_);
lean_ctor_set(v_reuseFailAlloc_1300_, 27, v_checks_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*28, v_bootstrap_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*28 + 1, v_precompileModules_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*28 + 3, v_reservoir_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*28 + 5, v_allowImportAll_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*28 + 6, v_fixedToolchain_1294_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__2(lean_object* v_f_1303_, lean_object* v_cfg_1304_){
_start:
{
lean_object* v_toWorkspaceConfig_1305_; lean_object* v_toLeanConfig_1306_; uint8_t v_bootstrap_1307_; lean_object* v_extraDepTargets_1308_; uint8_t v_precompileModules_1309_; lean_object* v_moreGlobalServerArgs_1310_; lean_object* v_srcDir_1311_; lean_object* v_buildDir_1312_; lean_object* v_leanLibDir_1313_; lean_object* v_nativeLibDir_1314_; lean_object* v_binDir_1315_; lean_object* v_irDir_1316_; lean_object* v_releaseRepo_1317_; lean_object* v_buildArchive_1318_; uint8_t v_preferReleaseBuild_1319_; lean_object* v_testDriver_1320_; lean_object* v_testDriverArgs_1321_; lean_object* v_lintDriver_1322_; lean_object* v_lintDriverArgs_1323_; lean_object* v_version_1324_; lean_object* v_versionTags_1325_; lean_object* v_description_1326_; lean_object* v_keywords_1327_; lean_object* v_homepage_1328_; lean_object* v_license_1329_; lean_object* v_licenseFiles_1330_; lean_object* v_readmeFile_1331_; uint8_t v_reservoir_1332_; lean_object* v_enableArtifactCache_x3f_1333_; lean_object* v_restoreAllArtifacts_x3f_1334_; uint8_t v_libPrefixOnWindows_1335_; uint8_t v_allowImportAll_1336_; lean_object* v_builtinLint_x3f_1337_; lean_object* v_checks_1338_; uint8_t v_fixedToolchain_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
v_toWorkspaceConfig_1305_ = lean_ctor_get(v_cfg_1304_, 0);
v_toLeanConfig_1306_ = lean_ctor_get(v_cfg_1304_, 1);
v_bootstrap_1307_ = lean_ctor_get_uint8(v_cfg_1304_, sizeof(void*)*28);
v_extraDepTargets_1308_ = lean_ctor_get(v_cfg_1304_, 2);
v_precompileModules_1309_ = lean_ctor_get_uint8(v_cfg_1304_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1310_ = lean_ctor_get(v_cfg_1304_, 3);
v_srcDir_1311_ = lean_ctor_get(v_cfg_1304_, 4);
v_buildDir_1312_ = lean_ctor_get(v_cfg_1304_, 5);
v_leanLibDir_1313_ = lean_ctor_get(v_cfg_1304_, 6);
v_nativeLibDir_1314_ = lean_ctor_get(v_cfg_1304_, 7);
v_binDir_1315_ = lean_ctor_get(v_cfg_1304_, 8);
v_irDir_1316_ = lean_ctor_get(v_cfg_1304_, 9);
v_releaseRepo_1317_ = lean_ctor_get(v_cfg_1304_, 10);
v_buildArchive_1318_ = lean_ctor_get(v_cfg_1304_, 11);
v_preferReleaseBuild_1319_ = lean_ctor_get_uint8(v_cfg_1304_, sizeof(void*)*28 + 2);
v_testDriver_1320_ = lean_ctor_get(v_cfg_1304_, 12);
v_testDriverArgs_1321_ = lean_ctor_get(v_cfg_1304_, 13);
v_lintDriver_1322_ = lean_ctor_get(v_cfg_1304_, 14);
v_lintDriverArgs_1323_ = lean_ctor_get(v_cfg_1304_, 15);
v_version_1324_ = lean_ctor_get(v_cfg_1304_, 16);
v_versionTags_1325_ = lean_ctor_get(v_cfg_1304_, 17);
v_description_1326_ = lean_ctor_get(v_cfg_1304_, 18);
v_keywords_1327_ = lean_ctor_get(v_cfg_1304_, 19);
v_homepage_1328_ = lean_ctor_get(v_cfg_1304_, 20);
v_license_1329_ = lean_ctor_get(v_cfg_1304_, 21);
v_licenseFiles_1330_ = lean_ctor_get(v_cfg_1304_, 22);
v_readmeFile_1331_ = lean_ctor_get(v_cfg_1304_, 23);
v_reservoir_1332_ = lean_ctor_get_uint8(v_cfg_1304_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1333_ = lean_ctor_get(v_cfg_1304_, 24);
v_restoreAllArtifacts_x3f_1334_ = lean_ctor_get(v_cfg_1304_, 25);
v_libPrefixOnWindows_1335_ = lean_ctor_get_uint8(v_cfg_1304_, sizeof(void*)*28 + 4);
v_allowImportAll_1336_ = lean_ctor_get_uint8(v_cfg_1304_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1337_ = lean_ctor_get(v_cfg_1304_, 26);
v_checks_1338_ = lean_ctor_get(v_cfg_1304_, 27);
v_fixedToolchain_1339_ = lean_ctor_get_uint8(v_cfg_1304_, sizeof(void*)*28 + 6);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_cfg_1304_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1341_ = v_cfg_1304_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_checks_1338_);
lean_inc(v_builtinLint_x3f_1337_);
lean_inc(v_restoreAllArtifacts_x3f_1334_);
lean_inc(v_enableArtifactCache_x3f_1333_);
lean_inc(v_readmeFile_1331_);
lean_inc(v_licenseFiles_1330_);
lean_inc(v_license_1329_);
lean_inc(v_homepage_1328_);
lean_inc(v_keywords_1327_);
lean_inc(v_description_1326_);
lean_inc(v_versionTags_1325_);
lean_inc(v_version_1324_);
lean_inc(v_lintDriverArgs_1323_);
lean_inc(v_lintDriver_1322_);
lean_inc(v_testDriverArgs_1321_);
lean_inc(v_testDriver_1320_);
lean_inc(v_buildArchive_1318_);
lean_inc(v_releaseRepo_1317_);
lean_inc(v_irDir_1316_);
lean_inc(v_binDir_1315_);
lean_inc(v_nativeLibDir_1314_);
lean_inc(v_leanLibDir_1313_);
lean_inc(v_buildDir_1312_);
lean_inc(v_srcDir_1311_);
lean_inc(v_moreGlobalServerArgs_1310_);
lean_inc(v_extraDepTargets_1308_);
lean_inc(v_toLeanConfig_1306_);
lean_inc(v_toWorkspaceConfig_1305_);
lean_dec(v_cfg_1304_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = lean_apply_1(v_f_1303_, v_irDir_1316_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 9, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_toWorkspaceConfig_1305_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_toLeanConfig_1306_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_extraDepTargets_1308_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_moreGlobalServerArgs_1310_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_srcDir_1311_);
lean_ctor_set(v_reuseFailAlloc_1346_, 5, v_buildDir_1312_);
lean_ctor_set(v_reuseFailAlloc_1346_, 6, v_leanLibDir_1313_);
lean_ctor_set(v_reuseFailAlloc_1346_, 7, v_nativeLibDir_1314_);
lean_ctor_set(v_reuseFailAlloc_1346_, 8, v_binDir_1315_);
lean_ctor_set(v_reuseFailAlloc_1346_, 9, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1346_, 10, v_releaseRepo_1317_);
lean_ctor_set(v_reuseFailAlloc_1346_, 11, v_buildArchive_1318_);
lean_ctor_set(v_reuseFailAlloc_1346_, 12, v_testDriver_1320_);
lean_ctor_set(v_reuseFailAlloc_1346_, 13, v_testDriverArgs_1321_);
lean_ctor_set(v_reuseFailAlloc_1346_, 14, v_lintDriver_1322_);
lean_ctor_set(v_reuseFailAlloc_1346_, 15, v_lintDriverArgs_1323_);
lean_ctor_set(v_reuseFailAlloc_1346_, 16, v_version_1324_);
lean_ctor_set(v_reuseFailAlloc_1346_, 17, v_versionTags_1325_);
lean_ctor_set(v_reuseFailAlloc_1346_, 18, v_description_1326_);
lean_ctor_set(v_reuseFailAlloc_1346_, 19, v_keywords_1327_);
lean_ctor_set(v_reuseFailAlloc_1346_, 20, v_homepage_1328_);
lean_ctor_set(v_reuseFailAlloc_1346_, 21, v_license_1329_);
lean_ctor_set(v_reuseFailAlloc_1346_, 22, v_licenseFiles_1330_);
lean_ctor_set(v_reuseFailAlloc_1346_, 23, v_readmeFile_1331_);
lean_ctor_set(v_reuseFailAlloc_1346_, 24, v_enableArtifactCache_x3f_1333_);
lean_ctor_set(v_reuseFailAlloc_1346_, 25, v_restoreAllArtifacts_x3f_1334_);
lean_ctor_set(v_reuseFailAlloc_1346_, 26, v_builtinLint_x3f_1337_);
lean_ctor_set(v_reuseFailAlloc_1346_, 27, v_checks_1338_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*28, v_bootstrap_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*28 + 1, v_precompileModules_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*28 + 3, v_reservoir_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1335_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*28 + 5, v_allowImportAll_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*28 + 6, v_fixedToolchain_1339_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__3(lean_object* v_x_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lake_defaultIrDir;
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__3___boxed(lean_object* v_x_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lake_PackageConfig_irDir___proj___redArg___lam__3(v_x_1350_);
lean_dec_ref(v_x_1350_);
return v_res_1351_;
}
}
lean_object* l_Lake_PackageConfig_irDir___proj___redArg(){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = ((lean_object*)(l_Lake_PackageConfig_irDir___proj___redArg___closed__4));
return v___x_1362_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_irDir___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1363_;
v_res_1363_ = l_Lake_PackageConfig_irDir___proj___redArg();
stack->m_obj
 = v_res_1363_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___boxed(lean_object* v___dummy_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lake_PackageConfig_irDir___proj___redArg();
return v_res_1365_;
}
}
static lean_object* _init_l_Lake_PackageConfig_irDir___proj___closed__0(void){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lake_PackageConfig_irDir___proj___redArg();
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object* v_p_1367_, lean_object* v_n_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_obj_once(&l_Lake_PackageConfig_irDir___proj___closed__0, &l_Lake_PackageConfig_irDir___proj___closed__0_once, _init_l_Lake_PackageConfig_irDir___proj___closed__0);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object* v_p_1370_, lean_object* v_n_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lake_PackageConfig_irDir___proj(v_p_1370_, v_n_1371_);
lean_dec(v_n_1371_);
lean_dec(v_p_1370_);
return v_res_1372_;
}
}
lean_object* l_Lake_PackageConfig_irDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_obj_once(&l_Lake_PackageConfig_irDir___proj___closed__0, &l_Lake_PackageConfig_irDir___proj___closed__0_once, _init_l_Lake_PackageConfig_irDir___proj___closed__0);
return v___x_1374_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_irDir_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1375_;
v_res_1375_ = l_Lake_PackageConfig_irDir_instConfigField___redArg();
stack->m_obj
 = v_res_1375_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___redArg___boxed(lean_object* v___dummy_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lake_PackageConfig_irDir_instConfigField___redArg();
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object* v_p_1378_, lean_object* v_n_1379_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_obj_once(&l_Lake_PackageConfig_irDir___proj___closed__0, &l_Lake_PackageConfig_irDir___proj___closed__0_once, _init_l_Lake_PackageConfig_irDir___proj___closed__0);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object* v_p_1381_, lean_object* v_n_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lake_PackageConfig_irDir_instConfigField(v_p_1381_, v_n_1382_);
lean_dec(v_n_1382_);
lean_dec(v_p_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0(lean_object* v_cfg_1384_){
_start:
{
lean_object* v_releaseRepo_1385_; 
v_releaseRepo_1385_ = lean_ctor_get(v_cfg_1384_, 10);
lean_inc(v_releaseRepo_1385_);
return v_releaseRepo_1385_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0___boxed(lean_object* v_cfg_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0(v_cfg_1386_);
lean_dec_ref(v_cfg_1386_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__1(lean_object* v_val_1388_, lean_object* v_cfg_1389_){
_start:
{
lean_object* v_toWorkspaceConfig_1390_; lean_object* v_toLeanConfig_1391_; uint8_t v_bootstrap_1392_; lean_object* v_extraDepTargets_1393_; uint8_t v_precompileModules_1394_; lean_object* v_moreGlobalServerArgs_1395_; lean_object* v_srcDir_1396_; lean_object* v_buildDir_1397_; lean_object* v_leanLibDir_1398_; lean_object* v_nativeLibDir_1399_; lean_object* v_binDir_1400_; lean_object* v_irDir_1401_; lean_object* v_buildArchive_1402_; uint8_t v_preferReleaseBuild_1403_; lean_object* v_testDriver_1404_; lean_object* v_testDriverArgs_1405_; lean_object* v_lintDriver_1406_; lean_object* v_lintDriverArgs_1407_; lean_object* v_version_1408_; lean_object* v_versionTags_1409_; lean_object* v_description_1410_; lean_object* v_keywords_1411_; lean_object* v_homepage_1412_; lean_object* v_license_1413_; lean_object* v_licenseFiles_1414_; lean_object* v_readmeFile_1415_; uint8_t v_reservoir_1416_; lean_object* v_enableArtifactCache_x3f_1417_; lean_object* v_restoreAllArtifacts_x3f_1418_; uint8_t v_libPrefixOnWindows_1419_; uint8_t v_allowImportAll_1420_; lean_object* v_builtinLint_x3f_1421_; lean_object* v_checks_1422_; uint8_t v_fixedToolchain_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
v_toWorkspaceConfig_1390_ = lean_ctor_get(v_cfg_1389_, 0);
v_toLeanConfig_1391_ = lean_ctor_get(v_cfg_1389_, 1);
v_bootstrap_1392_ = lean_ctor_get_uint8(v_cfg_1389_, sizeof(void*)*28);
v_extraDepTargets_1393_ = lean_ctor_get(v_cfg_1389_, 2);
v_precompileModules_1394_ = lean_ctor_get_uint8(v_cfg_1389_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1395_ = lean_ctor_get(v_cfg_1389_, 3);
v_srcDir_1396_ = lean_ctor_get(v_cfg_1389_, 4);
v_buildDir_1397_ = lean_ctor_get(v_cfg_1389_, 5);
v_leanLibDir_1398_ = lean_ctor_get(v_cfg_1389_, 6);
v_nativeLibDir_1399_ = lean_ctor_get(v_cfg_1389_, 7);
v_binDir_1400_ = lean_ctor_get(v_cfg_1389_, 8);
v_irDir_1401_ = lean_ctor_get(v_cfg_1389_, 9);
v_buildArchive_1402_ = lean_ctor_get(v_cfg_1389_, 11);
v_preferReleaseBuild_1403_ = lean_ctor_get_uint8(v_cfg_1389_, sizeof(void*)*28 + 2);
v_testDriver_1404_ = lean_ctor_get(v_cfg_1389_, 12);
v_testDriverArgs_1405_ = lean_ctor_get(v_cfg_1389_, 13);
v_lintDriver_1406_ = lean_ctor_get(v_cfg_1389_, 14);
v_lintDriverArgs_1407_ = lean_ctor_get(v_cfg_1389_, 15);
v_version_1408_ = lean_ctor_get(v_cfg_1389_, 16);
v_versionTags_1409_ = lean_ctor_get(v_cfg_1389_, 17);
v_description_1410_ = lean_ctor_get(v_cfg_1389_, 18);
v_keywords_1411_ = lean_ctor_get(v_cfg_1389_, 19);
v_homepage_1412_ = lean_ctor_get(v_cfg_1389_, 20);
v_license_1413_ = lean_ctor_get(v_cfg_1389_, 21);
v_licenseFiles_1414_ = lean_ctor_get(v_cfg_1389_, 22);
v_readmeFile_1415_ = lean_ctor_get(v_cfg_1389_, 23);
v_reservoir_1416_ = lean_ctor_get_uint8(v_cfg_1389_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1417_ = lean_ctor_get(v_cfg_1389_, 24);
v_restoreAllArtifacts_x3f_1418_ = lean_ctor_get(v_cfg_1389_, 25);
v_libPrefixOnWindows_1419_ = lean_ctor_get_uint8(v_cfg_1389_, sizeof(void*)*28 + 4);
v_allowImportAll_1420_ = lean_ctor_get_uint8(v_cfg_1389_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1421_ = lean_ctor_get(v_cfg_1389_, 26);
v_checks_1422_ = lean_ctor_get(v_cfg_1389_, 27);
v_fixedToolchain_1423_ = lean_ctor_get_uint8(v_cfg_1389_, sizeof(void*)*28 + 6);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_cfg_1389_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v_cfg_1389_, 10);
lean_dec(v_unused_1431_);
v___x_1425_ = v_cfg_1389_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_checks_1422_);
lean_inc(v_builtinLint_x3f_1421_);
lean_inc(v_restoreAllArtifacts_x3f_1418_);
lean_inc(v_enableArtifactCache_x3f_1417_);
lean_inc(v_readmeFile_1415_);
lean_inc(v_licenseFiles_1414_);
lean_inc(v_license_1413_);
lean_inc(v_homepage_1412_);
lean_inc(v_keywords_1411_);
lean_inc(v_description_1410_);
lean_inc(v_versionTags_1409_);
lean_inc(v_version_1408_);
lean_inc(v_lintDriverArgs_1407_);
lean_inc(v_lintDriver_1406_);
lean_inc(v_testDriverArgs_1405_);
lean_inc(v_testDriver_1404_);
lean_inc(v_buildArchive_1402_);
lean_inc(v_irDir_1401_);
lean_inc(v_binDir_1400_);
lean_inc(v_nativeLibDir_1399_);
lean_inc(v_leanLibDir_1398_);
lean_inc(v_buildDir_1397_);
lean_inc(v_srcDir_1396_);
lean_inc(v_moreGlobalServerArgs_1395_);
lean_inc(v_extraDepTargets_1393_);
lean_inc(v_toLeanConfig_1391_);
lean_inc(v_toWorkspaceConfig_1390_);
lean_dec(v_cfg_1389_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 10, v_val_1388_);
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_toWorkspaceConfig_1390_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_toLeanConfig_1391_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_extraDepTargets_1393_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v_moreGlobalServerArgs_1395_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v_srcDir_1396_);
lean_ctor_set(v_reuseFailAlloc_1429_, 5, v_buildDir_1397_);
lean_ctor_set(v_reuseFailAlloc_1429_, 6, v_leanLibDir_1398_);
lean_ctor_set(v_reuseFailAlloc_1429_, 7, v_nativeLibDir_1399_);
lean_ctor_set(v_reuseFailAlloc_1429_, 8, v_binDir_1400_);
lean_ctor_set(v_reuseFailAlloc_1429_, 9, v_irDir_1401_);
lean_ctor_set(v_reuseFailAlloc_1429_, 10, v_val_1388_);
lean_ctor_set(v_reuseFailAlloc_1429_, 11, v_buildArchive_1402_);
lean_ctor_set(v_reuseFailAlloc_1429_, 12, v_testDriver_1404_);
lean_ctor_set(v_reuseFailAlloc_1429_, 13, v_testDriverArgs_1405_);
lean_ctor_set(v_reuseFailAlloc_1429_, 14, v_lintDriver_1406_);
lean_ctor_set(v_reuseFailAlloc_1429_, 15, v_lintDriverArgs_1407_);
lean_ctor_set(v_reuseFailAlloc_1429_, 16, v_version_1408_);
lean_ctor_set(v_reuseFailAlloc_1429_, 17, v_versionTags_1409_);
lean_ctor_set(v_reuseFailAlloc_1429_, 18, v_description_1410_);
lean_ctor_set(v_reuseFailAlloc_1429_, 19, v_keywords_1411_);
lean_ctor_set(v_reuseFailAlloc_1429_, 20, v_homepage_1412_);
lean_ctor_set(v_reuseFailAlloc_1429_, 21, v_license_1413_);
lean_ctor_set(v_reuseFailAlloc_1429_, 22, v_licenseFiles_1414_);
lean_ctor_set(v_reuseFailAlloc_1429_, 23, v_readmeFile_1415_);
lean_ctor_set(v_reuseFailAlloc_1429_, 24, v_enableArtifactCache_x3f_1417_);
lean_ctor_set(v_reuseFailAlloc_1429_, 25, v_restoreAllArtifacts_x3f_1418_);
lean_ctor_set(v_reuseFailAlloc_1429_, 26, v_builtinLint_x3f_1421_);
lean_ctor_set(v_reuseFailAlloc_1429_, 27, v_checks_1422_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*28, v_bootstrap_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*28 + 1, v_precompileModules_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1403_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*28 + 3, v_reservoir_1416_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*28 + 5, v_allowImportAll_1420_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*28 + 6, v_fixedToolchain_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__2(lean_object* v_f_1432_, lean_object* v_cfg_1433_){
_start:
{
lean_object* v_toWorkspaceConfig_1434_; lean_object* v_toLeanConfig_1435_; uint8_t v_bootstrap_1436_; lean_object* v_extraDepTargets_1437_; uint8_t v_precompileModules_1438_; lean_object* v_moreGlobalServerArgs_1439_; lean_object* v_srcDir_1440_; lean_object* v_buildDir_1441_; lean_object* v_leanLibDir_1442_; lean_object* v_nativeLibDir_1443_; lean_object* v_binDir_1444_; lean_object* v_irDir_1445_; lean_object* v_releaseRepo_1446_; lean_object* v_buildArchive_1447_; uint8_t v_preferReleaseBuild_1448_; lean_object* v_testDriver_1449_; lean_object* v_testDriverArgs_1450_; lean_object* v_lintDriver_1451_; lean_object* v_lintDriverArgs_1452_; lean_object* v_version_1453_; lean_object* v_versionTags_1454_; lean_object* v_description_1455_; lean_object* v_keywords_1456_; lean_object* v_homepage_1457_; lean_object* v_license_1458_; lean_object* v_licenseFiles_1459_; lean_object* v_readmeFile_1460_; uint8_t v_reservoir_1461_; lean_object* v_enableArtifactCache_x3f_1462_; lean_object* v_restoreAllArtifacts_x3f_1463_; uint8_t v_libPrefixOnWindows_1464_; uint8_t v_allowImportAll_1465_; lean_object* v_builtinLint_x3f_1466_; lean_object* v_checks_1467_; uint8_t v_fixedToolchain_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
v_toWorkspaceConfig_1434_ = lean_ctor_get(v_cfg_1433_, 0);
v_toLeanConfig_1435_ = lean_ctor_get(v_cfg_1433_, 1);
v_bootstrap_1436_ = lean_ctor_get_uint8(v_cfg_1433_, sizeof(void*)*28);
v_extraDepTargets_1437_ = lean_ctor_get(v_cfg_1433_, 2);
v_precompileModules_1438_ = lean_ctor_get_uint8(v_cfg_1433_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1439_ = lean_ctor_get(v_cfg_1433_, 3);
v_srcDir_1440_ = lean_ctor_get(v_cfg_1433_, 4);
v_buildDir_1441_ = lean_ctor_get(v_cfg_1433_, 5);
v_leanLibDir_1442_ = lean_ctor_get(v_cfg_1433_, 6);
v_nativeLibDir_1443_ = lean_ctor_get(v_cfg_1433_, 7);
v_binDir_1444_ = lean_ctor_get(v_cfg_1433_, 8);
v_irDir_1445_ = lean_ctor_get(v_cfg_1433_, 9);
v_releaseRepo_1446_ = lean_ctor_get(v_cfg_1433_, 10);
v_buildArchive_1447_ = lean_ctor_get(v_cfg_1433_, 11);
v_preferReleaseBuild_1448_ = lean_ctor_get_uint8(v_cfg_1433_, sizeof(void*)*28 + 2);
v_testDriver_1449_ = lean_ctor_get(v_cfg_1433_, 12);
v_testDriverArgs_1450_ = lean_ctor_get(v_cfg_1433_, 13);
v_lintDriver_1451_ = lean_ctor_get(v_cfg_1433_, 14);
v_lintDriverArgs_1452_ = lean_ctor_get(v_cfg_1433_, 15);
v_version_1453_ = lean_ctor_get(v_cfg_1433_, 16);
v_versionTags_1454_ = lean_ctor_get(v_cfg_1433_, 17);
v_description_1455_ = lean_ctor_get(v_cfg_1433_, 18);
v_keywords_1456_ = lean_ctor_get(v_cfg_1433_, 19);
v_homepage_1457_ = lean_ctor_get(v_cfg_1433_, 20);
v_license_1458_ = lean_ctor_get(v_cfg_1433_, 21);
v_licenseFiles_1459_ = lean_ctor_get(v_cfg_1433_, 22);
v_readmeFile_1460_ = lean_ctor_get(v_cfg_1433_, 23);
v_reservoir_1461_ = lean_ctor_get_uint8(v_cfg_1433_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1462_ = lean_ctor_get(v_cfg_1433_, 24);
v_restoreAllArtifacts_x3f_1463_ = lean_ctor_get(v_cfg_1433_, 25);
v_libPrefixOnWindows_1464_ = lean_ctor_get_uint8(v_cfg_1433_, sizeof(void*)*28 + 4);
v_allowImportAll_1465_ = lean_ctor_get_uint8(v_cfg_1433_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1466_ = lean_ctor_get(v_cfg_1433_, 26);
v_checks_1467_ = lean_ctor_get(v_cfg_1433_, 27);
v_fixedToolchain_1468_ = lean_ctor_get_uint8(v_cfg_1433_, sizeof(void*)*28 + 6);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_cfg_1433_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1470_ = v_cfg_1433_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_checks_1467_);
lean_inc(v_builtinLint_x3f_1466_);
lean_inc(v_restoreAllArtifacts_x3f_1463_);
lean_inc(v_enableArtifactCache_x3f_1462_);
lean_inc(v_readmeFile_1460_);
lean_inc(v_licenseFiles_1459_);
lean_inc(v_license_1458_);
lean_inc(v_homepage_1457_);
lean_inc(v_keywords_1456_);
lean_inc(v_description_1455_);
lean_inc(v_versionTags_1454_);
lean_inc(v_version_1453_);
lean_inc(v_lintDriverArgs_1452_);
lean_inc(v_lintDriver_1451_);
lean_inc(v_testDriverArgs_1450_);
lean_inc(v_testDriver_1449_);
lean_inc(v_buildArchive_1447_);
lean_inc(v_releaseRepo_1446_);
lean_inc(v_irDir_1445_);
lean_inc(v_binDir_1444_);
lean_inc(v_nativeLibDir_1443_);
lean_inc(v_leanLibDir_1442_);
lean_inc(v_buildDir_1441_);
lean_inc(v_srcDir_1440_);
lean_inc(v_moreGlobalServerArgs_1439_);
lean_inc(v_extraDepTargets_1437_);
lean_inc(v_toLeanConfig_1435_);
lean_inc(v_toWorkspaceConfig_1434_);
lean_dec(v_cfg_1433_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_apply_1(v_f_1432_, v_releaseRepo_1446_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 10, v___x_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_toWorkspaceConfig_1434_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_toLeanConfig_1435_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_extraDepTargets_1437_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_moreGlobalServerArgs_1439_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_srcDir_1440_);
lean_ctor_set(v_reuseFailAlloc_1475_, 5, v_buildDir_1441_);
lean_ctor_set(v_reuseFailAlloc_1475_, 6, v_leanLibDir_1442_);
lean_ctor_set(v_reuseFailAlloc_1475_, 7, v_nativeLibDir_1443_);
lean_ctor_set(v_reuseFailAlloc_1475_, 8, v_binDir_1444_);
lean_ctor_set(v_reuseFailAlloc_1475_, 9, v_irDir_1445_);
lean_ctor_set(v_reuseFailAlloc_1475_, 10, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1475_, 11, v_buildArchive_1447_);
lean_ctor_set(v_reuseFailAlloc_1475_, 12, v_testDriver_1449_);
lean_ctor_set(v_reuseFailAlloc_1475_, 13, v_testDriverArgs_1450_);
lean_ctor_set(v_reuseFailAlloc_1475_, 14, v_lintDriver_1451_);
lean_ctor_set(v_reuseFailAlloc_1475_, 15, v_lintDriverArgs_1452_);
lean_ctor_set(v_reuseFailAlloc_1475_, 16, v_version_1453_);
lean_ctor_set(v_reuseFailAlloc_1475_, 17, v_versionTags_1454_);
lean_ctor_set(v_reuseFailAlloc_1475_, 18, v_description_1455_);
lean_ctor_set(v_reuseFailAlloc_1475_, 19, v_keywords_1456_);
lean_ctor_set(v_reuseFailAlloc_1475_, 20, v_homepage_1457_);
lean_ctor_set(v_reuseFailAlloc_1475_, 21, v_license_1458_);
lean_ctor_set(v_reuseFailAlloc_1475_, 22, v_licenseFiles_1459_);
lean_ctor_set(v_reuseFailAlloc_1475_, 23, v_readmeFile_1460_);
lean_ctor_set(v_reuseFailAlloc_1475_, 24, v_enableArtifactCache_x3f_1462_);
lean_ctor_set(v_reuseFailAlloc_1475_, 25, v_restoreAllArtifacts_x3f_1463_);
lean_ctor_set(v_reuseFailAlloc_1475_, 26, v_builtinLint_x3f_1466_);
lean_ctor_set(v_reuseFailAlloc_1475_, 27, v_checks_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*28, v_bootstrap_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*28 + 1, v_precompileModules_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*28 + 3, v_reservoir_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1464_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*28 + 5, v_allowImportAll_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*28 + 6, v_fixedToolchain_1468_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3(lean_object* v_x_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_box(0);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3___boxed(lean_object* v_x_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3(v_x_1479_);
lean_dec_ref(v_x_1479_);
return v_res_1480_;
}
}
lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg(){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = ((lean_object*)(l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__4));
return v___x_1491_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_releaseRepo___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1492_;
v_res_1492_ = l_Lake_PackageConfig_releaseRepo___proj___redArg();
stack->m_obj
 = v_res_1492_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___boxed(lean_object* v___dummy_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lake_PackageConfig_releaseRepo___proj___redArg();
return v_res_1494_;
}
}
static lean_object* _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0(void){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lake_PackageConfig_releaseRepo___proj___redArg();
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object* v_p_1496_, lean_object* v_n_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object* v_p_1499_, lean_object* v_n_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1499_, v_n_1500_);
lean_dec(v_n_1500_);
lean_dec(v_p_1499_);
return v_res_1501_;
}
}
lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___redArg(){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1503_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_releaseRepo_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1504_;
v_res_1504_ = l_Lake_PackageConfig_releaseRepo_instConfigField___redArg();
stack->m_obj
 = v_res_1504_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___redArg___boxed(lean_object* v___dummy_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lake_PackageConfig_releaseRepo_instConfigField___redArg();
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object* v_p_1507_, lean_object* v_n_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object* v_p_1510_, lean_object* v_n_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lake_PackageConfig_releaseRepo_instConfigField(v_p_1510_, v_n_1511_);
lean_dec(v_n_1511_);
lean_dec(v_p_1510_);
return v_res_1512_;
}
}
lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1514_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1515_;
v_res_1515_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg();
stack->m_obj
 = v_res_1515_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg();
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object* v_p_1518_, lean_object* v_n_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object* v_p_1521_, lean_object* v_n_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(v_p_1521_, v_n_1522_);
lean_dec(v_n_1522_);
lean_dec(v_p_1521_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0(lean_object* v_cfg_1524_){
_start:
{
lean_object* v_buildArchive_1525_; 
v_buildArchive_1525_ = lean_ctor_get(v_cfg_1524_, 11);
lean_inc(v_buildArchive_1525_);
return v_buildArchive_1525_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0___boxed(lean_object* v_cfg_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0(v_cfg_1526_);
lean_dec_ref(v_cfg_1526_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__1(lean_object* v_val_1528_, lean_object* v_cfg_1529_){
_start:
{
lean_object* v_toWorkspaceConfig_1530_; lean_object* v_toLeanConfig_1531_; uint8_t v_bootstrap_1532_; lean_object* v_extraDepTargets_1533_; uint8_t v_precompileModules_1534_; lean_object* v_moreGlobalServerArgs_1535_; lean_object* v_srcDir_1536_; lean_object* v_buildDir_1537_; lean_object* v_leanLibDir_1538_; lean_object* v_nativeLibDir_1539_; lean_object* v_binDir_1540_; lean_object* v_irDir_1541_; lean_object* v_releaseRepo_1542_; uint8_t v_preferReleaseBuild_1543_; lean_object* v_testDriver_1544_; lean_object* v_testDriverArgs_1545_; lean_object* v_lintDriver_1546_; lean_object* v_lintDriverArgs_1547_; lean_object* v_version_1548_; lean_object* v_versionTags_1549_; lean_object* v_description_1550_; lean_object* v_keywords_1551_; lean_object* v_homepage_1552_; lean_object* v_license_1553_; lean_object* v_licenseFiles_1554_; lean_object* v_readmeFile_1555_; uint8_t v_reservoir_1556_; lean_object* v_enableArtifactCache_x3f_1557_; lean_object* v_restoreAllArtifacts_x3f_1558_; uint8_t v_libPrefixOnWindows_1559_; uint8_t v_allowImportAll_1560_; lean_object* v_builtinLint_x3f_1561_; lean_object* v_checks_1562_; uint8_t v_fixedToolchain_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
v_toWorkspaceConfig_1530_ = lean_ctor_get(v_cfg_1529_, 0);
v_toLeanConfig_1531_ = lean_ctor_get(v_cfg_1529_, 1);
v_bootstrap_1532_ = lean_ctor_get_uint8(v_cfg_1529_, sizeof(void*)*28);
v_extraDepTargets_1533_ = lean_ctor_get(v_cfg_1529_, 2);
v_precompileModules_1534_ = lean_ctor_get_uint8(v_cfg_1529_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1535_ = lean_ctor_get(v_cfg_1529_, 3);
v_srcDir_1536_ = lean_ctor_get(v_cfg_1529_, 4);
v_buildDir_1537_ = lean_ctor_get(v_cfg_1529_, 5);
v_leanLibDir_1538_ = lean_ctor_get(v_cfg_1529_, 6);
v_nativeLibDir_1539_ = lean_ctor_get(v_cfg_1529_, 7);
v_binDir_1540_ = lean_ctor_get(v_cfg_1529_, 8);
v_irDir_1541_ = lean_ctor_get(v_cfg_1529_, 9);
v_releaseRepo_1542_ = lean_ctor_get(v_cfg_1529_, 10);
v_preferReleaseBuild_1543_ = lean_ctor_get_uint8(v_cfg_1529_, sizeof(void*)*28 + 2);
v_testDriver_1544_ = lean_ctor_get(v_cfg_1529_, 12);
v_testDriverArgs_1545_ = lean_ctor_get(v_cfg_1529_, 13);
v_lintDriver_1546_ = lean_ctor_get(v_cfg_1529_, 14);
v_lintDriverArgs_1547_ = lean_ctor_get(v_cfg_1529_, 15);
v_version_1548_ = lean_ctor_get(v_cfg_1529_, 16);
v_versionTags_1549_ = lean_ctor_get(v_cfg_1529_, 17);
v_description_1550_ = lean_ctor_get(v_cfg_1529_, 18);
v_keywords_1551_ = lean_ctor_get(v_cfg_1529_, 19);
v_homepage_1552_ = lean_ctor_get(v_cfg_1529_, 20);
v_license_1553_ = lean_ctor_get(v_cfg_1529_, 21);
v_licenseFiles_1554_ = lean_ctor_get(v_cfg_1529_, 22);
v_readmeFile_1555_ = lean_ctor_get(v_cfg_1529_, 23);
v_reservoir_1556_ = lean_ctor_get_uint8(v_cfg_1529_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1557_ = lean_ctor_get(v_cfg_1529_, 24);
v_restoreAllArtifacts_x3f_1558_ = lean_ctor_get(v_cfg_1529_, 25);
v_libPrefixOnWindows_1559_ = lean_ctor_get_uint8(v_cfg_1529_, sizeof(void*)*28 + 4);
v_allowImportAll_1560_ = lean_ctor_get_uint8(v_cfg_1529_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1561_ = lean_ctor_get(v_cfg_1529_, 26);
v_checks_1562_ = lean_ctor_get(v_cfg_1529_, 27);
v_fixedToolchain_1563_ = lean_ctor_get_uint8(v_cfg_1529_, sizeof(void*)*28 + 6);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_cfg_1529_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v_cfg_1529_, 11);
lean_dec(v_unused_1571_);
v___x_1565_ = v_cfg_1529_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_checks_1562_);
lean_inc(v_builtinLint_x3f_1561_);
lean_inc(v_restoreAllArtifacts_x3f_1558_);
lean_inc(v_enableArtifactCache_x3f_1557_);
lean_inc(v_readmeFile_1555_);
lean_inc(v_licenseFiles_1554_);
lean_inc(v_license_1553_);
lean_inc(v_homepage_1552_);
lean_inc(v_keywords_1551_);
lean_inc(v_description_1550_);
lean_inc(v_versionTags_1549_);
lean_inc(v_version_1548_);
lean_inc(v_lintDriverArgs_1547_);
lean_inc(v_lintDriver_1546_);
lean_inc(v_testDriverArgs_1545_);
lean_inc(v_testDriver_1544_);
lean_inc(v_releaseRepo_1542_);
lean_inc(v_irDir_1541_);
lean_inc(v_binDir_1540_);
lean_inc(v_nativeLibDir_1539_);
lean_inc(v_leanLibDir_1538_);
lean_inc(v_buildDir_1537_);
lean_inc(v_srcDir_1536_);
lean_inc(v_moreGlobalServerArgs_1535_);
lean_inc(v_extraDepTargets_1533_);
lean_inc(v_toLeanConfig_1531_);
lean_inc(v_toWorkspaceConfig_1530_);
lean_dec(v_cfg_1529_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 11, v_val_1528_);
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_toWorkspaceConfig_1530_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_toLeanConfig_1531_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_extraDepTargets_1533_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v_moreGlobalServerArgs_1535_);
lean_ctor_set(v_reuseFailAlloc_1569_, 4, v_srcDir_1536_);
lean_ctor_set(v_reuseFailAlloc_1569_, 5, v_buildDir_1537_);
lean_ctor_set(v_reuseFailAlloc_1569_, 6, v_leanLibDir_1538_);
lean_ctor_set(v_reuseFailAlloc_1569_, 7, v_nativeLibDir_1539_);
lean_ctor_set(v_reuseFailAlloc_1569_, 8, v_binDir_1540_);
lean_ctor_set(v_reuseFailAlloc_1569_, 9, v_irDir_1541_);
lean_ctor_set(v_reuseFailAlloc_1569_, 10, v_releaseRepo_1542_);
lean_ctor_set(v_reuseFailAlloc_1569_, 11, v_val_1528_);
lean_ctor_set(v_reuseFailAlloc_1569_, 12, v_testDriver_1544_);
lean_ctor_set(v_reuseFailAlloc_1569_, 13, v_testDriverArgs_1545_);
lean_ctor_set(v_reuseFailAlloc_1569_, 14, v_lintDriver_1546_);
lean_ctor_set(v_reuseFailAlloc_1569_, 15, v_lintDriverArgs_1547_);
lean_ctor_set(v_reuseFailAlloc_1569_, 16, v_version_1548_);
lean_ctor_set(v_reuseFailAlloc_1569_, 17, v_versionTags_1549_);
lean_ctor_set(v_reuseFailAlloc_1569_, 18, v_description_1550_);
lean_ctor_set(v_reuseFailAlloc_1569_, 19, v_keywords_1551_);
lean_ctor_set(v_reuseFailAlloc_1569_, 20, v_homepage_1552_);
lean_ctor_set(v_reuseFailAlloc_1569_, 21, v_license_1553_);
lean_ctor_set(v_reuseFailAlloc_1569_, 22, v_licenseFiles_1554_);
lean_ctor_set(v_reuseFailAlloc_1569_, 23, v_readmeFile_1555_);
lean_ctor_set(v_reuseFailAlloc_1569_, 24, v_enableArtifactCache_x3f_1557_);
lean_ctor_set(v_reuseFailAlloc_1569_, 25, v_restoreAllArtifacts_x3f_1558_);
lean_ctor_set(v_reuseFailAlloc_1569_, 26, v_builtinLint_x3f_1561_);
lean_ctor_set(v_reuseFailAlloc_1569_, 27, v_checks_1562_);
lean_ctor_set_uint8(v_reuseFailAlloc_1569_, sizeof(void*)*28, v_bootstrap_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1569_, sizeof(void*)*28 + 1, v_precompileModules_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1569_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1543_);
lean_ctor_set_uint8(v_reuseFailAlloc_1569_, sizeof(void*)*28 + 3, v_reservoir_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1569_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1569_, sizeof(void*)*28 + 5, v_allowImportAll_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1569_, sizeof(void*)*28 + 6, v_fixedToolchain_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__2(lean_object* v_f_1572_, lean_object* v_cfg_1573_){
_start:
{
lean_object* v_toWorkspaceConfig_1574_; lean_object* v_toLeanConfig_1575_; uint8_t v_bootstrap_1576_; lean_object* v_extraDepTargets_1577_; uint8_t v_precompileModules_1578_; lean_object* v_moreGlobalServerArgs_1579_; lean_object* v_srcDir_1580_; lean_object* v_buildDir_1581_; lean_object* v_leanLibDir_1582_; lean_object* v_nativeLibDir_1583_; lean_object* v_binDir_1584_; lean_object* v_irDir_1585_; lean_object* v_releaseRepo_1586_; lean_object* v_buildArchive_1587_; uint8_t v_preferReleaseBuild_1588_; lean_object* v_testDriver_1589_; lean_object* v_testDriverArgs_1590_; lean_object* v_lintDriver_1591_; lean_object* v_lintDriverArgs_1592_; lean_object* v_version_1593_; lean_object* v_versionTags_1594_; lean_object* v_description_1595_; lean_object* v_keywords_1596_; lean_object* v_homepage_1597_; lean_object* v_license_1598_; lean_object* v_licenseFiles_1599_; lean_object* v_readmeFile_1600_; uint8_t v_reservoir_1601_; lean_object* v_enableArtifactCache_x3f_1602_; lean_object* v_restoreAllArtifacts_x3f_1603_; uint8_t v_libPrefixOnWindows_1604_; uint8_t v_allowImportAll_1605_; lean_object* v_builtinLint_x3f_1606_; lean_object* v_checks_1607_; uint8_t v_fixedToolchain_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1616_; 
v_toWorkspaceConfig_1574_ = lean_ctor_get(v_cfg_1573_, 0);
v_toLeanConfig_1575_ = lean_ctor_get(v_cfg_1573_, 1);
v_bootstrap_1576_ = lean_ctor_get_uint8(v_cfg_1573_, sizeof(void*)*28);
v_extraDepTargets_1577_ = lean_ctor_get(v_cfg_1573_, 2);
v_precompileModules_1578_ = lean_ctor_get_uint8(v_cfg_1573_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1579_ = lean_ctor_get(v_cfg_1573_, 3);
v_srcDir_1580_ = lean_ctor_get(v_cfg_1573_, 4);
v_buildDir_1581_ = lean_ctor_get(v_cfg_1573_, 5);
v_leanLibDir_1582_ = lean_ctor_get(v_cfg_1573_, 6);
v_nativeLibDir_1583_ = lean_ctor_get(v_cfg_1573_, 7);
v_binDir_1584_ = lean_ctor_get(v_cfg_1573_, 8);
v_irDir_1585_ = lean_ctor_get(v_cfg_1573_, 9);
v_releaseRepo_1586_ = lean_ctor_get(v_cfg_1573_, 10);
v_buildArchive_1587_ = lean_ctor_get(v_cfg_1573_, 11);
v_preferReleaseBuild_1588_ = lean_ctor_get_uint8(v_cfg_1573_, sizeof(void*)*28 + 2);
v_testDriver_1589_ = lean_ctor_get(v_cfg_1573_, 12);
v_testDriverArgs_1590_ = lean_ctor_get(v_cfg_1573_, 13);
v_lintDriver_1591_ = lean_ctor_get(v_cfg_1573_, 14);
v_lintDriverArgs_1592_ = lean_ctor_get(v_cfg_1573_, 15);
v_version_1593_ = lean_ctor_get(v_cfg_1573_, 16);
v_versionTags_1594_ = lean_ctor_get(v_cfg_1573_, 17);
v_description_1595_ = lean_ctor_get(v_cfg_1573_, 18);
v_keywords_1596_ = lean_ctor_get(v_cfg_1573_, 19);
v_homepage_1597_ = lean_ctor_get(v_cfg_1573_, 20);
v_license_1598_ = lean_ctor_get(v_cfg_1573_, 21);
v_licenseFiles_1599_ = lean_ctor_get(v_cfg_1573_, 22);
v_readmeFile_1600_ = lean_ctor_get(v_cfg_1573_, 23);
v_reservoir_1601_ = lean_ctor_get_uint8(v_cfg_1573_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1602_ = lean_ctor_get(v_cfg_1573_, 24);
v_restoreAllArtifacts_x3f_1603_ = lean_ctor_get(v_cfg_1573_, 25);
v_libPrefixOnWindows_1604_ = lean_ctor_get_uint8(v_cfg_1573_, sizeof(void*)*28 + 4);
v_allowImportAll_1605_ = lean_ctor_get_uint8(v_cfg_1573_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1606_ = lean_ctor_get(v_cfg_1573_, 26);
v_checks_1607_ = lean_ctor_get(v_cfg_1573_, 27);
v_fixedToolchain_1608_ = lean_ctor_get_uint8(v_cfg_1573_, sizeof(void*)*28 + 6);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_cfg_1573_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1610_ = v_cfg_1573_;
v_isShared_1611_ = v_isSharedCheck_1616_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_checks_1607_);
lean_inc(v_builtinLint_x3f_1606_);
lean_inc(v_restoreAllArtifacts_x3f_1603_);
lean_inc(v_enableArtifactCache_x3f_1602_);
lean_inc(v_readmeFile_1600_);
lean_inc(v_licenseFiles_1599_);
lean_inc(v_license_1598_);
lean_inc(v_homepage_1597_);
lean_inc(v_keywords_1596_);
lean_inc(v_description_1595_);
lean_inc(v_versionTags_1594_);
lean_inc(v_version_1593_);
lean_inc(v_lintDriverArgs_1592_);
lean_inc(v_lintDriver_1591_);
lean_inc(v_testDriverArgs_1590_);
lean_inc(v_testDriver_1589_);
lean_inc(v_buildArchive_1587_);
lean_inc(v_releaseRepo_1586_);
lean_inc(v_irDir_1585_);
lean_inc(v_binDir_1584_);
lean_inc(v_nativeLibDir_1583_);
lean_inc(v_leanLibDir_1582_);
lean_inc(v_buildDir_1581_);
lean_inc(v_srcDir_1580_);
lean_inc(v_moreGlobalServerArgs_1579_);
lean_inc(v_extraDepTargets_1577_);
lean_inc(v_toLeanConfig_1575_);
lean_inc(v_toWorkspaceConfig_1574_);
lean_dec(v_cfg_1573_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1616_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = lean_apply_1(v_f_1572_, v_buildArchive_1587_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 11, v___x_1612_);
v___x_1614_ = v___x_1610_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_toWorkspaceConfig_1574_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_toLeanConfig_1575_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_extraDepTargets_1577_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_moreGlobalServerArgs_1579_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_srcDir_1580_);
lean_ctor_set(v_reuseFailAlloc_1615_, 5, v_buildDir_1581_);
lean_ctor_set(v_reuseFailAlloc_1615_, 6, v_leanLibDir_1582_);
lean_ctor_set(v_reuseFailAlloc_1615_, 7, v_nativeLibDir_1583_);
lean_ctor_set(v_reuseFailAlloc_1615_, 8, v_binDir_1584_);
lean_ctor_set(v_reuseFailAlloc_1615_, 9, v_irDir_1585_);
lean_ctor_set(v_reuseFailAlloc_1615_, 10, v_releaseRepo_1586_);
lean_ctor_set(v_reuseFailAlloc_1615_, 11, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1615_, 12, v_testDriver_1589_);
lean_ctor_set(v_reuseFailAlloc_1615_, 13, v_testDriverArgs_1590_);
lean_ctor_set(v_reuseFailAlloc_1615_, 14, v_lintDriver_1591_);
lean_ctor_set(v_reuseFailAlloc_1615_, 15, v_lintDriverArgs_1592_);
lean_ctor_set(v_reuseFailAlloc_1615_, 16, v_version_1593_);
lean_ctor_set(v_reuseFailAlloc_1615_, 17, v_versionTags_1594_);
lean_ctor_set(v_reuseFailAlloc_1615_, 18, v_description_1595_);
lean_ctor_set(v_reuseFailAlloc_1615_, 19, v_keywords_1596_);
lean_ctor_set(v_reuseFailAlloc_1615_, 20, v_homepage_1597_);
lean_ctor_set(v_reuseFailAlloc_1615_, 21, v_license_1598_);
lean_ctor_set(v_reuseFailAlloc_1615_, 22, v_licenseFiles_1599_);
lean_ctor_set(v_reuseFailAlloc_1615_, 23, v_readmeFile_1600_);
lean_ctor_set(v_reuseFailAlloc_1615_, 24, v_enableArtifactCache_x3f_1602_);
lean_ctor_set(v_reuseFailAlloc_1615_, 25, v_restoreAllArtifacts_x3f_1603_);
lean_ctor_set(v_reuseFailAlloc_1615_, 26, v_builtinLint_x3f_1606_);
lean_ctor_set(v_reuseFailAlloc_1615_, 27, v_checks_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*28, v_bootstrap_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*28 + 1, v_precompileModules_1578_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1588_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*28 + 3, v_reservoir_1601_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*28 + 5, v_allowImportAll_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*28 + 6, v_fixedToolchain_1608_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg(){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = ((lean_object*)(l_Lake_PackageConfig_buildArchive___proj___redArg___closed__3));
return v___x_1626_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_buildArchive___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1627_;
v_res_1627_ = l_Lake_PackageConfig_buildArchive___proj___redArg();
stack->m_obj
 = v_res_1627_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___boxed(lean_object* v___dummy_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lake_PackageConfig_buildArchive___proj___redArg();
return v_res_1629_;
}
}
static lean_object* _init_l_Lake_PackageConfig_buildArchive___proj___closed__0(void){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lake_PackageConfig_buildArchive___proj___redArg();
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object* v_p_1631_, lean_object* v_n_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object* v_p_1634_, lean_object* v_n_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1634_, v_n_1635_);
lean_dec(v_n_1635_);
lean_dec(v_p_1634_);
return v_res_1636_;
}
}
lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___redArg(){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1638_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_buildArchive_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1639_;
v_res_1639_ = l_Lake_PackageConfig_buildArchive_instConfigField___redArg();
stack->m_obj
 = v_res_1639_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___redArg___boxed(lean_object* v___dummy_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lake_PackageConfig_buildArchive_instConfigField___redArg();
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object* v_p_1642_, lean_object* v_n_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object* v_p_1645_, lean_object* v_n_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lake_PackageConfig_buildArchive_instConfigField(v_p_1645_, v_n_1646_);
lean_dec(v_n_1646_);
lean_dec(v_p_1645_);
return v_res_1647_;
}
}
lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1649_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1650_;
v_res_1650_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg();
stack->m_obj
 = v_res_1650_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg();
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object* v_p_1653_, lean_object* v_n_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object* v_p_1656_, lean_object* v_n_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField(v_p_1656_, v_n_1657_);
lean_dec(v_n_1657_);
lean_dec(v_p_1656_);
return v_res_1658_;
}
}
uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0(lean_object* v_cfg_1659_){
_start:
{
uint8_t v_preferReleaseBuild_1660_; 
v_preferReleaseBuild_1660_ = lean_ctor_get_uint8(v_cfg_1659_, sizeof(void*)*28 + 2);
return v_preferReleaseBuild_1660_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1659_ = stack[0].m_obj;
uint8_t v_res_1661_;
v_res_1661_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0(v_cfg_1659_);
stack->m_num = v_res_1661_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0___boxed(lean_object* v_cfg_1662_){
_start:
{
uint8_t v_res_1663_; lean_object* v_r_1664_; 
v_res_1663_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0(v_cfg_1662_);
lean_dec_ref(v_cfg_1662_);
v_r_1664_ = lean_box(v_res_1663_);
return v_r_1664_;
}
}
lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1(uint8_t v_val_1665_, lean_object* v_cfg_1666_){
_start:
{
lean_object* v_toWorkspaceConfig_1667_; lean_object* v_toLeanConfig_1668_; uint8_t v_bootstrap_1669_; lean_object* v_extraDepTargets_1670_; uint8_t v_precompileModules_1671_; lean_object* v_moreGlobalServerArgs_1672_; lean_object* v_srcDir_1673_; lean_object* v_buildDir_1674_; lean_object* v_leanLibDir_1675_; lean_object* v_nativeLibDir_1676_; lean_object* v_binDir_1677_; lean_object* v_irDir_1678_; lean_object* v_releaseRepo_1679_; lean_object* v_buildArchive_1680_; lean_object* v_testDriver_1681_; lean_object* v_testDriverArgs_1682_; lean_object* v_lintDriver_1683_; lean_object* v_lintDriverArgs_1684_; lean_object* v_version_1685_; lean_object* v_versionTags_1686_; lean_object* v_description_1687_; lean_object* v_keywords_1688_; lean_object* v_homepage_1689_; lean_object* v_license_1690_; lean_object* v_licenseFiles_1691_; lean_object* v_readmeFile_1692_; uint8_t v_reservoir_1693_; lean_object* v_enableArtifactCache_x3f_1694_; lean_object* v_restoreAllArtifacts_x3f_1695_; uint8_t v_libPrefixOnWindows_1696_; uint8_t v_allowImportAll_1697_; lean_object* v_builtinLint_x3f_1698_; lean_object* v_checks_1699_; uint8_t v_fixedToolchain_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_toWorkspaceConfig_1667_ = lean_ctor_get(v_cfg_1666_, 0);
v_toLeanConfig_1668_ = lean_ctor_get(v_cfg_1666_, 1);
v_bootstrap_1669_ = lean_ctor_get_uint8(v_cfg_1666_, sizeof(void*)*28);
v_extraDepTargets_1670_ = lean_ctor_get(v_cfg_1666_, 2);
v_precompileModules_1671_ = lean_ctor_get_uint8(v_cfg_1666_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1672_ = lean_ctor_get(v_cfg_1666_, 3);
v_srcDir_1673_ = lean_ctor_get(v_cfg_1666_, 4);
v_buildDir_1674_ = lean_ctor_get(v_cfg_1666_, 5);
v_leanLibDir_1675_ = lean_ctor_get(v_cfg_1666_, 6);
v_nativeLibDir_1676_ = lean_ctor_get(v_cfg_1666_, 7);
v_binDir_1677_ = lean_ctor_get(v_cfg_1666_, 8);
v_irDir_1678_ = lean_ctor_get(v_cfg_1666_, 9);
v_releaseRepo_1679_ = lean_ctor_get(v_cfg_1666_, 10);
v_buildArchive_1680_ = lean_ctor_get(v_cfg_1666_, 11);
v_testDriver_1681_ = lean_ctor_get(v_cfg_1666_, 12);
v_testDriverArgs_1682_ = lean_ctor_get(v_cfg_1666_, 13);
v_lintDriver_1683_ = lean_ctor_get(v_cfg_1666_, 14);
v_lintDriverArgs_1684_ = lean_ctor_get(v_cfg_1666_, 15);
v_version_1685_ = lean_ctor_get(v_cfg_1666_, 16);
v_versionTags_1686_ = lean_ctor_get(v_cfg_1666_, 17);
v_description_1687_ = lean_ctor_get(v_cfg_1666_, 18);
v_keywords_1688_ = lean_ctor_get(v_cfg_1666_, 19);
v_homepage_1689_ = lean_ctor_get(v_cfg_1666_, 20);
v_license_1690_ = lean_ctor_get(v_cfg_1666_, 21);
v_licenseFiles_1691_ = lean_ctor_get(v_cfg_1666_, 22);
v_readmeFile_1692_ = lean_ctor_get(v_cfg_1666_, 23);
v_reservoir_1693_ = lean_ctor_get_uint8(v_cfg_1666_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1694_ = lean_ctor_get(v_cfg_1666_, 24);
v_restoreAllArtifacts_x3f_1695_ = lean_ctor_get(v_cfg_1666_, 25);
v_libPrefixOnWindows_1696_ = lean_ctor_get_uint8(v_cfg_1666_, sizeof(void*)*28 + 4);
v_allowImportAll_1697_ = lean_ctor_get_uint8(v_cfg_1666_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1698_ = lean_ctor_get(v_cfg_1666_, 26);
v_checks_1699_ = lean_ctor_get(v_cfg_1666_, 27);
v_fixedToolchain_1700_ = lean_ctor_get_uint8(v_cfg_1666_, sizeof(void*)*28 + 6);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_cfg_1666_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v_cfg_1666_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_checks_1699_);
lean_inc(v_builtinLint_x3f_1698_);
lean_inc(v_restoreAllArtifacts_x3f_1695_);
lean_inc(v_enableArtifactCache_x3f_1694_);
lean_inc(v_readmeFile_1692_);
lean_inc(v_licenseFiles_1691_);
lean_inc(v_license_1690_);
lean_inc(v_homepage_1689_);
lean_inc(v_keywords_1688_);
lean_inc(v_description_1687_);
lean_inc(v_versionTags_1686_);
lean_inc(v_version_1685_);
lean_inc(v_lintDriverArgs_1684_);
lean_inc(v_lintDriver_1683_);
lean_inc(v_testDriverArgs_1682_);
lean_inc(v_testDriver_1681_);
lean_inc(v_buildArchive_1680_);
lean_inc(v_releaseRepo_1679_);
lean_inc(v_irDir_1678_);
lean_inc(v_binDir_1677_);
lean_inc(v_nativeLibDir_1676_);
lean_inc(v_leanLibDir_1675_);
lean_inc(v_buildDir_1674_);
lean_inc(v_srcDir_1673_);
lean_inc(v_moreGlobalServerArgs_1672_);
lean_inc(v_extraDepTargets_1670_);
lean_inc(v_toLeanConfig_1668_);
lean_inc(v_toWorkspaceConfig_1667_);
lean_dec(v_cfg_1666_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_toWorkspaceConfig_1667_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_toLeanConfig_1668_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_extraDepTargets_1670_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_moreGlobalServerArgs_1672_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v_srcDir_1673_);
lean_ctor_set(v_reuseFailAlloc_1706_, 5, v_buildDir_1674_);
lean_ctor_set(v_reuseFailAlloc_1706_, 6, v_leanLibDir_1675_);
lean_ctor_set(v_reuseFailAlloc_1706_, 7, v_nativeLibDir_1676_);
lean_ctor_set(v_reuseFailAlloc_1706_, 8, v_binDir_1677_);
lean_ctor_set(v_reuseFailAlloc_1706_, 9, v_irDir_1678_);
lean_ctor_set(v_reuseFailAlloc_1706_, 10, v_releaseRepo_1679_);
lean_ctor_set(v_reuseFailAlloc_1706_, 11, v_buildArchive_1680_);
lean_ctor_set(v_reuseFailAlloc_1706_, 12, v_testDriver_1681_);
lean_ctor_set(v_reuseFailAlloc_1706_, 13, v_testDriverArgs_1682_);
lean_ctor_set(v_reuseFailAlloc_1706_, 14, v_lintDriver_1683_);
lean_ctor_set(v_reuseFailAlloc_1706_, 15, v_lintDriverArgs_1684_);
lean_ctor_set(v_reuseFailAlloc_1706_, 16, v_version_1685_);
lean_ctor_set(v_reuseFailAlloc_1706_, 17, v_versionTags_1686_);
lean_ctor_set(v_reuseFailAlloc_1706_, 18, v_description_1687_);
lean_ctor_set(v_reuseFailAlloc_1706_, 19, v_keywords_1688_);
lean_ctor_set(v_reuseFailAlloc_1706_, 20, v_homepage_1689_);
lean_ctor_set(v_reuseFailAlloc_1706_, 21, v_license_1690_);
lean_ctor_set(v_reuseFailAlloc_1706_, 22, v_licenseFiles_1691_);
lean_ctor_set(v_reuseFailAlloc_1706_, 23, v_readmeFile_1692_);
lean_ctor_set(v_reuseFailAlloc_1706_, 24, v_enableArtifactCache_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1706_, 25, v_restoreAllArtifacts_x3f_1695_);
lean_ctor_set(v_reuseFailAlloc_1706_, 26, v_builtinLint_x3f_1698_);
lean_ctor_set(v_reuseFailAlloc_1706_, 27, v_checks_1699_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28, v_bootstrap_1669_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28 + 1, v_precompileModules_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28 + 3, v_reservoir_1693_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1696_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28 + 5, v_allowImportAll_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28 + 6, v_fixedToolchain_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*28 + 2, v_val_1665_);
return v___x_1705_;
}
}
}
}
LEAN_EXPORT void l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_1665_ = stack[0].m_num;
lean_object* v_cfg_1666_ = stack[1].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1(v_val_1665_, v_cfg_1666_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1___boxed(lean_object* v_val_1709_, lean_object* v_cfg_1710_){
_start:
{
uint8_t v_val_143__boxed_1711_; lean_object* v_res_1712_; 
v_val_143__boxed_1711_ = lean_unbox(v_val_1709_);
v_res_1712_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1(v_val_143__boxed_1711_, v_cfg_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__2(lean_object* v_f_1713_, lean_object* v_cfg_1714_){
_start:
{
lean_object* v_toWorkspaceConfig_1715_; lean_object* v_toLeanConfig_1716_; uint8_t v_bootstrap_1717_; lean_object* v_extraDepTargets_1718_; uint8_t v_precompileModules_1719_; lean_object* v_moreGlobalServerArgs_1720_; lean_object* v_srcDir_1721_; lean_object* v_buildDir_1722_; lean_object* v_leanLibDir_1723_; lean_object* v_nativeLibDir_1724_; lean_object* v_binDir_1725_; lean_object* v_irDir_1726_; lean_object* v_releaseRepo_1727_; lean_object* v_buildArchive_1728_; uint8_t v_preferReleaseBuild_1729_; lean_object* v_testDriver_1730_; lean_object* v_testDriverArgs_1731_; lean_object* v_lintDriver_1732_; lean_object* v_lintDriverArgs_1733_; lean_object* v_version_1734_; lean_object* v_versionTags_1735_; lean_object* v_description_1736_; lean_object* v_keywords_1737_; lean_object* v_homepage_1738_; lean_object* v_license_1739_; lean_object* v_licenseFiles_1740_; lean_object* v_readmeFile_1741_; uint8_t v_reservoir_1742_; lean_object* v_enableArtifactCache_x3f_1743_; lean_object* v_restoreAllArtifacts_x3f_1744_; uint8_t v_libPrefixOnWindows_1745_; uint8_t v_allowImportAll_1746_; lean_object* v_builtinLint_x3f_1747_; lean_object* v_checks_1748_; uint8_t v_fixedToolchain_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1759_; 
v_toWorkspaceConfig_1715_ = lean_ctor_get(v_cfg_1714_, 0);
v_toLeanConfig_1716_ = lean_ctor_get(v_cfg_1714_, 1);
v_bootstrap_1717_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*28);
v_extraDepTargets_1718_ = lean_ctor_get(v_cfg_1714_, 2);
v_precompileModules_1719_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1720_ = lean_ctor_get(v_cfg_1714_, 3);
v_srcDir_1721_ = lean_ctor_get(v_cfg_1714_, 4);
v_buildDir_1722_ = lean_ctor_get(v_cfg_1714_, 5);
v_leanLibDir_1723_ = lean_ctor_get(v_cfg_1714_, 6);
v_nativeLibDir_1724_ = lean_ctor_get(v_cfg_1714_, 7);
v_binDir_1725_ = lean_ctor_get(v_cfg_1714_, 8);
v_irDir_1726_ = lean_ctor_get(v_cfg_1714_, 9);
v_releaseRepo_1727_ = lean_ctor_get(v_cfg_1714_, 10);
v_buildArchive_1728_ = lean_ctor_get(v_cfg_1714_, 11);
v_preferReleaseBuild_1729_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*28 + 2);
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
v_reservoir_1742_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1743_ = lean_ctor_get(v_cfg_1714_, 24);
v_restoreAllArtifacts_x3f_1744_ = lean_ctor_get(v_cfg_1714_, 25);
v_libPrefixOnWindows_1745_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*28 + 4);
v_allowImportAll_1746_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1747_ = lean_ctor_get(v_cfg_1714_, 26);
v_checks_1748_ = lean_ctor_get(v_cfg_1714_, 27);
v_fixedToolchain_1749_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*28 + 6);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_cfg_1714_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1751_ = v_cfg_1714_;
v_isShared_1752_ = v_isSharedCheck_1759_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_checks_1748_);
lean_inc(v_builtinLint_x3f_1747_);
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
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1759_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1753_ = lean_box(v_preferReleaseBuild_1729_);
v___x_1754_ = lean_apply_1(v_f_1713_, v___x_1753_);
if (v_isShared_1752_ == 0)
{
v___x_1756_ = v___x_1751_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_toWorkspaceConfig_1715_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_toLeanConfig_1716_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_extraDepTargets_1718_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_moreGlobalServerArgs_1720_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_srcDir_1721_);
lean_ctor_set(v_reuseFailAlloc_1758_, 5, v_buildDir_1722_);
lean_ctor_set(v_reuseFailAlloc_1758_, 6, v_leanLibDir_1723_);
lean_ctor_set(v_reuseFailAlloc_1758_, 7, v_nativeLibDir_1724_);
lean_ctor_set(v_reuseFailAlloc_1758_, 8, v_binDir_1725_);
lean_ctor_set(v_reuseFailAlloc_1758_, 9, v_irDir_1726_);
lean_ctor_set(v_reuseFailAlloc_1758_, 10, v_releaseRepo_1727_);
lean_ctor_set(v_reuseFailAlloc_1758_, 11, v_buildArchive_1728_);
lean_ctor_set(v_reuseFailAlloc_1758_, 12, v_testDriver_1730_);
lean_ctor_set(v_reuseFailAlloc_1758_, 13, v_testDriverArgs_1731_);
lean_ctor_set(v_reuseFailAlloc_1758_, 14, v_lintDriver_1732_);
lean_ctor_set(v_reuseFailAlloc_1758_, 15, v_lintDriverArgs_1733_);
lean_ctor_set(v_reuseFailAlloc_1758_, 16, v_version_1734_);
lean_ctor_set(v_reuseFailAlloc_1758_, 17, v_versionTags_1735_);
lean_ctor_set(v_reuseFailAlloc_1758_, 18, v_description_1736_);
lean_ctor_set(v_reuseFailAlloc_1758_, 19, v_keywords_1737_);
lean_ctor_set(v_reuseFailAlloc_1758_, 20, v_homepage_1738_);
lean_ctor_set(v_reuseFailAlloc_1758_, 21, v_license_1739_);
lean_ctor_set(v_reuseFailAlloc_1758_, 22, v_licenseFiles_1740_);
lean_ctor_set(v_reuseFailAlloc_1758_, 23, v_readmeFile_1741_);
lean_ctor_set(v_reuseFailAlloc_1758_, 24, v_enableArtifactCache_x3f_1743_);
lean_ctor_set(v_reuseFailAlloc_1758_, 25, v_restoreAllArtifacts_x3f_1744_);
lean_ctor_set(v_reuseFailAlloc_1758_, 26, v_builtinLint_x3f_1747_);
lean_ctor_set(v_reuseFailAlloc_1758_, 27, v_checks_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1758_, sizeof(void*)*28, v_bootstrap_1717_);
lean_ctor_set_uint8(v_reuseFailAlloc_1758_, sizeof(void*)*28 + 1, v_precompileModules_1719_);
v___x_1756_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_unbox(v___x_1754_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*28 + 2, v___x_1757_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*28 + 3, v_reservoir_1742_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1745_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*28 + 5, v_allowImportAll_1746_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*28 + 6, v_fixedToolchain_1749_);
return v___x_1756_;
}
}
}
}
lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg(){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = ((lean_object*)(l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__3));
return v___x_1769_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_preferReleaseBuild___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1770_;
v_res_1770_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg();
stack->m_obj
 = v_res_1770_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___boxed(lean_object* v___dummy_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg();
return v_res_1772_;
}
}
static lean_object* _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0(void){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg();
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object* v_p_1774_, lean_object* v_n_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_obj_once(&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0, &l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_once, _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object* v_p_1777_, lean_object* v_n_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1777_, v_n_1778_);
lean_dec(v_n_1778_);
lean_dec(v_p_1777_);
return v_res_1779_;
}
}
lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg(){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_obj_once(&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0, &l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_once, _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0);
return v___x_1781_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1782_;
v_res_1782_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg();
stack->m_obj
 = v_res_1782_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg___boxed(lean_object* v___dummy_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg();
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object* v_p_1785_, lean_object* v_n_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_obj_once(&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0, &l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_once, _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object* v_p_1788_, lean_object* v_n_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField(v_p_1788_, v_n_1789_);
lean_dec(v_n_1789_);
lean_dec(v_p_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__0(lean_object* v_cfg_1791_){
_start:
{
lean_object* v_testDriver_1792_; 
v_testDriver_1792_ = lean_ctor_get(v_cfg_1791_, 12);
lean_inc_ref(v_testDriver_1792_);
return v_testDriver_1792_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__0___boxed(lean_object* v_cfg_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lake_PackageConfig_testDriver___proj___redArg___lam__0(v_cfg_1793_);
lean_dec_ref(v_cfg_1793_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__1(lean_object* v_val_1795_, lean_object* v_cfg_1796_){
_start:
{
lean_object* v_toWorkspaceConfig_1797_; lean_object* v_toLeanConfig_1798_; uint8_t v_bootstrap_1799_; lean_object* v_extraDepTargets_1800_; uint8_t v_precompileModules_1801_; lean_object* v_moreGlobalServerArgs_1802_; lean_object* v_srcDir_1803_; lean_object* v_buildDir_1804_; lean_object* v_leanLibDir_1805_; lean_object* v_nativeLibDir_1806_; lean_object* v_binDir_1807_; lean_object* v_irDir_1808_; lean_object* v_releaseRepo_1809_; lean_object* v_buildArchive_1810_; uint8_t v_preferReleaseBuild_1811_; lean_object* v_testDriverArgs_1812_; lean_object* v_lintDriver_1813_; lean_object* v_lintDriverArgs_1814_; lean_object* v_version_1815_; lean_object* v_versionTags_1816_; lean_object* v_description_1817_; lean_object* v_keywords_1818_; lean_object* v_homepage_1819_; lean_object* v_license_1820_; lean_object* v_licenseFiles_1821_; lean_object* v_readmeFile_1822_; uint8_t v_reservoir_1823_; lean_object* v_enableArtifactCache_x3f_1824_; lean_object* v_restoreAllArtifacts_x3f_1825_; uint8_t v_libPrefixOnWindows_1826_; uint8_t v_allowImportAll_1827_; lean_object* v_builtinLint_x3f_1828_; lean_object* v_checks_1829_; uint8_t v_fixedToolchain_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
v_toWorkspaceConfig_1797_ = lean_ctor_get(v_cfg_1796_, 0);
v_toLeanConfig_1798_ = lean_ctor_get(v_cfg_1796_, 1);
v_bootstrap_1799_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*28);
v_extraDepTargets_1800_ = lean_ctor_get(v_cfg_1796_, 2);
v_precompileModules_1801_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1802_ = lean_ctor_get(v_cfg_1796_, 3);
v_srcDir_1803_ = lean_ctor_get(v_cfg_1796_, 4);
v_buildDir_1804_ = lean_ctor_get(v_cfg_1796_, 5);
v_leanLibDir_1805_ = lean_ctor_get(v_cfg_1796_, 6);
v_nativeLibDir_1806_ = lean_ctor_get(v_cfg_1796_, 7);
v_binDir_1807_ = lean_ctor_get(v_cfg_1796_, 8);
v_irDir_1808_ = lean_ctor_get(v_cfg_1796_, 9);
v_releaseRepo_1809_ = lean_ctor_get(v_cfg_1796_, 10);
v_buildArchive_1810_ = lean_ctor_get(v_cfg_1796_, 11);
v_preferReleaseBuild_1811_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*28 + 2);
v_testDriverArgs_1812_ = lean_ctor_get(v_cfg_1796_, 13);
v_lintDriver_1813_ = lean_ctor_get(v_cfg_1796_, 14);
v_lintDriverArgs_1814_ = lean_ctor_get(v_cfg_1796_, 15);
v_version_1815_ = lean_ctor_get(v_cfg_1796_, 16);
v_versionTags_1816_ = lean_ctor_get(v_cfg_1796_, 17);
v_description_1817_ = lean_ctor_get(v_cfg_1796_, 18);
v_keywords_1818_ = lean_ctor_get(v_cfg_1796_, 19);
v_homepage_1819_ = lean_ctor_get(v_cfg_1796_, 20);
v_license_1820_ = lean_ctor_get(v_cfg_1796_, 21);
v_licenseFiles_1821_ = lean_ctor_get(v_cfg_1796_, 22);
v_readmeFile_1822_ = lean_ctor_get(v_cfg_1796_, 23);
v_reservoir_1823_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1824_ = lean_ctor_get(v_cfg_1796_, 24);
v_restoreAllArtifacts_x3f_1825_ = lean_ctor_get(v_cfg_1796_, 25);
v_libPrefixOnWindows_1826_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*28 + 4);
v_allowImportAll_1827_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1828_ = lean_ctor_get(v_cfg_1796_, 26);
v_checks_1829_ = lean_ctor_get(v_cfg_1796_, 27);
v_fixedToolchain_1830_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*28 + 6);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_cfg_1796_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v_cfg_1796_, 12);
lean_dec(v_unused_1838_);
v___x_1832_ = v_cfg_1796_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_checks_1829_);
lean_inc(v_builtinLint_x3f_1828_);
lean_inc(v_restoreAllArtifacts_x3f_1825_);
lean_inc(v_enableArtifactCache_x3f_1824_);
lean_inc(v_readmeFile_1822_);
lean_inc(v_licenseFiles_1821_);
lean_inc(v_license_1820_);
lean_inc(v_homepage_1819_);
lean_inc(v_keywords_1818_);
lean_inc(v_description_1817_);
lean_inc(v_versionTags_1816_);
lean_inc(v_version_1815_);
lean_inc(v_lintDriverArgs_1814_);
lean_inc(v_lintDriver_1813_);
lean_inc(v_testDriverArgs_1812_);
lean_inc(v_buildArchive_1810_);
lean_inc(v_releaseRepo_1809_);
lean_inc(v_irDir_1808_);
lean_inc(v_binDir_1807_);
lean_inc(v_nativeLibDir_1806_);
lean_inc(v_leanLibDir_1805_);
lean_inc(v_buildDir_1804_);
lean_inc(v_srcDir_1803_);
lean_inc(v_moreGlobalServerArgs_1802_);
lean_inc(v_extraDepTargets_1800_);
lean_inc(v_toLeanConfig_1798_);
lean_inc(v_toWorkspaceConfig_1797_);
lean_dec(v_cfg_1796_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 12, v_val_1795_);
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_toWorkspaceConfig_1797_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_toLeanConfig_1798_);
lean_ctor_set(v_reuseFailAlloc_1836_, 2, v_extraDepTargets_1800_);
lean_ctor_set(v_reuseFailAlloc_1836_, 3, v_moreGlobalServerArgs_1802_);
lean_ctor_set(v_reuseFailAlloc_1836_, 4, v_srcDir_1803_);
lean_ctor_set(v_reuseFailAlloc_1836_, 5, v_buildDir_1804_);
lean_ctor_set(v_reuseFailAlloc_1836_, 6, v_leanLibDir_1805_);
lean_ctor_set(v_reuseFailAlloc_1836_, 7, v_nativeLibDir_1806_);
lean_ctor_set(v_reuseFailAlloc_1836_, 8, v_binDir_1807_);
lean_ctor_set(v_reuseFailAlloc_1836_, 9, v_irDir_1808_);
lean_ctor_set(v_reuseFailAlloc_1836_, 10, v_releaseRepo_1809_);
lean_ctor_set(v_reuseFailAlloc_1836_, 11, v_buildArchive_1810_);
lean_ctor_set(v_reuseFailAlloc_1836_, 12, v_val_1795_);
lean_ctor_set(v_reuseFailAlloc_1836_, 13, v_testDriverArgs_1812_);
lean_ctor_set(v_reuseFailAlloc_1836_, 14, v_lintDriver_1813_);
lean_ctor_set(v_reuseFailAlloc_1836_, 15, v_lintDriverArgs_1814_);
lean_ctor_set(v_reuseFailAlloc_1836_, 16, v_version_1815_);
lean_ctor_set(v_reuseFailAlloc_1836_, 17, v_versionTags_1816_);
lean_ctor_set(v_reuseFailAlloc_1836_, 18, v_description_1817_);
lean_ctor_set(v_reuseFailAlloc_1836_, 19, v_keywords_1818_);
lean_ctor_set(v_reuseFailAlloc_1836_, 20, v_homepage_1819_);
lean_ctor_set(v_reuseFailAlloc_1836_, 21, v_license_1820_);
lean_ctor_set(v_reuseFailAlloc_1836_, 22, v_licenseFiles_1821_);
lean_ctor_set(v_reuseFailAlloc_1836_, 23, v_readmeFile_1822_);
lean_ctor_set(v_reuseFailAlloc_1836_, 24, v_enableArtifactCache_x3f_1824_);
lean_ctor_set(v_reuseFailAlloc_1836_, 25, v_restoreAllArtifacts_x3f_1825_);
lean_ctor_set(v_reuseFailAlloc_1836_, 26, v_builtinLint_x3f_1828_);
lean_ctor_set(v_reuseFailAlloc_1836_, 27, v_checks_1829_);
lean_ctor_set_uint8(v_reuseFailAlloc_1836_, sizeof(void*)*28, v_bootstrap_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1836_, sizeof(void*)*28 + 1, v_precompileModules_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1836_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1836_, sizeof(void*)*28 + 3, v_reservoir_1823_);
lean_ctor_set_uint8(v_reuseFailAlloc_1836_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1836_, sizeof(void*)*28 + 5, v_allowImportAll_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1836_, sizeof(void*)*28 + 6, v_fixedToolchain_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__2(lean_object* v_f_1839_, lean_object* v_cfg_1840_){
_start:
{
lean_object* v_toWorkspaceConfig_1841_; lean_object* v_toLeanConfig_1842_; uint8_t v_bootstrap_1843_; lean_object* v_extraDepTargets_1844_; uint8_t v_precompileModules_1845_; lean_object* v_moreGlobalServerArgs_1846_; lean_object* v_srcDir_1847_; lean_object* v_buildDir_1848_; lean_object* v_leanLibDir_1849_; lean_object* v_nativeLibDir_1850_; lean_object* v_binDir_1851_; lean_object* v_irDir_1852_; lean_object* v_releaseRepo_1853_; lean_object* v_buildArchive_1854_; uint8_t v_preferReleaseBuild_1855_; lean_object* v_testDriver_1856_; lean_object* v_testDriverArgs_1857_; lean_object* v_lintDriver_1858_; lean_object* v_lintDriverArgs_1859_; lean_object* v_version_1860_; lean_object* v_versionTags_1861_; lean_object* v_description_1862_; lean_object* v_keywords_1863_; lean_object* v_homepage_1864_; lean_object* v_license_1865_; lean_object* v_licenseFiles_1866_; lean_object* v_readmeFile_1867_; uint8_t v_reservoir_1868_; lean_object* v_enableArtifactCache_x3f_1869_; lean_object* v_restoreAllArtifacts_x3f_1870_; uint8_t v_libPrefixOnWindows_1871_; uint8_t v_allowImportAll_1872_; lean_object* v_builtinLint_x3f_1873_; lean_object* v_checks_1874_; uint8_t v_fixedToolchain_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1883_; 
v_toWorkspaceConfig_1841_ = lean_ctor_get(v_cfg_1840_, 0);
v_toLeanConfig_1842_ = lean_ctor_get(v_cfg_1840_, 1);
v_bootstrap_1843_ = lean_ctor_get_uint8(v_cfg_1840_, sizeof(void*)*28);
v_extraDepTargets_1844_ = lean_ctor_get(v_cfg_1840_, 2);
v_precompileModules_1845_ = lean_ctor_get_uint8(v_cfg_1840_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1846_ = lean_ctor_get(v_cfg_1840_, 3);
v_srcDir_1847_ = lean_ctor_get(v_cfg_1840_, 4);
v_buildDir_1848_ = lean_ctor_get(v_cfg_1840_, 5);
v_leanLibDir_1849_ = lean_ctor_get(v_cfg_1840_, 6);
v_nativeLibDir_1850_ = lean_ctor_get(v_cfg_1840_, 7);
v_binDir_1851_ = lean_ctor_get(v_cfg_1840_, 8);
v_irDir_1852_ = lean_ctor_get(v_cfg_1840_, 9);
v_releaseRepo_1853_ = lean_ctor_get(v_cfg_1840_, 10);
v_buildArchive_1854_ = lean_ctor_get(v_cfg_1840_, 11);
v_preferReleaseBuild_1855_ = lean_ctor_get_uint8(v_cfg_1840_, sizeof(void*)*28 + 2);
v_testDriver_1856_ = lean_ctor_get(v_cfg_1840_, 12);
v_testDriverArgs_1857_ = lean_ctor_get(v_cfg_1840_, 13);
v_lintDriver_1858_ = lean_ctor_get(v_cfg_1840_, 14);
v_lintDriverArgs_1859_ = lean_ctor_get(v_cfg_1840_, 15);
v_version_1860_ = lean_ctor_get(v_cfg_1840_, 16);
v_versionTags_1861_ = lean_ctor_get(v_cfg_1840_, 17);
v_description_1862_ = lean_ctor_get(v_cfg_1840_, 18);
v_keywords_1863_ = lean_ctor_get(v_cfg_1840_, 19);
v_homepage_1864_ = lean_ctor_get(v_cfg_1840_, 20);
v_license_1865_ = lean_ctor_get(v_cfg_1840_, 21);
v_licenseFiles_1866_ = lean_ctor_get(v_cfg_1840_, 22);
v_readmeFile_1867_ = lean_ctor_get(v_cfg_1840_, 23);
v_reservoir_1868_ = lean_ctor_get_uint8(v_cfg_1840_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1869_ = lean_ctor_get(v_cfg_1840_, 24);
v_restoreAllArtifacts_x3f_1870_ = lean_ctor_get(v_cfg_1840_, 25);
v_libPrefixOnWindows_1871_ = lean_ctor_get_uint8(v_cfg_1840_, sizeof(void*)*28 + 4);
v_allowImportAll_1872_ = lean_ctor_get_uint8(v_cfg_1840_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1873_ = lean_ctor_get(v_cfg_1840_, 26);
v_checks_1874_ = lean_ctor_get(v_cfg_1840_, 27);
v_fixedToolchain_1875_ = lean_ctor_get_uint8(v_cfg_1840_, sizeof(void*)*28 + 6);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_cfg_1840_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1877_ = v_cfg_1840_;
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_checks_1874_);
lean_inc(v_builtinLint_x3f_1873_);
lean_inc(v_restoreAllArtifacts_x3f_1870_);
lean_inc(v_enableArtifactCache_x3f_1869_);
lean_inc(v_readmeFile_1867_);
lean_inc(v_licenseFiles_1866_);
lean_inc(v_license_1865_);
lean_inc(v_homepage_1864_);
lean_inc(v_keywords_1863_);
lean_inc(v_description_1862_);
lean_inc(v_versionTags_1861_);
lean_inc(v_version_1860_);
lean_inc(v_lintDriverArgs_1859_);
lean_inc(v_lintDriver_1858_);
lean_inc(v_testDriverArgs_1857_);
lean_inc(v_testDriver_1856_);
lean_inc(v_buildArchive_1854_);
lean_inc(v_releaseRepo_1853_);
lean_inc(v_irDir_1852_);
lean_inc(v_binDir_1851_);
lean_inc(v_nativeLibDir_1850_);
lean_inc(v_leanLibDir_1849_);
lean_inc(v_buildDir_1848_);
lean_inc(v_srcDir_1847_);
lean_inc(v_moreGlobalServerArgs_1846_);
lean_inc(v_extraDepTargets_1844_);
lean_inc(v_toLeanConfig_1842_);
lean_inc(v_toWorkspaceConfig_1841_);
lean_dec(v_cfg_1840_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1879_ = lean_apply_1(v_f_1839_, v_testDriver_1856_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 12, v___x_1879_);
v___x_1881_ = v___x_1877_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_toWorkspaceConfig_1841_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_toLeanConfig_1842_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_extraDepTargets_1844_);
lean_ctor_set(v_reuseFailAlloc_1882_, 3, v_moreGlobalServerArgs_1846_);
lean_ctor_set(v_reuseFailAlloc_1882_, 4, v_srcDir_1847_);
lean_ctor_set(v_reuseFailAlloc_1882_, 5, v_buildDir_1848_);
lean_ctor_set(v_reuseFailAlloc_1882_, 6, v_leanLibDir_1849_);
lean_ctor_set(v_reuseFailAlloc_1882_, 7, v_nativeLibDir_1850_);
lean_ctor_set(v_reuseFailAlloc_1882_, 8, v_binDir_1851_);
lean_ctor_set(v_reuseFailAlloc_1882_, 9, v_irDir_1852_);
lean_ctor_set(v_reuseFailAlloc_1882_, 10, v_releaseRepo_1853_);
lean_ctor_set(v_reuseFailAlloc_1882_, 11, v_buildArchive_1854_);
lean_ctor_set(v_reuseFailAlloc_1882_, 12, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1882_, 13, v_testDriverArgs_1857_);
lean_ctor_set(v_reuseFailAlloc_1882_, 14, v_lintDriver_1858_);
lean_ctor_set(v_reuseFailAlloc_1882_, 15, v_lintDriverArgs_1859_);
lean_ctor_set(v_reuseFailAlloc_1882_, 16, v_version_1860_);
lean_ctor_set(v_reuseFailAlloc_1882_, 17, v_versionTags_1861_);
lean_ctor_set(v_reuseFailAlloc_1882_, 18, v_description_1862_);
lean_ctor_set(v_reuseFailAlloc_1882_, 19, v_keywords_1863_);
lean_ctor_set(v_reuseFailAlloc_1882_, 20, v_homepage_1864_);
lean_ctor_set(v_reuseFailAlloc_1882_, 21, v_license_1865_);
lean_ctor_set(v_reuseFailAlloc_1882_, 22, v_licenseFiles_1866_);
lean_ctor_set(v_reuseFailAlloc_1882_, 23, v_readmeFile_1867_);
lean_ctor_set(v_reuseFailAlloc_1882_, 24, v_enableArtifactCache_x3f_1869_);
lean_ctor_set(v_reuseFailAlloc_1882_, 25, v_restoreAllArtifacts_x3f_1870_);
lean_ctor_set(v_reuseFailAlloc_1882_, 26, v_builtinLint_x3f_1873_);
lean_ctor_set(v_reuseFailAlloc_1882_, 27, v_checks_1874_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*28, v_bootstrap_1843_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*28 + 1, v_precompileModules_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1855_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*28 + 3, v_reservoir_1868_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1871_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*28 + 5, v_allowImportAll_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*28 + 6, v_fixedToolchain_1875_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__3(lean_object* v_x_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__2));
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__3___boxed(lean_object* v_x_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lake_PackageConfig_testDriver___proj___redArg___lam__3(v_x_1886_);
lean_dec_ref(v_x_1886_);
return v_res_1887_;
}
}
lean_object* l_Lake_PackageConfig_testDriver___proj___redArg(){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = ((lean_object*)(l_Lake_PackageConfig_testDriver___proj___redArg___closed__4));
return v___x_1898_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_testDriver___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1899_;
v_res_1899_ = l_Lake_PackageConfig_testDriver___proj___redArg();
stack->m_obj
 = v_res_1899_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___boxed(lean_object* v___dummy_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lake_PackageConfig_testDriver___proj___redArg();
return v_res_1901_;
}
}
static lean_object* _init_l_Lake_PackageConfig_testDriver___proj___closed__0(void){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lake_PackageConfig_testDriver___proj___redArg();
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object* v_p_1903_, lean_object* v_n_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object* v_p_1906_, lean_object* v_n_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lake_PackageConfig_testDriver___proj(v_p_1906_, v_n_1907_);
lean_dec(v_n_1907_);
lean_dec(v_p_1906_);
return v_res_1908_;
}
}
lean_object* l_Lake_PackageConfig_testDriver_instConfigField___redArg(){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_1910_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_testDriver_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1911_;
v_res_1911_ = l_Lake_PackageConfig_testDriver_instConfigField___redArg();
stack->m_obj
 = v_res_1911_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___redArg___boxed(lean_object* v___dummy_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lake_PackageConfig_testDriver_instConfigField___redArg();
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object* v_p_1914_, lean_object* v_n_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object* v_p_1917_, lean_object* v_n_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lake_PackageConfig_testDriver_instConfigField(v_p_1917_, v_n_1918_);
lean_dec(v_n_1918_);
lean_dec(v_p_1917_);
return v_res_1919_;
}
}
lean_object* l_Lake_PackageConfig_testRunner_instConfigField___redArg(){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_1921_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_testRunner_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1922_;
v_res_1922_ = l_Lake_PackageConfig_testRunner_instConfigField___redArg();
stack->m_obj
 = v_res_1922_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___redArg___boxed(lean_object* v___dummy_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lake_PackageConfig_testRunner_instConfigField___redArg();
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object* v_p_1925_, lean_object* v_n_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object* v_p_1928_, lean_object* v_n_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lake_PackageConfig_testRunner_instConfigField(v_p_1928_, v_n_1929_);
lean_dec(v_n_1929_);
lean_dec(v_p_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0(lean_object* v_cfg_1931_){
_start:
{
lean_object* v_testDriverArgs_1932_; 
v_testDriverArgs_1932_ = lean_ctor_get(v_cfg_1931_, 13);
lean_inc_ref(v_testDriverArgs_1932_);
return v_testDriverArgs_1932_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0___boxed(lean_object* v_cfg_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0(v_cfg_1933_);
lean_dec_ref(v_cfg_1933_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__1(lean_object* v_val_1935_, lean_object* v_cfg_1936_){
_start:
{
lean_object* v_toWorkspaceConfig_1937_; lean_object* v_toLeanConfig_1938_; uint8_t v_bootstrap_1939_; lean_object* v_extraDepTargets_1940_; uint8_t v_precompileModules_1941_; lean_object* v_moreGlobalServerArgs_1942_; lean_object* v_srcDir_1943_; lean_object* v_buildDir_1944_; lean_object* v_leanLibDir_1945_; lean_object* v_nativeLibDir_1946_; lean_object* v_binDir_1947_; lean_object* v_irDir_1948_; lean_object* v_releaseRepo_1949_; lean_object* v_buildArchive_1950_; uint8_t v_preferReleaseBuild_1951_; lean_object* v_testDriver_1952_; lean_object* v_lintDriver_1953_; lean_object* v_lintDriverArgs_1954_; lean_object* v_version_1955_; lean_object* v_versionTags_1956_; lean_object* v_description_1957_; lean_object* v_keywords_1958_; lean_object* v_homepage_1959_; lean_object* v_license_1960_; lean_object* v_licenseFiles_1961_; lean_object* v_readmeFile_1962_; uint8_t v_reservoir_1963_; lean_object* v_enableArtifactCache_x3f_1964_; lean_object* v_restoreAllArtifacts_x3f_1965_; uint8_t v_libPrefixOnWindows_1966_; uint8_t v_allowImportAll_1967_; lean_object* v_builtinLint_x3f_1968_; lean_object* v_checks_1969_; uint8_t v_fixedToolchain_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
v_toWorkspaceConfig_1937_ = lean_ctor_get(v_cfg_1936_, 0);
v_toLeanConfig_1938_ = lean_ctor_get(v_cfg_1936_, 1);
v_bootstrap_1939_ = lean_ctor_get_uint8(v_cfg_1936_, sizeof(void*)*28);
v_extraDepTargets_1940_ = lean_ctor_get(v_cfg_1936_, 2);
v_precompileModules_1941_ = lean_ctor_get_uint8(v_cfg_1936_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1942_ = lean_ctor_get(v_cfg_1936_, 3);
v_srcDir_1943_ = lean_ctor_get(v_cfg_1936_, 4);
v_buildDir_1944_ = lean_ctor_get(v_cfg_1936_, 5);
v_leanLibDir_1945_ = lean_ctor_get(v_cfg_1936_, 6);
v_nativeLibDir_1946_ = lean_ctor_get(v_cfg_1936_, 7);
v_binDir_1947_ = lean_ctor_get(v_cfg_1936_, 8);
v_irDir_1948_ = lean_ctor_get(v_cfg_1936_, 9);
v_releaseRepo_1949_ = lean_ctor_get(v_cfg_1936_, 10);
v_buildArchive_1950_ = lean_ctor_get(v_cfg_1936_, 11);
v_preferReleaseBuild_1951_ = lean_ctor_get_uint8(v_cfg_1936_, sizeof(void*)*28 + 2);
v_testDriver_1952_ = lean_ctor_get(v_cfg_1936_, 12);
v_lintDriver_1953_ = lean_ctor_get(v_cfg_1936_, 14);
v_lintDriverArgs_1954_ = lean_ctor_get(v_cfg_1936_, 15);
v_version_1955_ = lean_ctor_get(v_cfg_1936_, 16);
v_versionTags_1956_ = lean_ctor_get(v_cfg_1936_, 17);
v_description_1957_ = lean_ctor_get(v_cfg_1936_, 18);
v_keywords_1958_ = lean_ctor_get(v_cfg_1936_, 19);
v_homepage_1959_ = lean_ctor_get(v_cfg_1936_, 20);
v_license_1960_ = lean_ctor_get(v_cfg_1936_, 21);
v_licenseFiles_1961_ = lean_ctor_get(v_cfg_1936_, 22);
v_readmeFile_1962_ = lean_ctor_get(v_cfg_1936_, 23);
v_reservoir_1963_ = lean_ctor_get_uint8(v_cfg_1936_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1964_ = lean_ctor_get(v_cfg_1936_, 24);
v_restoreAllArtifacts_x3f_1965_ = lean_ctor_get(v_cfg_1936_, 25);
v_libPrefixOnWindows_1966_ = lean_ctor_get_uint8(v_cfg_1936_, sizeof(void*)*28 + 4);
v_allowImportAll_1967_ = lean_ctor_get_uint8(v_cfg_1936_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1968_ = lean_ctor_get(v_cfg_1936_, 26);
v_checks_1969_ = lean_ctor_get(v_cfg_1936_, 27);
v_fixedToolchain_1970_ = lean_ctor_get_uint8(v_cfg_1936_, sizeof(void*)*28 + 6);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_cfg_1936_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; 
v_unused_1978_ = lean_ctor_get(v_cfg_1936_, 13);
lean_dec(v_unused_1978_);
v___x_1972_ = v_cfg_1936_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_checks_1969_);
lean_inc(v_builtinLint_x3f_1968_);
lean_inc(v_restoreAllArtifacts_x3f_1965_);
lean_inc(v_enableArtifactCache_x3f_1964_);
lean_inc(v_readmeFile_1962_);
lean_inc(v_licenseFiles_1961_);
lean_inc(v_license_1960_);
lean_inc(v_homepage_1959_);
lean_inc(v_keywords_1958_);
lean_inc(v_description_1957_);
lean_inc(v_versionTags_1956_);
lean_inc(v_version_1955_);
lean_inc(v_lintDriverArgs_1954_);
lean_inc(v_lintDriver_1953_);
lean_inc(v_testDriver_1952_);
lean_inc(v_buildArchive_1950_);
lean_inc(v_releaseRepo_1949_);
lean_inc(v_irDir_1948_);
lean_inc(v_binDir_1947_);
lean_inc(v_nativeLibDir_1946_);
lean_inc(v_leanLibDir_1945_);
lean_inc(v_buildDir_1944_);
lean_inc(v_srcDir_1943_);
lean_inc(v_moreGlobalServerArgs_1942_);
lean_inc(v_extraDepTargets_1940_);
lean_inc(v_toLeanConfig_1938_);
lean_inc(v_toWorkspaceConfig_1937_);
lean_dec(v_cfg_1936_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 13, v_val_1935_);
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_toWorkspaceConfig_1937_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_toLeanConfig_1938_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_extraDepTargets_1940_);
lean_ctor_set(v_reuseFailAlloc_1976_, 3, v_moreGlobalServerArgs_1942_);
lean_ctor_set(v_reuseFailAlloc_1976_, 4, v_srcDir_1943_);
lean_ctor_set(v_reuseFailAlloc_1976_, 5, v_buildDir_1944_);
lean_ctor_set(v_reuseFailAlloc_1976_, 6, v_leanLibDir_1945_);
lean_ctor_set(v_reuseFailAlloc_1976_, 7, v_nativeLibDir_1946_);
lean_ctor_set(v_reuseFailAlloc_1976_, 8, v_binDir_1947_);
lean_ctor_set(v_reuseFailAlloc_1976_, 9, v_irDir_1948_);
lean_ctor_set(v_reuseFailAlloc_1976_, 10, v_releaseRepo_1949_);
lean_ctor_set(v_reuseFailAlloc_1976_, 11, v_buildArchive_1950_);
lean_ctor_set(v_reuseFailAlloc_1976_, 12, v_testDriver_1952_);
lean_ctor_set(v_reuseFailAlloc_1976_, 13, v_val_1935_);
lean_ctor_set(v_reuseFailAlloc_1976_, 14, v_lintDriver_1953_);
lean_ctor_set(v_reuseFailAlloc_1976_, 15, v_lintDriverArgs_1954_);
lean_ctor_set(v_reuseFailAlloc_1976_, 16, v_version_1955_);
lean_ctor_set(v_reuseFailAlloc_1976_, 17, v_versionTags_1956_);
lean_ctor_set(v_reuseFailAlloc_1976_, 18, v_description_1957_);
lean_ctor_set(v_reuseFailAlloc_1976_, 19, v_keywords_1958_);
lean_ctor_set(v_reuseFailAlloc_1976_, 20, v_homepage_1959_);
lean_ctor_set(v_reuseFailAlloc_1976_, 21, v_license_1960_);
lean_ctor_set(v_reuseFailAlloc_1976_, 22, v_licenseFiles_1961_);
lean_ctor_set(v_reuseFailAlloc_1976_, 23, v_readmeFile_1962_);
lean_ctor_set(v_reuseFailAlloc_1976_, 24, v_enableArtifactCache_x3f_1964_);
lean_ctor_set(v_reuseFailAlloc_1976_, 25, v_restoreAllArtifacts_x3f_1965_);
lean_ctor_set(v_reuseFailAlloc_1976_, 26, v_builtinLint_x3f_1968_);
lean_ctor_set(v_reuseFailAlloc_1976_, 27, v_checks_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*28, v_bootstrap_1939_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*28 + 1, v_precompileModules_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1951_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*28 + 3, v_reservoir_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*28 + 5, v_allowImportAll_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*28 + 6, v_fixedToolchain_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__2(lean_object* v_f_1979_, lean_object* v_cfg_1980_){
_start:
{
lean_object* v_toWorkspaceConfig_1981_; lean_object* v_toLeanConfig_1982_; uint8_t v_bootstrap_1983_; lean_object* v_extraDepTargets_1984_; uint8_t v_precompileModules_1985_; lean_object* v_moreGlobalServerArgs_1986_; lean_object* v_srcDir_1987_; lean_object* v_buildDir_1988_; lean_object* v_leanLibDir_1989_; lean_object* v_nativeLibDir_1990_; lean_object* v_binDir_1991_; lean_object* v_irDir_1992_; lean_object* v_releaseRepo_1993_; lean_object* v_buildArchive_1994_; uint8_t v_preferReleaseBuild_1995_; lean_object* v_testDriver_1996_; lean_object* v_testDriverArgs_1997_; lean_object* v_lintDriver_1998_; lean_object* v_lintDriverArgs_1999_; lean_object* v_version_2000_; lean_object* v_versionTags_2001_; lean_object* v_description_2002_; lean_object* v_keywords_2003_; lean_object* v_homepage_2004_; lean_object* v_license_2005_; lean_object* v_licenseFiles_2006_; lean_object* v_readmeFile_2007_; uint8_t v_reservoir_2008_; lean_object* v_enableArtifactCache_x3f_2009_; lean_object* v_restoreAllArtifacts_x3f_2010_; uint8_t v_libPrefixOnWindows_2011_; uint8_t v_allowImportAll_2012_; lean_object* v_builtinLint_x3f_2013_; lean_object* v_checks_2014_; uint8_t v_fixedToolchain_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2023_; 
v_toWorkspaceConfig_1981_ = lean_ctor_get(v_cfg_1980_, 0);
v_toLeanConfig_1982_ = lean_ctor_get(v_cfg_1980_, 1);
v_bootstrap_1983_ = lean_ctor_get_uint8(v_cfg_1980_, sizeof(void*)*28);
v_extraDepTargets_1984_ = lean_ctor_get(v_cfg_1980_, 2);
v_precompileModules_1985_ = lean_ctor_get_uint8(v_cfg_1980_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1986_ = lean_ctor_get(v_cfg_1980_, 3);
v_srcDir_1987_ = lean_ctor_get(v_cfg_1980_, 4);
v_buildDir_1988_ = lean_ctor_get(v_cfg_1980_, 5);
v_leanLibDir_1989_ = lean_ctor_get(v_cfg_1980_, 6);
v_nativeLibDir_1990_ = lean_ctor_get(v_cfg_1980_, 7);
v_binDir_1991_ = lean_ctor_get(v_cfg_1980_, 8);
v_irDir_1992_ = lean_ctor_get(v_cfg_1980_, 9);
v_releaseRepo_1993_ = lean_ctor_get(v_cfg_1980_, 10);
v_buildArchive_1994_ = lean_ctor_get(v_cfg_1980_, 11);
v_preferReleaseBuild_1995_ = lean_ctor_get_uint8(v_cfg_1980_, sizeof(void*)*28 + 2);
v_testDriver_1996_ = lean_ctor_get(v_cfg_1980_, 12);
v_testDriverArgs_1997_ = lean_ctor_get(v_cfg_1980_, 13);
v_lintDriver_1998_ = lean_ctor_get(v_cfg_1980_, 14);
v_lintDriverArgs_1999_ = lean_ctor_get(v_cfg_1980_, 15);
v_version_2000_ = lean_ctor_get(v_cfg_1980_, 16);
v_versionTags_2001_ = lean_ctor_get(v_cfg_1980_, 17);
v_description_2002_ = lean_ctor_get(v_cfg_1980_, 18);
v_keywords_2003_ = lean_ctor_get(v_cfg_1980_, 19);
v_homepage_2004_ = lean_ctor_get(v_cfg_1980_, 20);
v_license_2005_ = lean_ctor_get(v_cfg_1980_, 21);
v_licenseFiles_2006_ = lean_ctor_get(v_cfg_1980_, 22);
v_readmeFile_2007_ = lean_ctor_get(v_cfg_1980_, 23);
v_reservoir_2008_ = lean_ctor_get_uint8(v_cfg_1980_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2009_ = lean_ctor_get(v_cfg_1980_, 24);
v_restoreAllArtifacts_x3f_2010_ = lean_ctor_get(v_cfg_1980_, 25);
v_libPrefixOnWindows_2011_ = lean_ctor_get_uint8(v_cfg_1980_, sizeof(void*)*28 + 4);
v_allowImportAll_2012_ = lean_ctor_get_uint8(v_cfg_1980_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2013_ = lean_ctor_get(v_cfg_1980_, 26);
v_checks_2014_ = lean_ctor_get(v_cfg_1980_, 27);
v_fixedToolchain_2015_ = lean_ctor_get_uint8(v_cfg_1980_, sizeof(void*)*28 + 6);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_cfg_1980_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2017_ = v_cfg_1980_;
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_checks_2014_);
lean_inc(v_builtinLint_x3f_2013_);
lean_inc(v_restoreAllArtifacts_x3f_2010_);
lean_inc(v_enableArtifactCache_x3f_2009_);
lean_inc(v_readmeFile_2007_);
lean_inc(v_licenseFiles_2006_);
lean_inc(v_license_2005_);
lean_inc(v_homepage_2004_);
lean_inc(v_keywords_2003_);
lean_inc(v_description_2002_);
lean_inc(v_versionTags_2001_);
lean_inc(v_version_2000_);
lean_inc(v_lintDriverArgs_1999_);
lean_inc(v_lintDriver_1998_);
lean_inc(v_testDriverArgs_1997_);
lean_inc(v_testDriver_1996_);
lean_inc(v_buildArchive_1994_);
lean_inc(v_releaseRepo_1993_);
lean_inc(v_irDir_1992_);
lean_inc(v_binDir_1991_);
lean_inc(v_nativeLibDir_1990_);
lean_inc(v_leanLibDir_1989_);
lean_inc(v_buildDir_1988_);
lean_inc(v_srcDir_1987_);
lean_inc(v_moreGlobalServerArgs_1986_);
lean_inc(v_extraDepTargets_1984_);
lean_inc(v_toLeanConfig_1982_);
lean_inc(v_toWorkspaceConfig_1981_);
lean_dec(v_cfg_1980_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_apply_1(v_f_1979_, v_testDriverArgs_1997_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 13, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_toWorkspaceConfig_1981_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_toLeanConfig_1982_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_extraDepTargets_1984_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_moreGlobalServerArgs_1986_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_srcDir_1987_);
lean_ctor_set(v_reuseFailAlloc_2022_, 5, v_buildDir_1988_);
lean_ctor_set(v_reuseFailAlloc_2022_, 6, v_leanLibDir_1989_);
lean_ctor_set(v_reuseFailAlloc_2022_, 7, v_nativeLibDir_1990_);
lean_ctor_set(v_reuseFailAlloc_2022_, 8, v_binDir_1991_);
lean_ctor_set(v_reuseFailAlloc_2022_, 9, v_irDir_1992_);
lean_ctor_set(v_reuseFailAlloc_2022_, 10, v_releaseRepo_1993_);
lean_ctor_set(v_reuseFailAlloc_2022_, 11, v_buildArchive_1994_);
lean_ctor_set(v_reuseFailAlloc_2022_, 12, v_testDriver_1996_);
lean_ctor_set(v_reuseFailAlloc_2022_, 13, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2022_, 14, v_lintDriver_1998_);
lean_ctor_set(v_reuseFailAlloc_2022_, 15, v_lintDriverArgs_1999_);
lean_ctor_set(v_reuseFailAlloc_2022_, 16, v_version_2000_);
lean_ctor_set(v_reuseFailAlloc_2022_, 17, v_versionTags_2001_);
lean_ctor_set(v_reuseFailAlloc_2022_, 18, v_description_2002_);
lean_ctor_set(v_reuseFailAlloc_2022_, 19, v_keywords_2003_);
lean_ctor_set(v_reuseFailAlloc_2022_, 20, v_homepage_2004_);
lean_ctor_set(v_reuseFailAlloc_2022_, 21, v_license_2005_);
lean_ctor_set(v_reuseFailAlloc_2022_, 22, v_licenseFiles_2006_);
lean_ctor_set(v_reuseFailAlloc_2022_, 23, v_readmeFile_2007_);
lean_ctor_set(v_reuseFailAlloc_2022_, 24, v_enableArtifactCache_x3f_2009_);
lean_ctor_set(v_reuseFailAlloc_2022_, 25, v_restoreAllArtifacts_x3f_2010_);
lean_ctor_set(v_reuseFailAlloc_2022_, 26, v_builtinLint_x3f_2013_);
lean_ctor_set(v_reuseFailAlloc_2022_, 27, v_checks_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*28, v_bootstrap_1983_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*28 + 1, v_precompileModules_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*28 + 3, v_reservoir_2008_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*28 + 5, v_allowImportAll_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*28 + 6, v_fixedToolchain_2015_);
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
lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg(){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = ((lean_object*)(l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__3));
return v___x_2033_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_testDriverArgs___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2034_;
v_res_2034_ = l_Lake_PackageConfig_testDriverArgs___proj___redArg();
stack->m_obj
 = v_res_2034_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___boxed(lean_object* v___dummy_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lake_PackageConfig_testDriverArgs___proj___redArg();
return v_res_2036_;
}
}
static lean_object* _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0(void){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lake_PackageConfig_testDriverArgs___proj___redArg();
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object* v_p_2038_, lean_object* v_n_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_obj_once(&l_Lake_PackageConfig_testDriverArgs___proj___closed__0, &l_Lake_PackageConfig_testDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object* v_p_2041_, lean_object* v_n_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_2041_, v_n_2042_);
lean_dec(v_n_2042_);
lean_dec(v_p_2041_);
return v_res_2043_;
}
}
lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_obj_once(&l_Lake_PackageConfig_testDriverArgs___proj___closed__0, &l_Lake_PackageConfig_testDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0);
return v___x_2045_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2046_;
v_res_2046_ = l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg();
stack->m_obj
 = v_res_2046_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg___boxed(lean_object* v___dummy_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg();
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object* v_p_2049_, lean_object* v_n_2050_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_obj_once(&l_Lake_PackageConfig_testDriverArgs___proj___closed__0, &l_Lake_PackageConfig_testDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object* v_p_2052_, lean_object* v_n_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lake_PackageConfig_testDriverArgs_instConfigField(v_p_2052_, v_n_2053_);
lean_dec(v_n_2053_);
lean_dec(v_p_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0(lean_object* v_cfg_2055_){
_start:
{
lean_object* v_lintDriver_2056_; 
v_lintDriver_2056_ = lean_ctor_get(v_cfg_2055_, 14);
lean_inc_ref(v_lintDriver_2056_);
return v_lintDriver_2056_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0___boxed(lean_object* v_cfg_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0(v_cfg_2057_);
lean_dec_ref(v_cfg_2057_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__1(lean_object* v_val_2059_, lean_object* v_cfg_2060_){
_start:
{
lean_object* v_toWorkspaceConfig_2061_; lean_object* v_toLeanConfig_2062_; uint8_t v_bootstrap_2063_; lean_object* v_extraDepTargets_2064_; uint8_t v_precompileModules_2065_; lean_object* v_moreGlobalServerArgs_2066_; lean_object* v_srcDir_2067_; lean_object* v_buildDir_2068_; lean_object* v_leanLibDir_2069_; lean_object* v_nativeLibDir_2070_; lean_object* v_binDir_2071_; lean_object* v_irDir_2072_; lean_object* v_releaseRepo_2073_; lean_object* v_buildArchive_2074_; uint8_t v_preferReleaseBuild_2075_; lean_object* v_testDriver_2076_; lean_object* v_testDriverArgs_2077_; lean_object* v_lintDriverArgs_2078_; lean_object* v_version_2079_; lean_object* v_versionTags_2080_; lean_object* v_description_2081_; lean_object* v_keywords_2082_; lean_object* v_homepage_2083_; lean_object* v_license_2084_; lean_object* v_licenseFiles_2085_; lean_object* v_readmeFile_2086_; uint8_t v_reservoir_2087_; lean_object* v_enableArtifactCache_x3f_2088_; lean_object* v_restoreAllArtifacts_x3f_2089_; uint8_t v_libPrefixOnWindows_2090_; uint8_t v_allowImportAll_2091_; lean_object* v_builtinLint_x3f_2092_; lean_object* v_checks_2093_; uint8_t v_fixedToolchain_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
v_toWorkspaceConfig_2061_ = lean_ctor_get(v_cfg_2060_, 0);
v_toLeanConfig_2062_ = lean_ctor_get(v_cfg_2060_, 1);
v_bootstrap_2063_ = lean_ctor_get_uint8(v_cfg_2060_, sizeof(void*)*28);
v_extraDepTargets_2064_ = lean_ctor_get(v_cfg_2060_, 2);
v_precompileModules_2065_ = lean_ctor_get_uint8(v_cfg_2060_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2066_ = lean_ctor_get(v_cfg_2060_, 3);
v_srcDir_2067_ = lean_ctor_get(v_cfg_2060_, 4);
v_buildDir_2068_ = lean_ctor_get(v_cfg_2060_, 5);
v_leanLibDir_2069_ = lean_ctor_get(v_cfg_2060_, 6);
v_nativeLibDir_2070_ = lean_ctor_get(v_cfg_2060_, 7);
v_binDir_2071_ = lean_ctor_get(v_cfg_2060_, 8);
v_irDir_2072_ = lean_ctor_get(v_cfg_2060_, 9);
v_releaseRepo_2073_ = lean_ctor_get(v_cfg_2060_, 10);
v_buildArchive_2074_ = lean_ctor_get(v_cfg_2060_, 11);
v_preferReleaseBuild_2075_ = lean_ctor_get_uint8(v_cfg_2060_, sizeof(void*)*28 + 2);
v_testDriver_2076_ = lean_ctor_get(v_cfg_2060_, 12);
v_testDriverArgs_2077_ = lean_ctor_get(v_cfg_2060_, 13);
v_lintDriverArgs_2078_ = lean_ctor_get(v_cfg_2060_, 15);
v_version_2079_ = lean_ctor_get(v_cfg_2060_, 16);
v_versionTags_2080_ = lean_ctor_get(v_cfg_2060_, 17);
v_description_2081_ = lean_ctor_get(v_cfg_2060_, 18);
v_keywords_2082_ = lean_ctor_get(v_cfg_2060_, 19);
v_homepage_2083_ = lean_ctor_get(v_cfg_2060_, 20);
v_license_2084_ = lean_ctor_get(v_cfg_2060_, 21);
v_licenseFiles_2085_ = lean_ctor_get(v_cfg_2060_, 22);
v_readmeFile_2086_ = lean_ctor_get(v_cfg_2060_, 23);
v_reservoir_2087_ = lean_ctor_get_uint8(v_cfg_2060_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2088_ = lean_ctor_get(v_cfg_2060_, 24);
v_restoreAllArtifacts_x3f_2089_ = lean_ctor_get(v_cfg_2060_, 25);
v_libPrefixOnWindows_2090_ = lean_ctor_get_uint8(v_cfg_2060_, sizeof(void*)*28 + 4);
v_allowImportAll_2091_ = lean_ctor_get_uint8(v_cfg_2060_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2092_ = lean_ctor_get(v_cfg_2060_, 26);
v_checks_2093_ = lean_ctor_get(v_cfg_2060_, 27);
v_fixedToolchain_2094_ = lean_ctor_get_uint8(v_cfg_2060_, sizeof(void*)*28 + 6);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_cfg_2060_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; 
v_unused_2102_ = lean_ctor_get(v_cfg_2060_, 14);
lean_dec(v_unused_2102_);
v___x_2096_ = v_cfg_2060_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_checks_2093_);
lean_inc(v_builtinLint_x3f_2092_);
lean_inc(v_restoreAllArtifacts_x3f_2089_);
lean_inc(v_enableArtifactCache_x3f_2088_);
lean_inc(v_readmeFile_2086_);
lean_inc(v_licenseFiles_2085_);
lean_inc(v_license_2084_);
lean_inc(v_homepage_2083_);
lean_inc(v_keywords_2082_);
lean_inc(v_description_2081_);
lean_inc(v_versionTags_2080_);
lean_inc(v_version_2079_);
lean_inc(v_lintDriverArgs_2078_);
lean_inc(v_testDriverArgs_2077_);
lean_inc(v_testDriver_2076_);
lean_inc(v_buildArchive_2074_);
lean_inc(v_releaseRepo_2073_);
lean_inc(v_irDir_2072_);
lean_inc(v_binDir_2071_);
lean_inc(v_nativeLibDir_2070_);
lean_inc(v_leanLibDir_2069_);
lean_inc(v_buildDir_2068_);
lean_inc(v_srcDir_2067_);
lean_inc(v_moreGlobalServerArgs_2066_);
lean_inc(v_extraDepTargets_2064_);
lean_inc(v_toLeanConfig_2062_);
lean_inc(v_toWorkspaceConfig_2061_);
lean_dec(v_cfg_2060_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 14, v_val_2059_);
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_toWorkspaceConfig_2061_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_toLeanConfig_2062_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_extraDepTargets_2064_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v_moreGlobalServerArgs_2066_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v_srcDir_2067_);
lean_ctor_set(v_reuseFailAlloc_2100_, 5, v_buildDir_2068_);
lean_ctor_set(v_reuseFailAlloc_2100_, 6, v_leanLibDir_2069_);
lean_ctor_set(v_reuseFailAlloc_2100_, 7, v_nativeLibDir_2070_);
lean_ctor_set(v_reuseFailAlloc_2100_, 8, v_binDir_2071_);
lean_ctor_set(v_reuseFailAlloc_2100_, 9, v_irDir_2072_);
lean_ctor_set(v_reuseFailAlloc_2100_, 10, v_releaseRepo_2073_);
lean_ctor_set(v_reuseFailAlloc_2100_, 11, v_buildArchive_2074_);
lean_ctor_set(v_reuseFailAlloc_2100_, 12, v_testDriver_2076_);
lean_ctor_set(v_reuseFailAlloc_2100_, 13, v_testDriverArgs_2077_);
lean_ctor_set(v_reuseFailAlloc_2100_, 14, v_val_2059_);
lean_ctor_set(v_reuseFailAlloc_2100_, 15, v_lintDriverArgs_2078_);
lean_ctor_set(v_reuseFailAlloc_2100_, 16, v_version_2079_);
lean_ctor_set(v_reuseFailAlloc_2100_, 17, v_versionTags_2080_);
lean_ctor_set(v_reuseFailAlloc_2100_, 18, v_description_2081_);
lean_ctor_set(v_reuseFailAlloc_2100_, 19, v_keywords_2082_);
lean_ctor_set(v_reuseFailAlloc_2100_, 20, v_homepage_2083_);
lean_ctor_set(v_reuseFailAlloc_2100_, 21, v_license_2084_);
lean_ctor_set(v_reuseFailAlloc_2100_, 22, v_licenseFiles_2085_);
lean_ctor_set(v_reuseFailAlloc_2100_, 23, v_readmeFile_2086_);
lean_ctor_set(v_reuseFailAlloc_2100_, 24, v_enableArtifactCache_x3f_2088_);
lean_ctor_set(v_reuseFailAlloc_2100_, 25, v_restoreAllArtifacts_x3f_2089_);
lean_ctor_set(v_reuseFailAlloc_2100_, 26, v_builtinLint_x3f_2092_);
lean_ctor_set(v_reuseFailAlloc_2100_, 27, v_checks_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*28, v_bootstrap_2063_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*28 + 1, v_precompileModules_2065_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2075_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*28 + 3, v_reservoir_2087_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2090_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*28 + 5, v_allowImportAll_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*28 + 6, v_fixedToolchain_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__2(lean_object* v_f_2103_, lean_object* v_cfg_2104_){
_start:
{
lean_object* v_toWorkspaceConfig_2105_; lean_object* v_toLeanConfig_2106_; uint8_t v_bootstrap_2107_; lean_object* v_extraDepTargets_2108_; uint8_t v_precompileModules_2109_; lean_object* v_moreGlobalServerArgs_2110_; lean_object* v_srcDir_2111_; lean_object* v_buildDir_2112_; lean_object* v_leanLibDir_2113_; lean_object* v_nativeLibDir_2114_; lean_object* v_binDir_2115_; lean_object* v_irDir_2116_; lean_object* v_releaseRepo_2117_; lean_object* v_buildArchive_2118_; uint8_t v_preferReleaseBuild_2119_; lean_object* v_testDriver_2120_; lean_object* v_testDriverArgs_2121_; lean_object* v_lintDriver_2122_; lean_object* v_lintDriverArgs_2123_; lean_object* v_version_2124_; lean_object* v_versionTags_2125_; lean_object* v_description_2126_; lean_object* v_keywords_2127_; lean_object* v_homepage_2128_; lean_object* v_license_2129_; lean_object* v_licenseFiles_2130_; lean_object* v_readmeFile_2131_; uint8_t v_reservoir_2132_; lean_object* v_enableArtifactCache_x3f_2133_; lean_object* v_restoreAllArtifacts_x3f_2134_; uint8_t v_libPrefixOnWindows_2135_; uint8_t v_allowImportAll_2136_; lean_object* v_builtinLint_x3f_2137_; lean_object* v_checks_2138_; uint8_t v_fixedToolchain_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2147_; 
v_toWorkspaceConfig_2105_ = lean_ctor_get(v_cfg_2104_, 0);
v_toLeanConfig_2106_ = lean_ctor_get(v_cfg_2104_, 1);
v_bootstrap_2107_ = lean_ctor_get_uint8(v_cfg_2104_, sizeof(void*)*28);
v_extraDepTargets_2108_ = lean_ctor_get(v_cfg_2104_, 2);
v_precompileModules_2109_ = lean_ctor_get_uint8(v_cfg_2104_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2110_ = lean_ctor_get(v_cfg_2104_, 3);
v_srcDir_2111_ = lean_ctor_get(v_cfg_2104_, 4);
v_buildDir_2112_ = lean_ctor_get(v_cfg_2104_, 5);
v_leanLibDir_2113_ = lean_ctor_get(v_cfg_2104_, 6);
v_nativeLibDir_2114_ = lean_ctor_get(v_cfg_2104_, 7);
v_binDir_2115_ = lean_ctor_get(v_cfg_2104_, 8);
v_irDir_2116_ = lean_ctor_get(v_cfg_2104_, 9);
v_releaseRepo_2117_ = lean_ctor_get(v_cfg_2104_, 10);
v_buildArchive_2118_ = lean_ctor_get(v_cfg_2104_, 11);
v_preferReleaseBuild_2119_ = lean_ctor_get_uint8(v_cfg_2104_, sizeof(void*)*28 + 2);
v_testDriver_2120_ = lean_ctor_get(v_cfg_2104_, 12);
v_testDriverArgs_2121_ = lean_ctor_get(v_cfg_2104_, 13);
v_lintDriver_2122_ = lean_ctor_get(v_cfg_2104_, 14);
v_lintDriverArgs_2123_ = lean_ctor_get(v_cfg_2104_, 15);
v_version_2124_ = lean_ctor_get(v_cfg_2104_, 16);
v_versionTags_2125_ = lean_ctor_get(v_cfg_2104_, 17);
v_description_2126_ = lean_ctor_get(v_cfg_2104_, 18);
v_keywords_2127_ = lean_ctor_get(v_cfg_2104_, 19);
v_homepage_2128_ = lean_ctor_get(v_cfg_2104_, 20);
v_license_2129_ = lean_ctor_get(v_cfg_2104_, 21);
v_licenseFiles_2130_ = lean_ctor_get(v_cfg_2104_, 22);
v_readmeFile_2131_ = lean_ctor_get(v_cfg_2104_, 23);
v_reservoir_2132_ = lean_ctor_get_uint8(v_cfg_2104_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2133_ = lean_ctor_get(v_cfg_2104_, 24);
v_restoreAllArtifacts_x3f_2134_ = lean_ctor_get(v_cfg_2104_, 25);
v_libPrefixOnWindows_2135_ = lean_ctor_get_uint8(v_cfg_2104_, sizeof(void*)*28 + 4);
v_allowImportAll_2136_ = lean_ctor_get_uint8(v_cfg_2104_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2137_ = lean_ctor_get(v_cfg_2104_, 26);
v_checks_2138_ = lean_ctor_get(v_cfg_2104_, 27);
v_fixedToolchain_2139_ = lean_ctor_get_uint8(v_cfg_2104_, sizeof(void*)*28 + 6);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_cfg_2104_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2141_ = v_cfg_2104_;
v_isShared_2142_ = v_isSharedCheck_2147_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_checks_2138_);
lean_inc(v_builtinLint_x3f_2137_);
lean_inc(v_restoreAllArtifacts_x3f_2134_);
lean_inc(v_enableArtifactCache_x3f_2133_);
lean_inc(v_readmeFile_2131_);
lean_inc(v_licenseFiles_2130_);
lean_inc(v_license_2129_);
lean_inc(v_homepage_2128_);
lean_inc(v_keywords_2127_);
lean_inc(v_description_2126_);
lean_inc(v_versionTags_2125_);
lean_inc(v_version_2124_);
lean_inc(v_lintDriverArgs_2123_);
lean_inc(v_lintDriver_2122_);
lean_inc(v_testDriverArgs_2121_);
lean_inc(v_testDriver_2120_);
lean_inc(v_buildArchive_2118_);
lean_inc(v_releaseRepo_2117_);
lean_inc(v_irDir_2116_);
lean_inc(v_binDir_2115_);
lean_inc(v_nativeLibDir_2114_);
lean_inc(v_leanLibDir_2113_);
lean_inc(v_buildDir_2112_);
lean_inc(v_srcDir_2111_);
lean_inc(v_moreGlobalServerArgs_2110_);
lean_inc(v_extraDepTargets_2108_);
lean_inc(v_toLeanConfig_2106_);
lean_inc(v_toWorkspaceConfig_2105_);
lean_dec(v_cfg_2104_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2147_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2143_ = lean_apply_1(v_f_2103_, v_lintDriver_2122_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 14, v___x_2143_);
v___x_2145_ = v___x_2141_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_toWorkspaceConfig_2105_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_toLeanConfig_2106_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_extraDepTargets_2108_);
lean_ctor_set(v_reuseFailAlloc_2146_, 3, v_moreGlobalServerArgs_2110_);
lean_ctor_set(v_reuseFailAlloc_2146_, 4, v_srcDir_2111_);
lean_ctor_set(v_reuseFailAlloc_2146_, 5, v_buildDir_2112_);
lean_ctor_set(v_reuseFailAlloc_2146_, 6, v_leanLibDir_2113_);
lean_ctor_set(v_reuseFailAlloc_2146_, 7, v_nativeLibDir_2114_);
lean_ctor_set(v_reuseFailAlloc_2146_, 8, v_binDir_2115_);
lean_ctor_set(v_reuseFailAlloc_2146_, 9, v_irDir_2116_);
lean_ctor_set(v_reuseFailAlloc_2146_, 10, v_releaseRepo_2117_);
lean_ctor_set(v_reuseFailAlloc_2146_, 11, v_buildArchive_2118_);
lean_ctor_set(v_reuseFailAlloc_2146_, 12, v_testDriver_2120_);
lean_ctor_set(v_reuseFailAlloc_2146_, 13, v_testDriverArgs_2121_);
lean_ctor_set(v_reuseFailAlloc_2146_, 14, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2146_, 15, v_lintDriverArgs_2123_);
lean_ctor_set(v_reuseFailAlloc_2146_, 16, v_version_2124_);
lean_ctor_set(v_reuseFailAlloc_2146_, 17, v_versionTags_2125_);
lean_ctor_set(v_reuseFailAlloc_2146_, 18, v_description_2126_);
lean_ctor_set(v_reuseFailAlloc_2146_, 19, v_keywords_2127_);
lean_ctor_set(v_reuseFailAlloc_2146_, 20, v_homepage_2128_);
lean_ctor_set(v_reuseFailAlloc_2146_, 21, v_license_2129_);
lean_ctor_set(v_reuseFailAlloc_2146_, 22, v_licenseFiles_2130_);
lean_ctor_set(v_reuseFailAlloc_2146_, 23, v_readmeFile_2131_);
lean_ctor_set(v_reuseFailAlloc_2146_, 24, v_enableArtifactCache_x3f_2133_);
lean_ctor_set(v_reuseFailAlloc_2146_, 25, v_restoreAllArtifacts_x3f_2134_);
lean_ctor_set(v_reuseFailAlloc_2146_, 26, v_builtinLint_x3f_2137_);
lean_ctor_set(v_reuseFailAlloc_2146_, 27, v_checks_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*28, v_bootstrap_2107_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*28 + 1, v_precompileModules_2109_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2119_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*28 + 3, v_reservoir_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*28 + 5, v_allowImportAll_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*28 + 6, v_fixedToolchain_2139_);
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
lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg(){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = ((lean_object*)(l_Lake_PackageConfig_lintDriver___proj___redArg___closed__3));
return v___x_2157_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_lintDriver___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2158_;
v_res_2158_ = l_Lake_PackageConfig_lintDriver___proj___redArg();
stack->m_obj
 = v_res_2158_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___boxed(lean_object* v___dummy_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lake_PackageConfig_lintDriver___proj___redArg();
return v_res_2160_;
}
}
static lean_object* _init_l_Lake_PackageConfig_lintDriver___proj___closed__0(void){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lake_PackageConfig_lintDriver___proj___redArg();
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object* v_p_2162_, lean_object* v_n_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_obj_once(&l_Lake_PackageConfig_lintDriver___proj___closed__0, &l_Lake_PackageConfig_lintDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriver___proj___closed__0);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object* v_p_2165_, lean_object* v_n_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lake_PackageConfig_lintDriver___proj(v_p_2165_, v_n_2166_);
lean_dec(v_n_2166_);
lean_dec(v_p_2165_);
return v_res_2167_;
}
}
lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___redArg(){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = lean_obj_once(&l_Lake_PackageConfig_lintDriver___proj___closed__0, &l_Lake_PackageConfig_lintDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriver___proj___closed__0);
return v___x_2169_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_lintDriver_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2170_;
v_res_2170_ = l_Lake_PackageConfig_lintDriver_instConfigField___redArg();
stack->m_obj
 = v_res_2170_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___redArg___boxed(lean_object* v___dummy_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lake_PackageConfig_lintDriver_instConfigField___redArg();
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object* v_p_2173_, lean_object* v_n_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = lean_obj_once(&l_Lake_PackageConfig_lintDriver___proj___closed__0, &l_Lake_PackageConfig_lintDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriver___proj___closed__0);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object* v_p_2176_, lean_object* v_n_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lake_PackageConfig_lintDriver_instConfigField(v_p_2176_, v_n_2177_);
lean_dec(v_n_2177_);
lean_dec(v_p_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0(lean_object* v_cfg_2179_){
_start:
{
lean_object* v_lintDriverArgs_2180_; 
v_lintDriverArgs_2180_ = lean_ctor_get(v_cfg_2179_, 15);
lean_inc_ref(v_lintDriverArgs_2180_);
return v_lintDriverArgs_2180_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0___boxed(lean_object* v_cfg_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0(v_cfg_2181_);
lean_dec_ref(v_cfg_2181_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__1(lean_object* v_val_2183_, lean_object* v_cfg_2184_){
_start:
{
lean_object* v_toWorkspaceConfig_2185_; lean_object* v_toLeanConfig_2186_; uint8_t v_bootstrap_2187_; lean_object* v_extraDepTargets_2188_; uint8_t v_precompileModules_2189_; lean_object* v_moreGlobalServerArgs_2190_; lean_object* v_srcDir_2191_; lean_object* v_buildDir_2192_; lean_object* v_leanLibDir_2193_; lean_object* v_nativeLibDir_2194_; lean_object* v_binDir_2195_; lean_object* v_irDir_2196_; lean_object* v_releaseRepo_2197_; lean_object* v_buildArchive_2198_; uint8_t v_preferReleaseBuild_2199_; lean_object* v_testDriver_2200_; lean_object* v_testDriverArgs_2201_; lean_object* v_lintDriver_2202_; lean_object* v_version_2203_; lean_object* v_versionTags_2204_; lean_object* v_description_2205_; lean_object* v_keywords_2206_; lean_object* v_homepage_2207_; lean_object* v_license_2208_; lean_object* v_licenseFiles_2209_; lean_object* v_readmeFile_2210_; uint8_t v_reservoir_2211_; lean_object* v_enableArtifactCache_x3f_2212_; lean_object* v_restoreAllArtifacts_x3f_2213_; uint8_t v_libPrefixOnWindows_2214_; uint8_t v_allowImportAll_2215_; lean_object* v_builtinLint_x3f_2216_; lean_object* v_checks_2217_; uint8_t v_fixedToolchain_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
v_toWorkspaceConfig_2185_ = lean_ctor_get(v_cfg_2184_, 0);
v_toLeanConfig_2186_ = lean_ctor_get(v_cfg_2184_, 1);
v_bootstrap_2187_ = lean_ctor_get_uint8(v_cfg_2184_, sizeof(void*)*28);
v_extraDepTargets_2188_ = lean_ctor_get(v_cfg_2184_, 2);
v_precompileModules_2189_ = lean_ctor_get_uint8(v_cfg_2184_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2190_ = lean_ctor_get(v_cfg_2184_, 3);
v_srcDir_2191_ = lean_ctor_get(v_cfg_2184_, 4);
v_buildDir_2192_ = lean_ctor_get(v_cfg_2184_, 5);
v_leanLibDir_2193_ = lean_ctor_get(v_cfg_2184_, 6);
v_nativeLibDir_2194_ = lean_ctor_get(v_cfg_2184_, 7);
v_binDir_2195_ = lean_ctor_get(v_cfg_2184_, 8);
v_irDir_2196_ = lean_ctor_get(v_cfg_2184_, 9);
v_releaseRepo_2197_ = lean_ctor_get(v_cfg_2184_, 10);
v_buildArchive_2198_ = lean_ctor_get(v_cfg_2184_, 11);
v_preferReleaseBuild_2199_ = lean_ctor_get_uint8(v_cfg_2184_, sizeof(void*)*28 + 2);
v_testDriver_2200_ = lean_ctor_get(v_cfg_2184_, 12);
v_testDriverArgs_2201_ = lean_ctor_get(v_cfg_2184_, 13);
v_lintDriver_2202_ = lean_ctor_get(v_cfg_2184_, 14);
v_version_2203_ = lean_ctor_get(v_cfg_2184_, 16);
v_versionTags_2204_ = lean_ctor_get(v_cfg_2184_, 17);
v_description_2205_ = lean_ctor_get(v_cfg_2184_, 18);
v_keywords_2206_ = lean_ctor_get(v_cfg_2184_, 19);
v_homepage_2207_ = lean_ctor_get(v_cfg_2184_, 20);
v_license_2208_ = lean_ctor_get(v_cfg_2184_, 21);
v_licenseFiles_2209_ = lean_ctor_get(v_cfg_2184_, 22);
v_readmeFile_2210_ = lean_ctor_get(v_cfg_2184_, 23);
v_reservoir_2211_ = lean_ctor_get_uint8(v_cfg_2184_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2212_ = lean_ctor_get(v_cfg_2184_, 24);
v_restoreAllArtifacts_x3f_2213_ = lean_ctor_get(v_cfg_2184_, 25);
v_libPrefixOnWindows_2214_ = lean_ctor_get_uint8(v_cfg_2184_, sizeof(void*)*28 + 4);
v_allowImportAll_2215_ = lean_ctor_get_uint8(v_cfg_2184_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2216_ = lean_ctor_get(v_cfg_2184_, 26);
v_checks_2217_ = lean_ctor_get(v_cfg_2184_, 27);
v_fixedToolchain_2218_ = lean_ctor_get_uint8(v_cfg_2184_, sizeof(void*)*28 + 6);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_cfg_2184_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v_cfg_2184_, 15);
lean_dec(v_unused_2226_);
v___x_2220_ = v_cfg_2184_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_checks_2217_);
lean_inc(v_builtinLint_x3f_2216_);
lean_inc(v_restoreAllArtifacts_x3f_2213_);
lean_inc(v_enableArtifactCache_x3f_2212_);
lean_inc(v_readmeFile_2210_);
lean_inc(v_licenseFiles_2209_);
lean_inc(v_license_2208_);
lean_inc(v_homepage_2207_);
lean_inc(v_keywords_2206_);
lean_inc(v_description_2205_);
lean_inc(v_versionTags_2204_);
lean_inc(v_version_2203_);
lean_inc(v_lintDriver_2202_);
lean_inc(v_testDriverArgs_2201_);
lean_inc(v_testDriver_2200_);
lean_inc(v_buildArchive_2198_);
lean_inc(v_releaseRepo_2197_);
lean_inc(v_irDir_2196_);
lean_inc(v_binDir_2195_);
lean_inc(v_nativeLibDir_2194_);
lean_inc(v_leanLibDir_2193_);
lean_inc(v_buildDir_2192_);
lean_inc(v_srcDir_2191_);
lean_inc(v_moreGlobalServerArgs_2190_);
lean_inc(v_extraDepTargets_2188_);
lean_inc(v_toLeanConfig_2186_);
lean_inc(v_toWorkspaceConfig_2185_);
lean_dec(v_cfg_2184_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 15, v_val_2183_);
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_toWorkspaceConfig_2185_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_toLeanConfig_2186_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_extraDepTargets_2188_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_moreGlobalServerArgs_2190_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_srcDir_2191_);
lean_ctor_set(v_reuseFailAlloc_2224_, 5, v_buildDir_2192_);
lean_ctor_set(v_reuseFailAlloc_2224_, 6, v_leanLibDir_2193_);
lean_ctor_set(v_reuseFailAlloc_2224_, 7, v_nativeLibDir_2194_);
lean_ctor_set(v_reuseFailAlloc_2224_, 8, v_binDir_2195_);
lean_ctor_set(v_reuseFailAlloc_2224_, 9, v_irDir_2196_);
lean_ctor_set(v_reuseFailAlloc_2224_, 10, v_releaseRepo_2197_);
lean_ctor_set(v_reuseFailAlloc_2224_, 11, v_buildArchive_2198_);
lean_ctor_set(v_reuseFailAlloc_2224_, 12, v_testDriver_2200_);
lean_ctor_set(v_reuseFailAlloc_2224_, 13, v_testDriverArgs_2201_);
lean_ctor_set(v_reuseFailAlloc_2224_, 14, v_lintDriver_2202_);
lean_ctor_set(v_reuseFailAlloc_2224_, 15, v_val_2183_);
lean_ctor_set(v_reuseFailAlloc_2224_, 16, v_version_2203_);
lean_ctor_set(v_reuseFailAlloc_2224_, 17, v_versionTags_2204_);
lean_ctor_set(v_reuseFailAlloc_2224_, 18, v_description_2205_);
lean_ctor_set(v_reuseFailAlloc_2224_, 19, v_keywords_2206_);
lean_ctor_set(v_reuseFailAlloc_2224_, 20, v_homepage_2207_);
lean_ctor_set(v_reuseFailAlloc_2224_, 21, v_license_2208_);
lean_ctor_set(v_reuseFailAlloc_2224_, 22, v_licenseFiles_2209_);
lean_ctor_set(v_reuseFailAlloc_2224_, 23, v_readmeFile_2210_);
lean_ctor_set(v_reuseFailAlloc_2224_, 24, v_enableArtifactCache_x3f_2212_);
lean_ctor_set(v_reuseFailAlloc_2224_, 25, v_restoreAllArtifacts_x3f_2213_);
lean_ctor_set(v_reuseFailAlloc_2224_, 26, v_builtinLint_x3f_2216_);
lean_ctor_set(v_reuseFailAlloc_2224_, 27, v_checks_2217_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*28, v_bootstrap_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*28 + 1, v_precompileModules_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*28 + 3, v_reservoir_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*28 + 5, v_allowImportAll_2215_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*28 + 6, v_fixedToolchain_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__2(lean_object* v_f_2227_, lean_object* v_cfg_2228_){
_start:
{
lean_object* v_toWorkspaceConfig_2229_; lean_object* v_toLeanConfig_2230_; uint8_t v_bootstrap_2231_; lean_object* v_extraDepTargets_2232_; uint8_t v_precompileModules_2233_; lean_object* v_moreGlobalServerArgs_2234_; lean_object* v_srcDir_2235_; lean_object* v_buildDir_2236_; lean_object* v_leanLibDir_2237_; lean_object* v_nativeLibDir_2238_; lean_object* v_binDir_2239_; lean_object* v_irDir_2240_; lean_object* v_releaseRepo_2241_; lean_object* v_buildArchive_2242_; uint8_t v_preferReleaseBuild_2243_; lean_object* v_testDriver_2244_; lean_object* v_testDriverArgs_2245_; lean_object* v_lintDriver_2246_; lean_object* v_lintDriverArgs_2247_; lean_object* v_version_2248_; lean_object* v_versionTags_2249_; lean_object* v_description_2250_; lean_object* v_keywords_2251_; lean_object* v_homepage_2252_; lean_object* v_license_2253_; lean_object* v_licenseFiles_2254_; lean_object* v_readmeFile_2255_; uint8_t v_reservoir_2256_; lean_object* v_enableArtifactCache_x3f_2257_; lean_object* v_restoreAllArtifacts_x3f_2258_; uint8_t v_libPrefixOnWindows_2259_; uint8_t v_allowImportAll_2260_; lean_object* v_builtinLint_x3f_2261_; lean_object* v_checks_2262_; uint8_t v_fixedToolchain_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2271_; 
v_toWorkspaceConfig_2229_ = lean_ctor_get(v_cfg_2228_, 0);
v_toLeanConfig_2230_ = lean_ctor_get(v_cfg_2228_, 1);
v_bootstrap_2231_ = lean_ctor_get_uint8(v_cfg_2228_, sizeof(void*)*28);
v_extraDepTargets_2232_ = lean_ctor_get(v_cfg_2228_, 2);
v_precompileModules_2233_ = lean_ctor_get_uint8(v_cfg_2228_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2234_ = lean_ctor_get(v_cfg_2228_, 3);
v_srcDir_2235_ = lean_ctor_get(v_cfg_2228_, 4);
v_buildDir_2236_ = lean_ctor_get(v_cfg_2228_, 5);
v_leanLibDir_2237_ = lean_ctor_get(v_cfg_2228_, 6);
v_nativeLibDir_2238_ = lean_ctor_get(v_cfg_2228_, 7);
v_binDir_2239_ = lean_ctor_get(v_cfg_2228_, 8);
v_irDir_2240_ = lean_ctor_get(v_cfg_2228_, 9);
v_releaseRepo_2241_ = lean_ctor_get(v_cfg_2228_, 10);
v_buildArchive_2242_ = lean_ctor_get(v_cfg_2228_, 11);
v_preferReleaseBuild_2243_ = lean_ctor_get_uint8(v_cfg_2228_, sizeof(void*)*28 + 2);
v_testDriver_2244_ = lean_ctor_get(v_cfg_2228_, 12);
v_testDriverArgs_2245_ = lean_ctor_get(v_cfg_2228_, 13);
v_lintDriver_2246_ = lean_ctor_get(v_cfg_2228_, 14);
v_lintDriverArgs_2247_ = lean_ctor_get(v_cfg_2228_, 15);
v_version_2248_ = lean_ctor_get(v_cfg_2228_, 16);
v_versionTags_2249_ = lean_ctor_get(v_cfg_2228_, 17);
v_description_2250_ = lean_ctor_get(v_cfg_2228_, 18);
v_keywords_2251_ = lean_ctor_get(v_cfg_2228_, 19);
v_homepage_2252_ = lean_ctor_get(v_cfg_2228_, 20);
v_license_2253_ = lean_ctor_get(v_cfg_2228_, 21);
v_licenseFiles_2254_ = lean_ctor_get(v_cfg_2228_, 22);
v_readmeFile_2255_ = lean_ctor_get(v_cfg_2228_, 23);
v_reservoir_2256_ = lean_ctor_get_uint8(v_cfg_2228_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2257_ = lean_ctor_get(v_cfg_2228_, 24);
v_restoreAllArtifacts_x3f_2258_ = lean_ctor_get(v_cfg_2228_, 25);
v_libPrefixOnWindows_2259_ = lean_ctor_get_uint8(v_cfg_2228_, sizeof(void*)*28 + 4);
v_allowImportAll_2260_ = lean_ctor_get_uint8(v_cfg_2228_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2261_ = lean_ctor_get(v_cfg_2228_, 26);
v_checks_2262_ = lean_ctor_get(v_cfg_2228_, 27);
v_fixedToolchain_2263_ = lean_ctor_get_uint8(v_cfg_2228_, sizeof(void*)*28 + 6);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_cfg_2228_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2265_ = v_cfg_2228_;
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_checks_2262_);
lean_inc(v_builtinLint_x3f_2261_);
lean_inc(v_restoreAllArtifacts_x3f_2258_);
lean_inc(v_enableArtifactCache_x3f_2257_);
lean_inc(v_readmeFile_2255_);
lean_inc(v_licenseFiles_2254_);
lean_inc(v_license_2253_);
lean_inc(v_homepage_2252_);
lean_inc(v_keywords_2251_);
lean_inc(v_description_2250_);
lean_inc(v_versionTags_2249_);
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
lean_inc(v_toLeanConfig_2230_);
lean_inc(v_toWorkspaceConfig_2229_);
lean_dec(v_cfg_2228_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2267_ = lean_apply_1(v_f_2227_, v_lintDriverArgs_2247_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 15, v___x_2267_);
v___x_2269_ = v___x_2265_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_toWorkspaceConfig_2229_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_toLeanConfig_2230_);
lean_ctor_set(v_reuseFailAlloc_2270_, 2, v_extraDepTargets_2232_);
lean_ctor_set(v_reuseFailAlloc_2270_, 3, v_moreGlobalServerArgs_2234_);
lean_ctor_set(v_reuseFailAlloc_2270_, 4, v_srcDir_2235_);
lean_ctor_set(v_reuseFailAlloc_2270_, 5, v_buildDir_2236_);
lean_ctor_set(v_reuseFailAlloc_2270_, 6, v_leanLibDir_2237_);
lean_ctor_set(v_reuseFailAlloc_2270_, 7, v_nativeLibDir_2238_);
lean_ctor_set(v_reuseFailAlloc_2270_, 8, v_binDir_2239_);
lean_ctor_set(v_reuseFailAlloc_2270_, 9, v_irDir_2240_);
lean_ctor_set(v_reuseFailAlloc_2270_, 10, v_releaseRepo_2241_);
lean_ctor_set(v_reuseFailAlloc_2270_, 11, v_buildArchive_2242_);
lean_ctor_set(v_reuseFailAlloc_2270_, 12, v_testDriver_2244_);
lean_ctor_set(v_reuseFailAlloc_2270_, 13, v_testDriverArgs_2245_);
lean_ctor_set(v_reuseFailAlloc_2270_, 14, v_lintDriver_2246_);
lean_ctor_set(v_reuseFailAlloc_2270_, 15, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2270_, 16, v_version_2248_);
lean_ctor_set(v_reuseFailAlloc_2270_, 17, v_versionTags_2249_);
lean_ctor_set(v_reuseFailAlloc_2270_, 18, v_description_2250_);
lean_ctor_set(v_reuseFailAlloc_2270_, 19, v_keywords_2251_);
lean_ctor_set(v_reuseFailAlloc_2270_, 20, v_homepage_2252_);
lean_ctor_set(v_reuseFailAlloc_2270_, 21, v_license_2253_);
lean_ctor_set(v_reuseFailAlloc_2270_, 22, v_licenseFiles_2254_);
lean_ctor_set(v_reuseFailAlloc_2270_, 23, v_readmeFile_2255_);
lean_ctor_set(v_reuseFailAlloc_2270_, 24, v_enableArtifactCache_x3f_2257_);
lean_ctor_set(v_reuseFailAlloc_2270_, 25, v_restoreAllArtifacts_x3f_2258_);
lean_ctor_set(v_reuseFailAlloc_2270_, 26, v_builtinLint_x3f_2261_);
lean_ctor_set(v_reuseFailAlloc_2270_, 27, v_checks_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*28, v_bootstrap_2231_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*28 + 1, v_precompileModules_2233_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2243_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*28 + 3, v_reservoir_2256_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2259_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*28 + 5, v_allowImportAll_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*28 + 6, v_fixedToolchain_2263_);
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
lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg(){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = ((lean_object*)(l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__3));
return v___x_2281_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_lintDriverArgs___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2282_;
v_res_2282_ = l_Lake_PackageConfig_lintDriverArgs___proj___redArg();
stack->m_obj
 = v_res_2282_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___boxed(lean_object* v___dummy_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lake_PackageConfig_lintDriverArgs___proj___redArg();
return v_res_2284_;
}
}
static lean_object* _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0(void){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lake_PackageConfig_lintDriverArgs___proj___redArg();
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object* v_p_2286_, lean_object* v_n_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_obj_once(&l_Lake_PackageConfig_lintDriverArgs___proj___closed__0, &l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object* v_p_2289_, lean_object* v_n_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2289_, v_n_2290_);
lean_dec(v_n_2290_);
lean_dec(v_p_2289_);
return v_res_2291_;
}
}
lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_obj_once(&l_Lake_PackageConfig_lintDriverArgs___proj___closed__0, &l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0);
return v___x_2293_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2294_;
v_res_2294_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg();
stack->m_obj
 = v_res_2294_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg___boxed(lean_object* v___dummy_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg();
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object* v_p_2297_, lean_object* v_n_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_obj_once(&l_Lake_PackageConfig_lintDriverArgs___proj___closed__0, &l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object* v_p_2300_, lean_object* v_n_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField(v_p_2300_, v_n_2301_);
lean_dec(v_n_2301_);
lean_dec(v_p_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__0(lean_object* v_cfg_2303_){
_start:
{
lean_object* v_version_2304_; 
v_version_2304_ = lean_ctor_get(v_cfg_2303_, 16);
lean_inc_ref(v_version_2304_);
return v_version_2304_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__0___boxed(lean_object* v_cfg_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lake_PackageConfig_version___proj___redArg___lam__0(v_cfg_2305_);
lean_dec_ref(v_cfg_2305_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__1(lean_object* v_val_2307_, lean_object* v_cfg_2308_){
_start:
{
lean_object* v_toWorkspaceConfig_2309_; lean_object* v_toLeanConfig_2310_; uint8_t v_bootstrap_2311_; lean_object* v_extraDepTargets_2312_; uint8_t v_precompileModules_2313_; lean_object* v_moreGlobalServerArgs_2314_; lean_object* v_srcDir_2315_; lean_object* v_buildDir_2316_; lean_object* v_leanLibDir_2317_; lean_object* v_nativeLibDir_2318_; lean_object* v_binDir_2319_; lean_object* v_irDir_2320_; lean_object* v_releaseRepo_2321_; lean_object* v_buildArchive_2322_; uint8_t v_preferReleaseBuild_2323_; lean_object* v_testDriver_2324_; lean_object* v_testDriverArgs_2325_; lean_object* v_lintDriver_2326_; lean_object* v_lintDriverArgs_2327_; lean_object* v_versionTags_2328_; lean_object* v_description_2329_; lean_object* v_keywords_2330_; lean_object* v_homepage_2331_; lean_object* v_license_2332_; lean_object* v_licenseFiles_2333_; lean_object* v_readmeFile_2334_; uint8_t v_reservoir_2335_; lean_object* v_enableArtifactCache_x3f_2336_; lean_object* v_restoreAllArtifacts_x3f_2337_; uint8_t v_libPrefixOnWindows_2338_; uint8_t v_allowImportAll_2339_; lean_object* v_builtinLint_x3f_2340_; lean_object* v_checks_2341_; uint8_t v_fixedToolchain_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
v_toWorkspaceConfig_2309_ = lean_ctor_get(v_cfg_2308_, 0);
v_toLeanConfig_2310_ = lean_ctor_get(v_cfg_2308_, 1);
v_bootstrap_2311_ = lean_ctor_get_uint8(v_cfg_2308_, sizeof(void*)*28);
v_extraDepTargets_2312_ = lean_ctor_get(v_cfg_2308_, 2);
v_precompileModules_2313_ = lean_ctor_get_uint8(v_cfg_2308_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2314_ = lean_ctor_get(v_cfg_2308_, 3);
v_srcDir_2315_ = lean_ctor_get(v_cfg_2308_, 4);
v_buildDir_2316_ = lean_ctor_get(v_cfg_2308_, 5);
v_leanLibDir_2317_ = lean_ctor_get(v_cfg_2308_, 6);
v_nativeLibDir_2318_ = lean_ctor_get(v_cfg_2308_, 7);
v_binDir_2319_ = lean_ctor_get(v_cfg_2308_, 8);
v_irDir_2320_ = lean_ctor_get(v_cfg_2308_, 9);
v_releaseRepo_2321_ = lean_ctor_get(v_cfg_2308_, 10);
v_buildArchive_2322_ = lean_ctor_get(v_cfg_2308_, 11);
v_preferReleaseBuild_2323_ = lean_ctor_get_uint8(v_cfg_2308_, sizeof(void*)*28 + 2);
v_testDriver_2324_ = lean_ctor_get(v_cfg_2308_, 12);
v_testDriverArgs_2325_ = lean_ctor_get(v_cfg_2308_, 13);
v_lintDriver_2326_ = lean_ctor_get(v_cfg_2308_, 14);
v_lintDriverArgs_2327_ = lean_ctor_get(v_cfg_2308_, 15);
v_versionTags_2328_ = lean_ctor_get(v_cfg_2308_, 17);
v_description_2329_ = lean_ctor_get(v_cfg_2308_, 18);
v_keywords_2330_ = lean_ctor_get(v_cfg_2308_, 19);
v_homepage_2331_ = lean_ctor_get(v_cfg_2308_, 20);
v_license_2332_ = lean_ctor_get(v_cfg_2308_, 21);
v_licenseFiles_2333_ = lean_ctor_get(v_cfg_2308_, 22);
v_readmeFile_2334_ = lean_ctor_get(v_cfg_2308_, 23);
v_reservoir_2335_ = lean_ctor_get_uint8(v_cfg_2308_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2336_ = lean_ctor_get(v_cfg_2308_, 24);
v_restoreAllArtifacts_x3f_2337_ = lean_ctor_get(v_cfg_2308_, 25);
v_libPrefixOnWindows_2338_ = lean_ctor_get_uint8(v_cfg_2308_, sizeof(void*)*28 + 4);
v_allowImportAll_2339_ = lean_ctor_get_uint8(v_cfg_2308_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2340_ = lean_ctor_get(v_cfg_2308_, 26);
v_checks_2341_ = lean_ctor_get(v_cfg_2308_, 27);
v_fixedToolchain_2342_ = lean_ctor_get_uint8(v_cfg_2308_, sizeof(void*)*28 + 6);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_cfg_2308_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; 
v_unused_2350_ = lean_ctor_get(v_cfg_2308_, 16);
lean_dec(v_unused_2350_);
v___x_2344_ = v_cfg_2308_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_checks_2341_);
lean_inc(v_builtinLint_x3f_2340_);
lean_inc(v_restoreAllArtifacts_x3f_2337_);
lean_inc(v_enableArtifactCache_x3f_2336_);
lean_inc(v_readmeFile_2334_);
lean_inc(v_licenseFiles_2333_);
lean_inc(v_license_2332_);
lean_inc(v_homepage_2331_);
lean_inc(v_keywords_2330_);
lean_inc(v_description_2329_);
lean_inc(v_versionTags_2328_);
lean_inc(v_lintDriverArgs_2327_);
lean_inc(v_lintDriver_2326_);
lean_inc(v_testDriverArgs_2325_);
lean_inc(v_testDriver_2324_);
lean_inc(v_buildArchive_2322_);
lean_inc(v_releaseRepo_2321_);
lean_inc(v_irDir_2320_);
lean_inc(v_binDir_2319_);
lean_inc(v_nativeLibDir_2318_);
lean_inc(v_leanLibDir_2317_);
lean_inc(v_buildDir_2316_);
lean_inc(v_srcDir_2315_);
lean_inc(v_moreGlobalServerArgs_2314_);
lean_inc(v_extraDepTargets_2312_);
lean_inc(v_toLeanConfig_2310_);
lean_inc(v_toWorkspaceConfig_2309_);
lean_dec(v_cfg_2308_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 16, v_val_2307_);
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_toWorkspaceConfig_2309_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_toLeanConfig_2310_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_extraDepTargets_2312_);
lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_moreGlobalServerArgs_2314_);
lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_srcDir_2315_);
lean_ctor_set(v_reuseFailAlloc_2348_, 5, v_buildDir_2316_);
lean_ctor_set(v_reuseFailAlloc_2348_, 6, v_leanLibDir_2317_);
lean_ctor_set(v_reuseFailAlloc_2348_, 7, v_nativeLibDir_2318_);
lean_ctor_set(v_reuseFailAlloc_2348_, 8, v_binDir_2319_);
lean_ctor_set(v_reuseFailAlloc_2348_, 9, v_irDir_2320_);
lean_ctor_set(v_reuseFailAlloc_2348_, 10, v_releaseRepo_2321_);
lean_ctor_set(v_reuseFailAlloc_2348_, 11, v_buildArchive_2322_);
lean_ctor_set(v_reuseFailAlloc_2348_, 12, v_testDriver_2324_);
lean_ctor_set(v_reuseFailAlloc_2348_, 13, v_testDriverArgs_2325_);
lean_ctor_set(v_reuseFailAlloc_2348_, 14, v_lintDriver_2326_);
lean_ctor_set(v_reuseFailAlloc_2348_, 15, v_lintDriverArgs_2327_);
lean_ctor_set(v_reuseFailAlloc_2348_, 16, v_val_2307_);
lean_ctor_set(v_reuseFailAlloc_2348_, 17, v_versionTags_2328_);
lean_ctor_set(v_reuseFailAlloc_2348_, 18, v_description_2329_);
lean_ctor_set(v_reuseFailAlloc_2348_, 19, v_keywords_2330_);
lean_ctor_set(v_reuseFailAlloc_2348_, 20, v_homepage_2331_);
lean_ctor_set(v_reuseFailAlloc_2348_, 21, v_license_2332_);
lean_ctor_set(v_reuseFailAlloc_2348_, 22, v_licenseFiles_2333_);
lean_ctor_set(v_reuseFailAlloc_2348_, 23, v_readmeFile_2334_);
lean_ctor_set(v_reuseFailAlloc_2348_, 24, v_enableArtifactCache_x3f_2336_);
lean_ctor_set(v_reuseFailAlloc_2348_, 25, v_restoreAllArtifacts_x3f_2337_);
lean_ctor_set(v_reuseFailAlloc_2348_, 26, v_builtinLint_x3f_2340_);
lean_ctor_set(v_reuseFailAlloc_2348_, 27, v_checks_2341_);
lean_ctor_set_uint8(v_reuseFailAlloc_2348_, sizeof(void*)*28, v_bootstrap_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2348_, sizeof(void*)*28 + 1, v_precompileModules_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2348_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2323_);
lean_ctor_set_uint8(v_reuseFailAlloc_2348_, sizeof(void*)*28 + 3, v_reservoir_2335_);
lean_ctor_set_uint8(v_reuseFailAlloc_2348_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2338_);
lean_ctor_set_uint8(v_reuseFailAlloc_2348_, sizeof(void*)*28 + 5, v_allowImportAll_2339_);
lean_ctor_set_uint8(v_reuseFailAlloc_2348_, sizeof(void*)*28 + 6, v_fixedToolchain_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__2(lean_object* v_f_2351_, lean_object* v_cfg_2352_){
_start:
{
lean_object* v_toWorkspaceConfig_2353_; lean_object* v_toLeanConfig_2354_; uint8_t v_bootstrap_2355_; lean_object* v_extraDepTargets_2356_; uint8_t v_precompileModules_2357_; lean_object* v_moreGlobalServerArgs_2358_; lean_object* v_srcDir_2359_; lean_object* v_buildDir_2360_; lean_object* v_leanLibDir_2361_; lean_object* v_nativeLibDir_2362_; lean_object* v_binDir_2363_; lean_object* v_irDir_2364_; lean_object* v_releaseRepo_2365_; lean_object* v_buildArchive_2366_; uint8_t v_preferReleaseBuild_2367_; lean_object* v_testDriver_2368_; lean_object* v_testDriverArgs_2369_; lean_object* v_lintDriver_2370_; lean_object* v_lintDriverArgs_2371_; lean_object* v_version_2372_; lean_object* v_versionTags_2373_; lean_object* v_description_2374_; lean_object* v_keywords_2375_; lean_object* v_homepage_2376_; lean_object* v_license_2377_; lean_object* v_licenseFiles_2378_; lean_object* v_readmeFile_2379_; uint8_t v_reservoir_2380_; lean_object* v_enableArtifactCache_x3f_2381_; lean_object* v_restoreAllArtifacts_x3f_2382_; uint8_t v_libPrefixOnWindows_2383_; uint8_t v_allowImportAll_2384_; lean_object* v_builtinLint_x3f_2385_; lean_object* v_checks_2386_; uint8_t v_fixedToolchain_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2395_; 
v_toWorkspaceConfig_2353_ = lean_ctor_get(v_cfg_2352_, 0);
v_toLeanConfig_2354_ = lean_ctor_get(v_cfg_2352_, 1);
v_bootstrap_2355_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*28);
v_extraDepTargets_2356_ = lean_ctor_get(v_cfg_2352_, 2);
v_precompileModules_2357_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2358_ = lean_ctor_get(v_cfg_2352_, 3);
v_srcDir_2359_ = lean_ctor_get(v_cfg_2352_, 4);
v_buildDir_2360_ = lean_ctor_get(v_cfg_2352_, 5);
v_leanLibDir_2361_ = lean_ctor_get(v_cfg_2352_, 6);
v_nativeLibDir_2362_ = lean_ctor_get(v_cfg_2352_, 7);
v_binDir_2363_ = lean_ctor_get(v_cfg_2352_, 8);
v_irDir_2364_ = lean_ctor_get(v_cfg_2352_, 9);
v_releaseRepo_2365_ = lean_ctor_get(v_cfg_2352_, 10);
v_buildArchive_2366_ = lean_ctor_get(v_cfg_2352_, 11);
v_preferReleaseBuild_2367_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*28 + 2);
v_testDriver_2368_ = lean_ctor_get(v_cfg_2352_, 12);
v_testDriverArgs_2369_ = lean_ctor_get(v_cfg_2352_, 13);
v_lintDriver_2370_ = lean_ctor_get(v_cfg_2352_, 14);
v_lintDriverArgs_2371_ = lean_ctor_get(v_cfg_2352_, 15);
v_version_2372_ = lean_ctor_get(v_cfg_2352_, 16);
v_versionTags_2373_ = lean_ctor_get(v_cfg_2352_, 17);
v_description_2374_ = lean_ctor_get(v_cfg_2352_, 18);
v_keywords_2375_ = lean_ctor_get(v_cfg_2352_, 19);
v_homepage_2376_ = lean_ctor_get(v_cfg_2352_, 20);
v_license_2377_ = lean_ctor_get(v_cfg_2352_, 21);
v_licenseFiles_2378_ = lean_ctor_get(v_cfg_2352_, 22);
v_readmeFile_2379_ = lean_ctor_get(v_cfg_2352_, 23);
v_reservoir_2380_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2381_ = lean_ctor_get(v_cfg_2352_, 24);
v_restoreAllArtifacts_x3f_2382_ = lean_ctor_get(v_cfg_2352_, 25);
v_libPrefixOnWindows_2383_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*28 + 4);
v_allowImportAll_2384_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2385_ = lean_ctor_get(v_cfg_2352_, 26);
v_checks_2386_ = lean_ctor_get(v_cfg_2352_, 27);
v_fixedToolchain_2387_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*28 + 6);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_cfg_2352_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2389_ = v_cfg_2352_;
v_isShared_2390_ = v_isSharedCheck_2395_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_checks_2386_);
lean_inc(v_builtinLint_x3f_2385_);
lean_inc(v_restoreAllArtifacts_x3f_2382_);
lean_inc(v_enableArtifactCache_x3f_2381_);
lean_inc(v_readmeFile_2379_);
lean_inc(v_licenseFiles_2378_);
lean_inc(v_license_2377_);
lean_inc(v_homepage_2376_);
lean_inc(v_keywords_2375_);
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
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2395_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2391_ = lean_apply_1(v_f_2351_, v_version_2372_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 16, v___x_2391_);
v___x_2393_ = v___x_2389_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_toWorkspaceConfig_2353_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_toLeanConfig_2354_);
lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_extraDepTargets_2356_);
lean_ctor_set(v_reuseFailAlloc_2394_, 3, v_moreGlobalServerArgs_2358_);
lean_ctor_set(v_reuseFailAlloc_2394_, 4, v_srcDir_2359_);
lean_ctor_set(v_reuseFailAlloc_2394_, 5, v_buildDir_2360_);
lean_ctor_set(v_reuseFailAlloc_2394_, 6, v_leanLibDir_2361_);
lean_ctor_set(v_reuseFailAlloc_2394_, 7, v_nativeLibDir_2362_);
lean_ctor_set(v_reuseFailAlloc_2394_, 8, v_binDir_2363_);
lean_ctor_set(v_reuseFailAlloc_2394_, 9, v_irDir_2364_);
lean_ctor_set(v_reuseFailAlloc_2394_, 10, v_releaseRepo_2365_);
lean_ctor_set(v_reuseFailAlloc_2394_, 11, v_buildArchive_2366_);
lean_ctor_set(v_reuseFailAlloc_2394_, 12, v_testDriver_2368_);
lean_ctor_set(v_reuseFailAlloc_2394_, 13, v_testDriverArgs_2369_);
lean_ctor_set(v_reuseFailAlloc_2394_, 14, v_lintDriver_2370_);
lean_ctor_set(v_reuseFailAlloc_2394_, 15, v_lintDriverArgs_2371_);
lean_ctor_set(v_reuseFailAlloc_2394_, 16, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2394_, 17, v_versionTags_2373_);
lean_ctor_set(v_reuseFailAlloc_2394_, 18, v_description_2374_);
lean_ctor_set(v_reuseFailAlloc_2394_, 19, v_keywords_2375_);
lean_ctor_set(v_reuseFailAlloc_2394_, 20, v_homepage_2376_);
lean_ctor_set(v_reuseFailAlloc_2394_, 21, v_license_2377_);
lean_ctor_set(v_reuseFailAlloc_2394_, 22, v_licenseFiles_2378_);
lean_ctor_set(v_reuseFailAlloc_2394_, 23, v_readmeFile_2379_);
lean_ctor_set(v_reuseFailAlloc_2394_, 24, v_enableArtifactCache_x3f_2381_);
lean_ctor_set(v_reuseFailAlloc_2394_, 25, v_restoreAllArtifacts_x3f_2382_);
lean_ctor_set(v_reuseFailAlloc_2394_, 26, v_builtinLint_x3f_2385_);
lean_ctor_set(v_reuseFailAlloc_2394_, 27, v_checks_2386_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*28, v_bootstrap_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*28 + 1, v_precompileModules_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*28 + 3, v_reservoir_2380_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2383_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*28 + 5, v_allowImportAll_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*28 + 6, v_fixedToolchain_2387_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__3(lean_object* v_x_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__4));
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__3___boxed(lean_object* v_x_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lake_PackageConfig_version___proj___redArg___lam__3(v_x_2398_);
lean_dec_ref(v_x_2398_);
return v_res_2399_;
}
}
lean_object* l_Lake_PackageConfig_version___proj___redArg(){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___redArg___closed__4));
return v___x_2410_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_version___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2411_;
v_res_2411_ = l_Lake_PackageConfig_version___proj___redArg();
stack->m_obj
 = v_res_2411_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___boxed(lean_object* v___dummy_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lake_PackageConfig_version___proj___redArg();
return v_res_2413_;
}
}
static lean_object* _init_l_Lake_PackageConfig_version___proj___closed__0(void){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lake_PackageConfig_version___proj___redArg();
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object* v_p_2415_, lean_object* v_n_2416_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_obj_once(&l_Lake_PackageConfig_version___proj___closed__0, &l_Lake_PackageConfig_version___proj___closed__0_once, _init_l_Lake_PackageConfig_version___proj___closed__0);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object* v_p_2418_, lean_object* v_n_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lake_PackageConfig_version___proj(v_p_2418_, v_n_2419_);
lean_dec(v_n_2419_);
lean_dec(v_p_2418_);
return v_res_2420_;
}
}
lean_object* l_Lake_PackageConfig_version_instConfigField___redArg(){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_obj_once(&l_Lake_PackageConfig_version___proj___closed__0, &l_Lake_PackageConfig_version___proj___closed__0_once, _init_l_Lake_PackageConfig_version___proj___closed__0);
return v___x_2422_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_version_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2423_;
v_res_2423_ = l_Lake_PackageConfig_version_instConfigField___redArg();
stack->m_obj
 = v_res_2423_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___redArg___boxed(lean_object* v___dummy_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lake_PackageConfig_version_instConfigField___redArg();
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object* v_p_2426_, lean_object* v_n_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_obj_once(&l_Lake_PackageConfig_version___proj___closed__0, &l_Lake_PackageConfig_version___proj___closed__0_once, _init_l_Lake_PackageConfig_version___proj___closed__0);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object* v_p_2429_, lean_object* v_n_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lake_PackageConfig_version_instConfigField(v_p_2429_, v_n_2430_);
lean_dec(v_n_2430_);
lean_dec(v_p_2429_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__0(lean_object* v_cfg_2432_){
_start:
{
lean_object* v_versionTags_2433_; 
v_versionTags_2433_ = lean_ctor_get(v_cfg_2432_, 17);
lean_inc_ref(v_versionTags_2433_);
return v_versionTags_2433_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__0___boxed(lean_object* v_cfg_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lake_PackageConfig_versionTags___proj___redArg___lam__0(v_cfg_2434_);
lean_dec_ref(v_cfg_2434_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__1(lean_object* v_val_2436_, lean_object* v_cfg_2437_){
_start:
{
lean_object* v_toWorkspaceConfig_2438_; lean_object* v_toLeanConfig_2439_; uint8_t v_bootstrap_2440_; lean_object* v_extraDepTargets_2441_; uint8_t v_precompileModules_2442_; lean_object* v_moreGlobalServerArgs_2443_; lean_object* v_srcDir_2444_; lean_object* v_buildDir_2445_; lean_object* v_leanLibDir_2446_; lean_object* v_nativeLibDir_2447_; lean_object* v_binDir_2448_; lean_object* v_irDir_2449_; lean_object* v_releaseRepo_2450_; lean_object* v_buildArchive_2451_; uint8_t v_preferReleaseBuild_2452_; lean_object* v_testDriver_2453_; lean_object* v_testDriverArgs_2454_; lean_object* v_lintDriver_2455_; lean_object* v_lintDriverArgs_2456_; lean_object* v_version_2457_; lean_object* v_description_2458_; lean_object* v_keywords_2459_; lean_object* v_homepage_2460_; lean_object* v_license_2461_; lean_object* v_licenseFiles_2462_; lean_object* v_readmeFile_2463_; uint8_t v_reservoir_2464_; lean_object* v_enableArtifactCache_x3f_2465_; lean_object* v_restoreAllArtifacts_x3f_2466_; uint8_t v_libPrefixOnWindows_2467_; uint8_t v_allowImportAll_2468_; lean_object* v_builtinLint_x3f_2469_; lean_object* v_checks_2470_; uint8_t v_fixedToolchain_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
v_toWorkspaceConfig_2438_ = lean_ctor_get(v_cfg_2437_, 0);
v_toLeanConfig_2439_ = lean_ctor_get(v_cfg_2437_, 1);
v_bootstrap_2440_ = lean_ctor_get_uint8(v_cfg_2437_, sizeof(void*)*28);
v_extraDepTargets_2441_ = lean_ctor_get(v_cfg_2437_, 2);
v_precompileModules_2442_ = lean_ctor_get_uint8(v_cfg_2437_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2443_ = lean_ctor_get(v_cfg_2437_, 3);
v_srcDir_2444_ = lean_ctor_get(v_cfg_2437_, 4);
v_buildDir_2445_ = lean_ctor_get(v_cfg_2437_, 5);
v_leanLibDir_2446_ = lean_ctor_get(v_cfg_2437_, 6);
v_nativeLibDir_2447_ = lean_ctor_get(v_cfg_2437_, 7);
v_binDir_2448_ = lean_ctor_get(v_cfg_2437_, 8);
v_irDir_2449_ = lean_ctor_get(v_cfg_2437_, 9);
v_releaseRepo_2450_ = lean_ctor_get(v_cfg_2437_, 10);
v_buildArchive_2451_ = lean_ctor_get(v_cfg_2437_, 11);
v_preferReleaseBuild_2452_ = lean_ctor_get_uint8(v_cfg_2437_, sizeof(void*)*28 + 2);
v_testDriver_2453_ = lean_ctor_get(v_cfg_2437_, 12);
v_testDriverArgs_2454_ = lean_ctor_get(v_cfg_2437_, 13);
v_lintDriver_2455_ = lean_ctor_get(v_cfg_2437_, 14);
v_lintDriverArgs_2456_ = lean_ctor_get(v_cfg_2437_, 15);
v_version_2457_ = lean_ctor_get(v_cfg_2437_, 16);
v_description_2458_ = lean_ctor_get(v_cfg_2437_, 18);
v_keywords_2459_ = lean_ctor_get(v_cfg_2437_, 19);
v_homepage_2460_ = lean_ctor_get(v_cfg_2437_, 20);
v_license_2461_ = lean_ctor_get(v_cfg_2437_, 21);
v_licenseFiles_2462_ = lean_ctor_get(v_cfg_2437_, 22);
v_readmeFile_2463_ = lean_ctor_get(v_cfg_2437_, 23);
v_reservoir_2464_ = lean_ctor_get_uint8(v_cfg_2437_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2465_ = lean_ctor_get(v_cfg_2437_, 24);
v_restoreAllArtifacts_x3f_2466_ = lean_ctor_get(v_cfg_2437_, 25);
v_libPrefixOnWindows_2467_ = lean_ctor_get_uint8(v_cfg_2437_, sizeof(void*)*28 + 4);
v_allowImportAll_2468_ = lean_ctor_get_uint8(v_cfg_2437_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2469_ = lean_ctor_get(v_cfg_2437_, 26);
v_checks_2470_ = lean_ctor_get(v_cfg_2437_, 27);
v_fixedToolchain_2471_ = lean_ctor_get_uint8(v_cfg_2437_, sizeof(void*)*28 + 6);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_cfg_2437_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v_cfg_2437_, 17);
lean_dec(v_unused_2479_);
v___x_2473_ = v_cfg_2437_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_checks_2470_);
lean_inc(v_builtinLint_x3f_2469_);
lean_inc(v_restoreAllArtifacts_x3f_2466_);
lean_inc(v_enableArtifactCache_x3f_2465_);
lean_inc(v_readmeFile_2463_);
lean_inc(v_licenseFiles_2462_);
lean_inc(v_license_2461_);
lean_inc(v_homepage_2460_);
lean_inc(v_keywords_2459_);
lean_inc(v_description_2458_);
lean_inc(v_version_2457_);
lean_inc(v_lintDriverArgs_2456_);
lean_inc(v_lintDriver_2455_);
lean_inc(v_testDriverArgs_2454_);
lean_inc(v_testDriver_2453_);
lean_inc(v_buildArchive_2451_);
lean_inc(v_releaseRepo_2450_);
lean_inc(v_irDir_2449_);
lean_inc(v_binDir_2448_);
lean_inc(v_nativeLibDir_2447_);
lean_inc(v_leanLibDir_2446_);
lean_inc(v_buildDir_2445_);
lean_inc(v_srcDir_2444_);
lean_inc(v_moreGlobalServerArgs_2443_);
lean_inc(v_extraDepTargets_2441_);
lean_inc(v_toLeanConfig_2439_);
lean_inc(v_toWorkspaceConfig_2438_);
lean_dec(v_cfg_2437_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 17, v_val_2436_);
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_toWorkspaceConfig_2438_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_toLeanConfig_2439_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_extraDepTargets_2441_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_moreGlobalServerArgs_2443_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_srcDir_2444_);
lean_ctor_set(v_reuseFailAlloc_2477_, 5, v_buildDir_2445_);
lean_ctor_set(v_reuseFailAlloc_2477_, 6, v_leanLibDir_2446_);
lean_ctor_set(v_reuseFailAlloc_2477_, 7, v_nativeLibDir_2447_);
lean_ctor_set(v_reuseFailAlloc_2477_, 8, v_binDir_2448_);
lean_ctor_set(v_reuseFailAlloc_2477_, 9, v_irDir_2449_);
lean_ctor_set(v_reuseFailAlloc_2477_, 10, v_releaseRepo_2450_);
lean_ctor_set(v_reuseFailAlloc_2477_, 11, v_buildArchive_2451_);
lean_ctor_set(v_reuseFailAlloc_2477_, 12, v_testDriver_2453_);
lean_ctor_set(v_reuseFailAlloc_2477_, 13, v_testDriverArgs_2454_);
lean_ctor_set(v_reuseFailAlloc_2477_, 14, v_lintDriver_2455_);
lean_ctor_set(v_reuseFailAlloc_2477_, 15, v_lintDriverArgs_2456_);
lean_ctor_set(v_reuseFailAlloc_2477_, 16, v_version_2457_);
lean_ctor_set(v_reuseFailAlloc_2477_, 17, v_val_2436_);
lean_ctor_set(v_reuseFailAlloc_2477_, 18, v_description_2458_);
lean_ctor_set(v_reuseFailAlloc_2477_, 19, v_keywords_2459_);
lean_ctor_set(v_reuseFailAlloc_2477_, 20, v_homepage_2460_);
lean_ctor_set(v_reuseFailAlloc_2477_, 21, v_license_2461_);
lean_ctor_set(v_reuseFailAlloc_2477_, 22, v_licenseFiles_2462_);
lean_ctor_set(v_reuseFailAlloc_2477_, 23, v_readmeFile_2463_);
lean_ctor_set(v_reuseFailAlloc_2477_, 24, v_enableArtifactCache_x3f_2465_);
lean_ctor_set(v_reuseFailAlloc_2477_, 25, v_restoreAllArtifacts_x3f_2466_);
lean_ctor_set(v_reuseFailAlloc_2477_, 26, v_builtinLint_x3f_2469_);
lean_ctor_set(v_reuseFailAlloc_2477_, 27, v_checks_2470_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*28, v_bootstrap_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*28 + 1, v_precompileModules_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*28 + 3, v_reservoir_2464_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2467_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*28 + 5, v_allowImportAll_2468_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*28 + 6, v_fixedToolchain_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__2(lean_object* v_f_2480_, lean_object* v_cfg_2481_){
_start:
{
lean_object* v_toWorkspaceConfig_2482_; lean_object* v_toLeanConfig_2483_; uint8_t v_bootstrap_2484_; lean_object* v_extraDepTargets_2485_; uint8_t v_precompileModules_2486_; lean_object* v_moreGlobalServerArgs_2487_; lean_object* v_srcDir_2488_; lean_object* v_buildDir_2489_; lean_object* v_leanLibDir_2490_; lean_object* v_nativeLibDir_2491_; lean_object* v_binDir_2492_; lean_object* v_irDir_2493_; lean_object* v_releaseRepo_2494_; lean_object* v_buildArchive_2495_; uint8_t v_preferReleaseBuild_2496_; lean_object* v_testDriver_2497_; lean_object* v_testDriverArgs_2498_; lean_object* v_lintDriver_2499_; lean_object* v_lintDriverArgs_2500_; lean_object* v_version_2501_; lean_object* v_versionTags_2502_; lean_object* v_description_2503_; lean_object* v_keywords_2504_; lean_object* v_homepage_2505_; lean_object* v_license_2506_; lean_object* v_licenseFiles_2507_; lean_object* v_readmeFile_2508_; uint8_t v_reservoir_2509_; lean_object* v_enableArtifactCache_x3f_2510_; lean_object* v_restoreAllArtifacts_x3f_2511_; uint8_t v_libPrefixOnWindows_2512_; uint8_t v_allowImportAll_2513_; lean_object* v_builtinLint_x3f_2514_; lean_object* v_checks_2515_; uint8_t v_fixedToolchain_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2524_; 
v_toWorkspaceConfig_2482_ = lean_ctor_get(v_cfg_2481_, 0);
v_toLeanConfig_2483_ = lean_ctor_get(v_cfg_2481_, 1);
v_bootstrap_2484_ = lean_ctor_get_uint8(v_cfg_2481_, sizeof(void*)*28);
v_extraDepTargets_2485_ = lean_ctor_get(v_cfg_2481_, 2);
v_precompileModules_2486_ = lean_ctor_get_uint8(v_cfg_2481_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2487_ = lean_ctor_get(v_cfg_2481_, 3);
v_srcDir_2488_ = lean_ctor_get(v_cfg_2481_, 4);
v_buildDir_2489_ = lean_ctor_get(v_cfg_2481_, 5);
v_leanLibDir_2490_ = lean_ctor_get(v_cfg_2481_, 6);
v_nativeLibDir_2491_ = lean_ctor_get(v_cfg_2481_, 7);
v_binDir_2492_ = lean_ctor_get(v_cfg_2481_, 8);
v_irDir_2493_ = lean_ctor_get(v_cfg_2481_, 9);
v_releaseRepo_2494_ = lean_ctor_get(v_cfg_2481_, 10);
v_buildArchive_2495_ = lean_ctor_get(v_cfg_2481_, 11);
v_preferReleaseBuild_2496_ = lean_ctor_get_uint8(v_cfg_2481_, sizeof(void*)*28 + 2);
v_testDriver_2497_ = lean_ctor_get(v_cfg_2481_, 12);
v_testDriverArgs_2498_ = lean_ctor_get(v_cfg_2481_, 13);
v_lintDriver_2499_ = lean_ctor_get(v_cfg_2481_, 14);
v_lintDriverArgs_2500_ = lean_ctor_get(v_cfg_2481_, 15);
v_version_2501_ = lean_ctor_get(v_cfg_2481_, 16);
v_versionTags_2502_ = lean_ctor_get(v_cfg_2481_, 17);
v_description_2503_ = lean_ctor_get(v_cfg_2481_, 18);
v_keywords_2504_ = lean_ctor_get(v_cfg_2481_, 19);
v_homepage_2505_ = lean_ctor_get(v_cfg_2481_, 20);
v_license_2506_ = lean_ctor_get(v_cfg_2481_, 21);
v_licenseFiles_2507_ = lean_ctor_get(v_cfg_2481_, 22);
v_readmeFile_2508_ = lean_ctor_get(v_cfg_2481_, 23);
v_reservoir_2509_ = lean_ctor_get_uint8(v_cfg_2481_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2510_ = lean_ctor_get(v_cfg_2481_, 24);
v_restoreAllArtifacts_x3f_2511_ = lean_ctor_get(v_cfg_2481_, 25);
v_libPrefixOnWindows_2512_ = lean_ctor_get_uint8(v_cfg_2481_, sizeof(void*)*28 + 4);
v_allowImportAll_2513_ = lean_ctor_get_uint8(v_cfg_2481_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2514_ = lean_ctor_get(v_cfg_2481_, 26);
v_checks_2515_ = lean_ctor_get(v_cfg_2481_, 27);
v_fixedToolchain_2516_ = lean_ctor_get_uint8(v_cfg_2481_, sizeof(void*)*28 + 6);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_cfg_2481_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2518_ = v_cfg_2481_;
v_isShared_2519_ = v_isSharedCheck_2524_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_checks_2515_);
lean_inc(v_builtinLint_x3f_2514_);
lean_inc(v_restoreAllArtifacts_x3f_2511_);
lean_inc(v_enableArtifactCache_x3f_2510_);
lean_inc(v_readmeFile_2508_);
lean_inc(v_licenseFiles_2507_);
lean_inc(v_license_2506_);
lean_inc(v_homepage_2505_);
lean_inc(v_keywords_2504_);
lean_inc(v_description_2503_);
lean_inc(v_versionTags_2502_);
lean_inc(v_version_2501_);
lean_inc(v_lintDriverArgs_2500_);
lean_inc(v_lintDriver_2499_);
lean_inc(v_testDriverArgs_2498_);
lean_inc(v_testDriver_2497_);
lean_inc(v_buildArchive_2495_);
lean_inc(v_releaseRepo_2494_);
lean_inc(v_irDir_2493_);
lean_inc(v_binDir_2492_);
lean_inc(v_nativeLibDir_2491_);
lean_inc(v_leanLibDir_2490_);
lean_inc(v_buildDir_2489_);
lean_inc(v_srcDir_2488_);
lean_inc(v_moreGlobalServerArgs_2487_);
lean_inc(v_extraDepTargets_2485_);
lean_inc(v_toLeanConfig_2483_);
lean_inc(v_toWorkspaceConfig_2482_);
lean_dec(v_cfg_2481_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2524_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2520_ = lean_apply_1(v_f_2480_, v_versionTags_2502_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 17, v___x_2520_);
v___x_2522_ = v___x_2518_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_toWorkspaceConfig_2482_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_toLeanConfig_2483_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_extraDepTargets_2485_);
lean_ctor_set(v_reuseFailAlloc_2523_, 3, v_moreGlobalServerArgs_2487_);
lean_ctor_set(v_reuseFailAlloc_2523_, 4, v_srcDir_2488_);
lean_ctor_set(v_reuseFailAlloc_2523_, 5, v_buildDir_2489_);
lean_ctor_set(v_reuseFailAlloc_2523_, 6, v_leanLibDir_2490_);
lean_ctor_set(v_reuseFailAlloc_2523_, 7, v_nativeLibDir_2491_);
lean_ctor_set(v_reuseFailAlloc_2523_, 8, v_binDir_2492_);
lean_ctor_set(v_reuseFailAlloc_2523_, 9, v_irDir_2493_);
lean_ctor_set(v_reuseFailAlloc_2523_, 10, v_releaseRepo_2494_);
lean_ctor_set(v_reuseFailAlloc_2523_, 11, v_buildArchive_2495_);
lean_ctor_set(v_reuseFailAlloc_2523_, 12, v_testDriver_2497_);
lean_ctor_set(v_reuseFailAlloc_2523_, 13, v_testDriverArgs_2498_);
lean_ctor_set(v_reuseFailAlloc_2523_, 14, v_lintDriver_2499_);
lean_ctor_set(v_reuseFailAlloc_2523_, 15, v_lintDriverArgs_2500_);
lean_ctor_set(v_reuseFailAlloc_2523_, 16, v_version_2501_);
lean_ctor_set(v_reuseFailAlloc_2523_, 17, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2523_, 18, v_description_2503_);
lean_ctor_set(v_reuseFailAlloc_2523_, 19, v_keywords_2504_);
lean_ctor_set(v_reuseFailAlloc_2523_, 20, v_homepage_2505_);
lean_ctor_set(v_reuseFailAlloc_2523_, 21, v_license_2506_);
lean_ctor_set(v_reuseFailAlloc_2523_, 22, v_licenseFiles_2507_);
lean_ctor_set(v_reuseFailAlloc_2523_, 23, v_readmeFile_2508_);
lean_ctor_set(v_reuseFailAlloc_2523_, 24, v_enableArtifactCache_x3f_2510_);
lean_ctor_set(v_reuseFailAlloc_2523_, 25, v_restoreAllArtifacts_x3f_2511_);
lean_ctor_set(v_reuseFailAlloc_2523_, 26, v_builtinLint_x3f_2514_);
lean_ctor_set(v_reuseFailAlloc_2523_, 27, v_checks_2515_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*28, v_bootstrap_2484_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*28 + 1, v_precompileModules_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2496_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*28 + 3, v_reservoir_2509_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2512_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*28 + 5, v_allowImportAll_2513_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*28 + 6, v_fixedToolchain_2516_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__3(lean_object* v_x_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lake_defaultVersionTags;
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__3___boxed(lean_object* v_x_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lake_PackageConfig_versionTags___proj___redArg___lam__3(v_x_2527_);
lean_dec_ref(v_x_2527_);
return v_res_2528_;
}
}
lean_object* l_Lake_PackageConfig_versionTags___proj___redArg(){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = ((lean_object*)(l_Lake_PackageConfig_versionTags___proj___redArg___closed__4));
return v___x_2539_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_versionTags___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2540_;
v_res_2540_ = l_Lake_PackageConfig_versionTags___proj___redArg();
stack->m_obj
 = v_res_2540_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___boxed(lean_object* v___dummy_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lake_PackageConfig_versionTags___proj___redArg();
return v_res_2542_;
}
}
static lean_object* _init_l_Lake_PackageConfig_versionTags___proj___closed__0(void){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lake_PackageConfig_versionTags___proj___redArg();
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object* v_p_2544_, lean_object* v_n_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_obj_once(&l_Lake_PackageConfig_versionTags___proj___closed__0, &l_Lake_PackageConfig_versionTags___proj___closed__0_once, _init_l_Lake_PackageConfig_versionTags___proj___closed__0);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object* v_p_2547_, lean_object* v_n_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lake_PackageConfig_versionTags___proj(v_p_2547_, v_n_2548_);
lean_dec(v_n_2548_);
lean_dec(v_p_2547_);
return v_res_2549_;
}
}
lean_object* l_Lake_PackageConfig_versionTags_instConfigField___redArg(){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_obj_once(&l_Lake_PackageConfig_versionTags___proj___closed__0, &l_Lake_PackageConfig_versionTags___proj___closed__0_once, _init_l_Lake_PackageConfig_versionTags___proj___closed__0);
return v___x_2551_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_versionTags_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2552_;
v_res_2552_ = l_Lake_PackageConfig_versionTags_instConfigField___redArg();
stack->m_obj
 = v_res_2552_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___redArg___boxed(lean_object* v___dummy_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lake_PackageConfig_versionTags_instConfigField___redArg();
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object* v_p_2555_, lean_object* v_n_2556_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_obj_once(&l_Lake_PackageConfig_versionTags___proj___closed__0, &l_Lake_PackageConfig_versionTags___proj___closed__0_once, _init_l_Lake_PackageConfig_versionTags___proj___closed__0);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object* v_p_2558_, lean_object* v_n_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lake_PackageConfig_versionTags_instConfigField(v_p_2558_, v_n_2559_);
lean_dec(v_n_2559_);
lean_dec(v_p_2558_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__0(lean_object* v_cfg_2561_){
_start:
{
lean_object* v_description_2562_; 
v_description_2562_ = lean_ctor_get(v_cfg_2561_, 18);
lean_inc_ref(v_description_2562_);
return v_description_2562_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__0___boxed(lean_object* v_cfg_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lake_PackageConfig_description___proj___redArg___lam__0(v_cfg_2563_);
lean_dec_ref(v_cfg_2563_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__1(lean_object* v_val_2565_, lean_object* v_cfg_2566_){
_start:
{
lean_object* v_toWorkspaceConfig_2567_; lean_object* v_toLeanConfig_2568_; uint8_t v_bootstrap_2569_; lean_object* v_extraDepTargets_2570_; uint8_t v_precompileModules_2571_; lean_object* v_moreGlobalServerArgs_2572_; lean_object* v_srcDir_2573_; lean_object* v_buildDir_2574_; lean_object* v_leanLibDir_2575_; lean_object* v_nativeLibDir_2576_; lean_object* v_binDir_2577_; lean_object* v_irDir_2578_; lean_object* v_releaseRepo_2579_; lean_object* v_buildArchive_2580_; uint8_t v_preferReleaseBuild_2581_; lean_object* v_testDriver_2582_; lean_object* v_testDriverArgs_2583_; lean_object* v_lintDriver_2584_; lean_object* v_lintDriverArgs_2585_; lean_object* v_version_2586_; lean_object* v_versionTags_2587_; lean_object* v_keywords_2588_; lean_object* v_homepage_2589_; lean_object* v_license_2590_; lean_object* v_licenseFiles_2591_; lean_object* v_readmeFile_2592_; uint8_t v_reservoir_2593_; lean_object* v_enableArtifactCache_x3f_2594_; lean_object* v_restoreAllArtifacts_x3f_2595_; uint8_t v_libPrefixOnWindows_2596_; uint8_t v_allowImportAll_2597_; lean_object* v_builtinLint_x3f_2598_; lean_object* v_checks_2599_; uint8_t v_fixedToolchain_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
v_toWorkspaceConfig_2567_ = lean_ctor_get(v_cfg_2566_, 0);
v_toLeanConfig_2568_ = lean_ctor_get(v_cfg_2566_, 1);
v_bootstrap_2569_ = lean_ctor_get_uint8(v_cfg_2566_, sizeof(void*)*28);
v_extraDepTargets_2570_ = lean_ctor_get(v_cfg_2566_, 2);
v_precompileModules_2571_ = lean_ctor_get_uint8(v_cfg_2566_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2572_ = lean_ctor_get(v_cfg_2566_, 3);
v_srcDir_2573_ = lean_ctor_get(v_cfg_2566_, 4);
v_buildDir_2574_ = lean_ctor_get(v_cfg_2566_, 5);
v_leanLibDir_2575_ = lean_ctor_get(v_cfg_2566_, 6);
v_nativeLibDir_2576_ = lean_ctor_get(v_cfg_2566_, 7);
v_binDir_2577_ = lean_ctor_get(v_cfg_2566_, 8);
v_irDir_2578_ = lean_ctor_get(v_cfg_2566_, 9);
v_releaseRepo_2579_ = lean_ctor_get(v_cfg_2566_, 10);
v_buildArchive_2580_ = lean_ctor_get(v_cfg_2566_, 11);
v_preferReleaseBuild_2581_ = lean_ctor_get_uint8(v_cfg_2566_, sizeof(void*)*28 + 2);
v_testDriver_2582_ = lean_ctor_get(v_cfg_2566_, 12);
v_testDriverArgs_2583_ = lean_ctor_get(v_cfg_2566_, 13);
v_lintDriver_2584_ = lean_ctor_get(v_cfg_2566_, 14);
v_lintDriverArgs_2585_ = lean_ctor_get(v_cfg_2566_, 15);
v_version_2586_ = lean_ctor_get(v_cfg_2566_, 16);
v_versionTags_2587_ = lean_ctor_get(v_cfg_2566_, 17);
v_keywords_2588_ = lean_ctor_get(v_cfg_2566_, 19);
v_homepage_2589_ = lean_ctor_get(v_cfg_2566_, 20);
v_license_2590_ = lean_ctor_get(v_cfg_2566_, 21);
v_licenseFiles_2591_ = lean_ctor_get(v_cfg_2566_, 22);
v_readmeFile_2592_ = lean_ctor_get(v_cfg_2566_, 23);
v_reservoir_2593_ = lean_ctor_get_uint8(v_cfg_2566_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2594_ = lean_ctor_get(v_cfg_2566_, 24);
v_restoreAllArtifacts_x3f_2595_ = lean_ctor_get(v_cfg_2566_, 25);
v_libPrefixOnWindows_2596_ = lean_ctor_get_uint8(v_cfg_2566_, sizeof(void*)*28 + 4);
v_allowImportAll_2597_ = lean_ctor_get_uint8(v_cfg_2566_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2598_ = lean_ctor_get(v_cfg_2566_, 26);
v_checks_2599_ = lean_ctor_get(v_cfg_2566_, 27);
v_fixedToolchain_2600_ = lean_ctor_get_uint8(v_cfg_2566_, sizeof(void*)*28 + 6);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_cfg_2566_);
if (v_isSharedCheck_2607_ == 0)
{
lean_object* v_unused_2608_; 
v_unused_2608_ = lean_ctor_get(v_cfg_2566_, 18);
lean_dec(v_unused_2608_);
v___x_2602_ = v_cfg_2566_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_checks_2599_);
lean_inc(v_builtinLint_x3f_2598_);
lean_inc(v_restoreAllArtifacts_x3f_2595_);
lean_inc(v_enableArtifactCache_x3f_2594_);
lean_inc(v_readmeFile_2592_);
lean_inc(v_licenseFiles_2591_);
lean_inc(v_license_2590_);
lean_inc(v_homepage_2589_);
lean_inc(v_keywords_2588_);
lean_inc(v_versionTags_2587_);
lean_inc(v_version_2586_);
lean_inc(v_lintDriverArgs_2585_);
lean_inc(v_lintDriver_2584_);
lean_inc(v_testDriverArgs_2583_);
lean_inc(v_testDriver_2582_);
lean_inc(v_buildArchive_2580_);
lean_inc(v_releaseRepo_2579_);
lean_inc(v_irDir_2578_);
lean_inc(v_binDir_2577_);
lean_inc(v_nativeLibDir_2576_);
lean_inc(v_leanLibDir_2575_);
lean_inc(v_buildDir_2574_);
lean_inc(v_srcDir_2573_);
lean_inc(v_moreGlobalServerArgs_2572_);
lean_inc(v_extraDepTargets_2570_);
lean_inc(v_toLeanConfig_2568_);
lean_inc(v_toWorkspaceConfig_2567_);
lean_dec(v_cfg_2566_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 18, v_val_2565_);
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_toWorkspaceConfig_2567_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_toLeanConfig_2568_);
lean_ctor_set(v_reuseFailAlloc_2606_, 2, v_extraDepTargets_2570_);
lean_ctor_set(v_reuseFailAlloc_2606_, 3, v_moreGlobalServerArgs_2572_);
lean_ctor_set(v_reuseFailAlloc_2606_, 4, v_srcDir_2573_);
lean_ctor_set(v_reuseFailAlloc_2606_, 5, v_buildDir_2574_);
lean_ctor_set(v_reuseFailAlloc_2606_, 6, v_leanLibDir_2575_);
lean_ctor_set(v_reuseFailAlloc_2606_, 7, v_nativeLibDir_2576_);
lean_ctor_set(v_reuseFailAlloc_2606_, 8, v_binDir_2577_);
lean_ctor_set(v_reuseFailAlloc_2606_, 9, v_irDir_2578_);
lean_ctor_set(v_reuseFailAlloc_2606_, 10, v_releaseRepo_2579_);
lean_ctor_set(v_reuseFailAlloc_2606_, 11, v_buildArchive_2580_);
lean_ctor_set(v_reuseFailAlloc_2606_, 12, v_testDriver_2582_);
lean_ctor_set(v_reuseFailAlloc_2606_, 13, v_testDriverArgs_2583_);
lean_ctor_set(v_reuseFailAlloc_2606_, 14, v_lintDriver_2584_);
lean_ctor_set(v_reuseFailAlloc_2606_, 15, v_lintDriverArgs_2585_);
lean_ctor_set(v_reuseFailAlloc_2606_, 16, v_version_2586_);
lean_ctor_set(v_reuseFailAlloc_2606_, 17, v_versionTags_2587_);
lean_ctor_set(v_reuseFailAlloc_2606_, 18, v_val_2565_);
lean_ctor_set(v_reuseFailAlloc_2606_, 19, v_keywords_2588_);
lean_ctor_set(v_reuseFailAlloc_2606_, 20, v_homepage_2589_);
lean_ctor_set(v_reuseFailAlloc_2606_, 21, v_license_2590_);
lean_ctor_set(v_reuseFailAlloc_2606_, 22, v_licenseFiles_2591_);
lean_ctor_set(v_reuseFailAlloc_2606_, 23, v_readmeFile_2592_);
lean_ctor_set(v_reuseFailAlloc_2606_, 24, v_enableArtifactCache_x3f_2594_);
lean_ctor_set(v_reuseFailAlloc_2606_, 25, v_restoreAllArtifacts_x3f_2595_);
lean_ctor_set(v_reuseFailAlloc_2606_, 26, v_builtinLint_x3f_2598_);
lean_ctor_set(v_reuseFailAlloc_2606_, 27, v_checks_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, sizeof(void*)*28, v_bootstrap_2569_);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, sizeof(void*)*28 + 1, v_precompileModules_2571_);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, sizeof(void*)*28 + 3, v_reservoir_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2596_);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, sizeof(void*)*28 + 5, v_allowImportAll_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, sizeof(void*)*28 + 6, v_fixedToolchain_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__2(lean_object* v_f_2609_, lean_object* v_cfg_2610_){
_start:
{
lean_object* v_toWorkspaceConfig_2611_; lean_object* v_toLeanConfig_2612_; uint8_t v_bootstrap_2613_; lean_object* v_extraDepTargets_2614_; uint8_t v_precompileModules_2615_; lean_object* v_moreGlobalServerArgs_2616_; lean_object* v_srcDir_2617_; lean_object* v_buildDir_2618_; lean_object* v_leanLibDir_2619_; lean_object* v_nativeLibDir_2620_; lean_object* v_binDir_2621_; lean_object* v_irDir_2622_; lean_object* v_releaseRepo_2623_; lean_object* v_buildArchive_2624_; uint8_t v_preferReleaseBuild_2625_; lean_object* v_testDriver_2626_; lean_object* v_testDriverArgs_2627_; lean_object* v_lintDriver_2628_; lean_object* v_lintDriverArgs_2629_; lean_object* v_version_2630_; lean_object* v_versionTags_2631_; lean_object* v_description_2632_; lean_object* v_keywords_2633_; lean_object* v_homepage_2634_; lean_object* v_license_2635_; lean_object* v_licenseFiles_2636_; lean_object* v_readmeFile_2637_; uint8_t v_reservoir_2638_; lean_object* v_enableArtifactCache_x3f_2639_; lean_object* v_restoreAllArtifacts_x3f_2640_; uint8_t v_libPrefixOnWindows_2641_; uint8_t v_allowImportAll_2642_; lean_object* v_builtinLint_x3f_2643_; lean_object* v_checks_2644_; uint8_t v_fixedToolchain_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2653_; 
v_toWorkspaceConfig_2611_ = lean_ctor_get(v_cfg_2610_, 0);
v_toLeanConfig_2612_ = lean_ctor_get(v_cfg_2610_, 1);
v_bootstrap_2613_ = lean_ctor_get_uint8(v_cfg_2610_, sizeof(void*)*28);
v_extraDepTargets_2614_ = lean_ctor_get(v_cfg_2610_, 2);
v_precompileModules_2615_ = lean_ctor_get_uint8(v_cfg_2610_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2616_ = lean_ctor_get(v_cfg_2610_, 3);
v_srcDir_2617_ = lean_ctor_get(v_cfg_2610_, 4);
v_buildDir_2618_ = lean_ctor_get(v_cfg_2610_, 5);
v_leanLibDir_2619_ = lean_ctor_get(v_cfg_2610_, 6);
v_nativeLibDir_2620_ = lean_ctor_get(v_cfg_2610_, 7);
v_binDir_2621_ = lean_ctor_get(v_cfg_2610_, 8);
v_irDir_2622_ = lean_ctor_get(v_cfg_2610_, 9);
v_releaseRepo_2623_ = lean_ctor_get(v_cfg_2610_, 10);
v_buildArchive_2624_ = lean_ctor_get(v_cfg_2610_, 11);
v_preferReleaseBuild_2625_ = lean_ctor_get_uint8(v_cfg_2610_, sizeof(void*)*28 + 2);
v_testDriver_2626_ = lean_ctor_get(v_cfg_2610_, 12);
v_testDriverArgs_2627_ = lean_ctor_get(v_cfg_2610_, 13);
v_lintDriver_2628_ = lean_ctor_get(v_cfg_2610_, 14);
v_lintDriverArgs_2629_ = lean_ctor_get(v_cfg_2610_, 15);
v_version_2630_ = lean_ctor_get(v_cfg_2610_, 16);
v_versionTags_2631_ = lean_ctor_get(v_cfg_2610_, 17);
v_description_2632_ = lean_ctor_get(v_cfg_2610_, 18);
v_keywords_2633_ = lean_ctor_get(v_cfg_2610_, 19);
v_homepage_2634_ = lean_ctor_get(v_cfg_2610_, 20);
v_license_2635_ = lean_ctor_get(v_cfg_2610_, 21);
v_licenseFiles_2636_ = lean_ctor_get(v_cfg_2610_, 22);
v_readmeFile_2637_ = lean_ctor_get(v_cfg_2610_, 23);
v_reservoir_2638_ = lean_ctor_get_uint8(v_cfg_2610_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2639_ = lean_ctor_get(v_cfg_2610_, 24);
v_restoreAllArtifacts_x3f_2640_ = lean_ctor_get(v_cfg_2610_, 25);
v_libPrefixOnWindows_2641_ = lean_ctor_get_uint8(v_cfg_2610_, sizeof(void*)*28 + 4);
v_allowImportAll_2642_ = lean_ctor_get_uint8(v_cfg_2610_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2643_ = lean_ctor_get(v_cfg_2610_, 26);
v_checks_2644_ = lean_ctor_get(v_cfg_2610_, 27);
v_fixedToolchain_2645_ = lean_ctor_get_uint8(v_cfg_2610_, sizeof(void*)*28 + 6);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_cfg_2610_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2647_ = v_cfg_2610_;
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_checks_2644_);
lean_inc(v_builtinLint_x3f_2643_);
lean_inc(v_restoreAllArtifacts_x3f_2640_);
lean_inc(v_enableArtifactCache_x3f_2639_);
lean_inc(v_readmeFile_2637_);
lean_inc(v_licenseFiles_2636_);
lean_inc(v_license_2635_);
lean_inc(v_homepage_2634_);
lean_inc(v_keywords_2633_);
lean_inc(v_description_2632_);
lean_inc(v_versionTags_2631_);
lean_inc(v_version_2630_);
lean_inc(v_lintDriverArgs_2629_);
lean_inc(v_lintDriver_2628_);
lean_inc(v_testDriverArgs_2627_);
lean_inc(v_testDriver_2626_);
lean_inc(v_buildArchive_2624_);
lean_inc(v_releaseRepo_2623_);
lean_inc(v_irDir_2622_);
lean_inc(v_binDir_2621_);
lean_inc(v_nativeLibDir_2620_);
lean_inc(v_leanLibDir_2619_);
lean_inc(v_buildDir_2618_);
lean_inc(v_srcDir_2617_);
lean_inc(v_moreGlobalServerArgs_2616_);
lean_inc(v_extraDepTargets_2614_);
lean_inc(v_toLeanConfig_2612_);
lean_inc(v_toWorkspaceConfig_2611_);
lean_dec(v_cfg_2610_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_apply_1(v_f_2609_, v_description_2632_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 18, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_toWorkspaceConfig_2611_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_toLeanConfig_2612_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_extraDepTargets_2614_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_moreGlobalServerArgs_2616_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v_srcDir_2617_);
lean_ctor_set(v_reuseFailAlloc_2652_, 5, v_buildDir_2618_);
lean_ctor_set(v_reuseFailAlloc_2652_, 6, v_leanLibDir_2619_);
lean_ctor_set(v_reuseFailAlloc_2652_, 7, v_nativeLibDir_2620_);
lean_ctor_set(v_reuseFailAlloc_2652_, 8, v_binDir_2621_);
lean_ctor_set(v_reuseFailAlloc_2652_, 9, v_irDir_2622_);
lean_ctor_set(v_reuseFailAlloc_2652_, 10, v_releaseRepo_2623_);
lean_ctor_set(v_reuseFailAlloc_2652_, 11, v_buildArchive_2624_);
lean_ctor_set(v_reuseFailAlloc_2652_, 12, v_testDriver_2626_);
lean_ctor_set(v_reuseFailAlloc_2652_, 13, v_testDriverArgs_2627_);
lean_ctor_set(v_reuseFailAlloc_2652_, 14, v_lintDriver_2628_);
lean_ctor_set(v_reuseFailAlloc_2652_, 15, v_lintDriverArgs_2629_);
lean_ctor_set(v_reuseFailAlloc_2652_, 16, v_version_2630_);
lean_ctor_set(v_reuseFailAlloc_2652_, 17, v_versionTags_2631_);
lean_ctor_set(v_reuseFailAlloc_2652_, 18, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2652_, 19, v_keywords_2633_);
lean_ctor_set(v_reuseFailAlloc_2652_, 20, v_homepage_2634_);
lean_ctor_set(v_reuseFailAlloc_2652_, 21, v_license_2635_);
lean_ctor_set(v_reuseFailAlloc_2652_, 22, v_licenseFiles_2636_);
lean_ctor_set(v_reuseFailAlloc_2652_, 23, v_readmeFile_2637_);
lean_ctor_set(v_reuseFailAlloc_2652_, 24, v_enableArtifactCache_x3f_2639_);
lean_ctor_set(v_reuseFailAlloc_2652_, 25, v_restoreAllArtifacts_x3f_2640_);
lean_ctor_set(v_reuseFailAlloc_2652_, 26, v_builtinLint_x3f_2643_);
lean_ctor_set(v_reuseFailAlloc_2652_, 27, v_checks_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*28, v_bootstrap_2613_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*28 + 1, v_precompileModules_2615_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2625_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*28 + 3, v_reservoir_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*28 + 5, v_allowImportAll_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*28 + 6, v_fixedToolchain_2645_);
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
lean_object* l_Lake_PackageConfig_description___proj___redArg(){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = ((lean_object*)(l_Lake_PackageConfig_description___proj___redArg___closed__3));
return v___x_2663_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_description___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2664_;
v_res_2664_ = l_Lake_PackageConfig_description___proj___redArg();
stack->m_obj
 = v_res_2664_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___boxed(lean_object* v___dummy_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lake_PackageConfig_description___proj___redArg();
return v_res_2666_;
}
}
static lean_object* _init_l_Lake_PackageConfig_description___proj___closed__0(void){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lake_PackageConfig_description___proj___redArg();
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object* v_p_2668_, lean_object* v_n_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_obj_once(&l_Lake_PackageConfig_description___proj___closed__0, &l_Lake_PackageConfig_description___proj___closed__0_once, _init_l_Lake_PackageConfig_description___proj___closed__0);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object* v_p_2671_, lean_object* v_n_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lake_PackageConfig_description___proj(v_p_2671_, v_n_2672_);
lean_dec(v_n_2672_);
lean_dec(v_p_2671_);
return v_res_2673_;
}
}
lean_object* l_Lake_PackageConfig_description_instConfigField___redArg(){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = lean_obj_once(&l_Lake_PackageConfig_description___proj___closed__0, &l_Lake_PackageConfig_description___proj___closed__0_once, _init_l_Lake_PackageConfig_description___proj___closed__0);
return v___x_2675_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_description_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2676_;
v_res_2676_ = l_Lake_PackageConfig_description_instConfigField___redArg();
stack->m_obj
 = v_res_2676_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___redArg___boxed(lean_object* v___dummy_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lake_PackageConfig_description_instConfigField___redArg();
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object* v_p_2679_, lean_object* v_n_2680_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = lean_obj_once(&l_Lake_PackageConfig_description___proj___closed__0, &l_Lake_PackageConfig_description___proj___closed__0_once, _init_l_Lake_PackageConfig_description___proj___closed__0);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object* v_p_2682_, lean_object* v_n_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Lake_PackageConfig_description_instConfigField(v_p_2682_, v_n_2683_);
lean_dec(v_n_2683_);
lean_dec(v_p_2682_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__0(lean_object* v_cfg_2685_){
_start:
{
lean_object* v_keywords_2686_; 
v_keywords_2686_ = lean_ctor_get(v_cfg_2685_, 19);
lean_inc_ref(v_keywords_2686_);
return v_keywords_2686_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__0___boxed(lean_object* v_cfg_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lake_PackageConfig_keywords___proj___redArg___lam__0(v_cfg_2687_);
lean_dec_ref(v_cfg_2687_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__1(lean_object* v_val_2689_, lean_object* v_cfg_2690_){
_start:
{
lean_object* v_toWorkspaceConfig_2691_; lean_object* v_toLeanConfig_2692_; uint8_t v_bootstrap_2693_; lean_object* v_extraDepTargets_2694_; uint8_t v_precompileModules_2695_; lean_object* v_moreGlobalServerArgs_2696_; lean_object* v_srcDir_2697_; lean_object* v_buildDir_2698_; lean_object* v_leanLibDir_2699_; lean_object* v_nativeLibDir_2700_; lean_object* v_binDir_2701_; lean_object* v_irDir_2702_; lean_object* v_releaseRepo_2703_; lean_object* v_buildArchive_2704_; uint8_t v_preferReleaseBuild_2705_; lean_object* v_testDriver_2706_; lean_object* v_testDriverArgs_2707_; lean_object* v_lintDriver_2708_; lean_object* v_lintDriverArgs_2709_; lean_object* v_version_2710_; lean_object* v_versionTags_2711_; lean_object* v_description_2712_; lean_object* v_homepage_2713_; lean_object* v_license_2714_; lean_object* v_licenseFiles_2715_; lean_object* v_readmeFile_2716_; uint8_t v_reservoir_2717_; lean_object* v_enableArtifactCache_x3f_2718_; lean_object* v_restoreAllArtifacts_x3f_2719_; uint8_t v_libPrefixOnWindows_2720_; uint8_t v_allowImportAll_2721_; lean_object* v_builtinLint_x3f_2722_; lean_object* v_checks_2723_; uint8_t v_fixedToolchain_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
v_toWorkspaceConfig_2691_ = lean_ctor_get(v_cfg_2690_, 0);
v_toLeanConfig_2692_ = lean_ctor_get(v_cfg_2690_, 1);
v_bootstrap_2693_ = lean_ctor_get_uint8(v_cfg_2690_, sizeof(void*)*28);
v_extraDepTargets_2694_ = lean_ctor_get(v_cfg_2690_, 2);
v_precompileModules_2695_ = lean_ctor_get_uint8(v_cfg_2690_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2696_ = lean_ctor_get(v_cfg_2690_, 3);
v_srcDir_2697_ = lean_ctor_get(v_cfg_2690_, 4);
v_buildDir_2698_ = lean_ctor_get(v_cfg_2690_, 5);
v_leanLibDir_2699_ = lean_ctor_get(v_cfg_2690_, 6);
v_nativeLibDir_2700_ = lean_ctor_get(v_cfg_2690_, 7);
v_binDir_2701_ = lean_ctor_get(v_cfg_2690_, 8);
v_irDir_2702_ = lean_ctor_get(v_cfg_2690_, 9);
v_releaseRepo_2703_ = lean_ctor_get(v_cfg_2690_, 10);
v_buildArchive_2704_ = lean_ctor_get(v_cfg_2690_, 11);
v_preferReleaseBuild_2705_ = lean_ctor_get_uint8(v_cfg_2690_, sizeof(void*)*28 + 2);
v_testDriver_2706_ = lean_ctor_get(v_cfg_2690_, 12);
v_testDriverArgs_2707_ = lean_ctor_get(v_cfg_2690_, 13);
v_lintDriver_2708_ = lean_ctor_get(v_cfg_2690_, 14);
v_lintDriverArgs_2709_ = lean_ctor_get(v_cfg_2690_, 15);
v_version_2710_ = lean_ctor_get(v_cfg_2690_, 16);
v_versionTags_2711_ = lean_ctor_get(v_cfg_2690_, 17);
v_description_2712_ = lean_ctor_get(v_cfg_2690_, 18);
v_homepage_2713_ = lean_ctor_get(v_cfg_2690_, 20);
v_license_2714_ = lean_ctor_get(v_cfg_2690_, 21);
v_licenseFiles_2715_ = lean_ctor_get(v_cfg_2690_, 22);
v_readmeFile_2716_ = lean_ctor_get(v_cfg_2690_, 23);
v_reservoir_2717_ = lean_ctor_get_uint8(v_cfg_2690_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2718_ = lean_ctor_get(v_cfg_2690_, 24);
v_restoreAllArtifacts_x3f_2719_ = lean_ctor_get(v_cfg_2690_, 25);
v_libPrefixOnWindows_2720_ = lean_ctor_get_uint8(v_cfg_2690_, sizeof(void*)*28 + 4);
v_allowImportAll_2721_ = lean_ctor_get_uint8(v_cfg_2690_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2722_ = lean_ctor_get(v_cfg_2690_, 26);
v_checks_2723_ = lean_ctor_get(v_cfg_2690_, 27);
v_fixedToolchain_2724_ = lean_ctor_get_uint8(v_cfg_2690_, sizeof(void*)*28 + 6);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_cfg_2690_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; 
v_unused_2732_ = lean_ctor_get(v_cfg_2690_, 19);
lean_dec(v_unused_2732_);
v___x_2726_ = v_cfg_2690_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_checks_2723_);
lean_inc(v_builtinLint_x3f_2722_);
lean_inc(v_restoreAllArtifacts_x3f_2719_);
lean_inc(v_enableArtifactCache_x3f_2718_);
lean_inc(v_readmeFile_2716_);
lean_inc(v_licenseFiles_2715_);
lean_inc(v_license_2714_);
lean_inc(v_homepage_2713_);
lean_inc(v_description_2712_);
lean_inc(v_versionTags_2711_);
lean_inc(v_version_2710_);
lean_inc(v_lintDriverArgs_2709_);
lean_inc(v_lintDriver_2708_);
lean_inc(v_testDriverArgs_2707_);
lean_inc(v_testDriver_2706_);
lean_inc(v_buildArchive_2704_);
lean_inc(v_releaseRepo_2703_);
lean_inc(v_irDir_2702_);
lean_inc(v_binDir_2701_);
lean_inc(v_nativeLibDir_2700_);
lean_inc(v_leanLibDir_2699_);
lean_inc(v_buildDir_2698_);
lean_inc(v_srcDir_2697_);
lean_inc(v_moreGlobalServerArgs_2696_);
lean_inc(v_extraDepTargets_2694_);
lean_inc(v_toLeanConfig_2692_);
lean_inc(v_toWorkspaceConfig_2691_);
lean_dec(v_cfg_2690_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 19, v_val_2689_);
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_toWorkspaceConfig_2691_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_toLeanConfig_2692_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_extraDepTargets_2694_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v_moreGlobalServerArgs_2696_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v_srcDir_2697_);
lean_ctor_set(v_reuseFailAlloc_2730_, 5, v_buildDir_2698_);
lean_ctor_set(v_reuseFailAlloc_2730_, 6, v_leanLibDir_2699_);
lean_ctor_set(v_reuseFailAlloc_2730_, 7, v_nativeLibDir_2700_);
lean_ctor_set(v_reuseFailAlloc_2730_, 8, v_binDir_2701_);
lean_ctor_set(v_reuseFailAlloc_2730_, 9, v_irDir_2702_);
lean_ctor_set(v_reuseFailAlloc_2730_, 10, v_releaseRepo_2703_);
lean_ctor_set(v_reuseFailAlloc_2730_, 11, v_buildArchive_2704_);
lean_ctor_set(v_reuseFailAlloc_2730_, 12, v_testDriver_2706_);
lean_ctor_set(v_reuseFailAlloc_2730_, 13, v_testDriverArgs_2707_);
lean_ctor_set(v_reuseFailAlloc_2730_, 14, v_lintDriver_2708_);
lean_ctor_set(v_reuseFailAlloc_2730_, 15, v_lintDriverArgs_2709_);
lean_ctor_set(v_reuseFailAlloc_2730_, 16, v_version_2710_);
lean_ctor_set(v_reuseFailAlloc_2730_, 17, v_versionTags_2711_);
lean_ctor_set(v_reuseFailAlloc_2730_, 18, v_description_2712_);
lean_ctor_set(v_reuseFailAlloc_2730_, 19, v_val_2689_);
lean_ctor_set(v_reuseFailAlloc_2730_, 20, v_homepage_2713_);
lean_ctor_set(v_reuseFailAlloc_2730_, 21, v_license_2714_);
lean_ctor_set(v_reuseFailAlloc_2730_, 22, v_licenseFiles_2715_);
lean_ctor_set(v_reuseFailAlloc_2730_, 23, v_readmeFile_2716_);
lean_ctor_set(v_reuseFailAlloc_2730_, 24, v_enableArtifactCache_x3f_2718_);
lean_ctor_set(v_reuseFailAlloc_2730_, 25, v_restoreAllArtifacts_x3f_2719_);
lean_ctor_set(v_reuseFailAlloc_2730_, 26, v_builtinLint_x3f_2722_);
lean_ctor_set(v_reuseFailAlloc_2730_, 27, v_checks_2723_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*28, v_bootstrap_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*28 + 1, v_precompileModules_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*28 + 3, v_reservoir_2717_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2720_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*28 + 5, v_allowImportAll_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*28 + 6, v_fixedToolchain_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__2(lean_object* v_f_2733_, lean_object* v_cfg_2734_){
_start:
{
lean_object* v_toWorkspaceConfig_2735_; lean_object* v_toLeanConfig_2736_; uint8_t v_bootstrap_2737_; lean_object* v_extraDepTargets_2738_; uint8_t v_precompileModules_2739_; lean_object* v_moreGlobalServerArgs_2740_; lean_object* v_srcDir_2741_; lean_object* v_buildDir_2742_; lean_object* v_leanLibDir_2743_; lean_object* v_nativeLibDir_2744_; lean_object* v_binDir_2745_; lean_object* v_irDir_2746_; lean_object* v_releaseRepo_2747_; lean_object* v_buildArchive_2748_; uint8_t v_preferReleaseBuild_2749_; lean_object* v_testDriver_2750_; lean_object* v_testDriverArgs_2751_; lean_object* v_lintDriver_2752_; lean_object* v_lintDriverArgs_2753_; lean_object* v_version_2754_; lean_object* v_versionTags_2755_; lean_object* v_description_2756_; lean_object* v_keywords_2757_; lean_object* v_homepage_2758_; lean_object* v_license_2759_; lean_object* v_licenseFiles_2760_; lean_object* v_readmeFile_2761_; uint8_t v_reservoir_2762_; lean_object* v_enableArtifactCache_x3f_2763_; lean_object* v_restoreAllArtifacts_x3f_2764_; uint8_t v_libPrefixOnWindows_2765_; uint8_t v_allowImportAll_2766_; lean_object* v_builtinLint_x3f_2767_; lean_object* v_checks_2768_; uint8_t v_fixedToolchain_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2777_; 
v_toWorkspaceConfig_2735_ = lean_ctor_get(v_cfg_2734_, 0);
v_toLeanConfig_2736_ = lean_ctor_get(v_cfg_2734_, 1);
v_bootstrap_2737_ = lean_ctor_get_uint8(v_cfg_2734_, sizeof(void*)*28);
v_extraDepTargets_2738_ = lean_ctor_get(v_cfg_2734_, 2);
v_precompileModules_2739_ = lean_ctor_get_uint8(v_cfg_2734_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2740_ = lean_ctor_get(v_cfg_2734_, 3);
v_srcDir_2741_ = lean_ctor_get(v_cfg_2734_, 4);
v_buildDir_2742_ = lean_ctor_get(v_cfg_2734_, 5);
v_leanLibDir_2743_ = lean_ctor_get(v_cfg_2734_, 6);
v_nativeLibDir_2744_ = lean_ctor_get(v_cfg_2734_, 7);
v_binDir_2745_ = lean_ctor_get(v_cfg_2734_, 8);
v_irDir_2746_ = lean_ctor_get(v_cfg_2734_, 9);
v_releaseRepo_2747_ = lean_ctor_get(v_cfg_2734_, 10);
v_buildArchive_2748_ = lean_ctor_get(v_cfg_2734_, 11);
v_preferReleaseBuild_2749_ = lean_ctor_get_uint8(v_cfg_2734_, sizeof(void*)*28 + 2);
v_testDriver_2750_ = lean_ctor_get(v_cfg_2734_, 12);
v_testDriverArgs_2751_ = lean_ctor_get(v_cfg_2734_, 13);
v_lintDriver_2752_ = lean_ctor_get(v_cfg_2734_, 14);
v_lintDriverArgs_2753_ = lean_ctor_get(v_cfg_2734_, 15);
v_version_2754_ = lean_ctor_get(v_cfg_2734_, 16);
v_versionTags_2755_ = lean_ctor_get(v_cfg_2734_, 17);
v_description_2756_ = lean_ctor_get(v_cfg_2734_, 18);
v_keywords_2757_ = lean_ctor_get(v_cfg_2734_, 19);
v_homepage_2758_ = lean_ctor_get(v_cfg_2734_, 20);
v_license_2759_ = lean_ctor_get(v_cfg_2734_, 21);
v_licenseFiles_2760_ = lean_ctor_get(v_cfg_2734_, 22);
v_readmeFile_2761_ = lean_ctor_get(v_cfg_2734_, 23);
v_reservoir_2762_ = lean_ctor_get_uint8(v_cfg_2734_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2763_ = lean_ctor_get(v_cfg_2734_, 24);
v_restoreAllArtifacts_x3f_2764_ = lean_ctor_get(v_cfg_2734_, 25);
v_libPrefixOnWindows_2765_ = lean_ctor_get_uint8(v_cfg_2734_, sizeof(void*)*28 + 4);
v_allowImportAll_2766_ = lean_ctor_get_uint8(v_cfg_2734_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2767_ = lean_ctor_get(v_cfg_2734_, 26);
v_checks_2768_ = lean_ctor_get(v_cfg_2734_, 27);
v_fixedToolchain_2769_ = lean_ctor_get_uint8(v_cfg_2734_, sizeof(void*)*28 + 6);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_cfg_2734_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2771_ = v_cfg_2734_;
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_checks_2768_);
lean_inc(v_builtinLint_x3f_2767_);
lean_inc(v_restoreAllArtifacts_x3f_2764_);
lean_inc(v_enableArtifactCache_x3f_2763_);
lean_inc(v_readmeFile_2761_);
lean_inc(v_licenseFiles_2760_);
lean_inc(v_license_2759_);
lean_inc(v_homepage_2758_);
lean_inc(v_keywords_2757_);
lean_inc(v_description_2756_);
lean_inc(v_versionTags_2755_);
lean_inc(v_version_2754_);
lean_inc(v_lintDriverArgs_2753_);
lean_inc(v_lintDriver_2752_);
lean_inc(v_testDriverArgs_2751_);
lean_inc(v_testDriver_2750_);
lean_inc(v_buildArchive_2748_);
lean_inc(v_releaseRepo_2747_);
lean_inc(v_irDir_2746_);
lean_inc(v_binDir_2745_);
lean_inc(v_nativeLibDir_2744_);
lean_inc(v_leanLibDir_2743_);
lean_inc(v_buildDir_2742_);
lean_inc(v_srcDir_2741_);
lean_inc(v_moreGlobalServerArgs_2740_);
lean_inc(v_extraDepTargets_2738_);
lean_inc(v_toLeanConfig_2736_);
lean_inc(v_toWorkspaceConfig_2735_);
lean_dec(v_cfg_2734_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2773_ = lean_apply_1(v_f_2733_, v_keywords_2757_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 19, v___x_2773_);
v___x_2775_ = v___x_2771_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_toWorkspaceConfig_2735_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_toLeanConfig_2736_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_extraDepTargets_2738_);
lean_ctor_set(v_reuseFailAlloc_2776_, 3, v_moreGlobalServerArgs_2740_);
lean_ctor_set(v_reuseFailAlloc_2776_, 4, v_srcDir_2741_);
lean_ctor_set(v_reuseFailAlloc_2776_, 5, v_buildDir_2742_);
lean_ctor_set(v_reuseFailAlloc_2776_, 6, v_leanLibDir_2743_);
lean_ctor_set(v_reuseFailAlloc_2776_, 7, v_nativeLibDir_2744_);
lean_ctor_set(v_reuseFailAlloc_2776_, 8, v_binDir_2745_);
lean_ctor_set(v_reuseFailAlloc_2776_, 9, v_irDir_2746_);
lean_ctor_set(v_reuseFailAlloc_2776_, 10, v_releaseRepo_2747_);
lean_ctor_set(v_reuseFailAlloc_2776_, 11, v_buildArchive_2748_);
lean_ctor_set(v_reuseFailAlloc_2776_, 12, v_testDriver_2750_);
lean_ctor_set(v_reuseFailAlloc_2776_, 13, v_testDriverArgs_2751_);
lean_ctor_set(v_reuseFailAlloc_2776_, 14, v_lintDriver_2752_);
lean_ctor_set(v_reuseFailAlloc_2776_, 15, v_lintDriverArgs_2753_);
lean_ctor_set(v_reuseFailAlloc_2776_, 16, v_version_2754_);
lean_ctor_set(v_reuseFailAlloc_2776_, 17, v_versionTags_2755_);
lean_ctor_set(v_reuseFailAlloc_2776_, 18, v_description_2756_);
lean_ctor_set(v_reuseFailAlloc_2776_, 19, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2776_, 20, v_homepage_2758_);
lean_ctor_set(v_reuseFailAlloc_2776_, 21, v_license_2759_);
lean_ctor_set(v_reuseFailAlloc_2776_, 22, v_licenseFiles_2760_);
lean_ctor_set(v_reuseFailAlloc_2776_, 23, v_readmeFile_2761_);
lean_ctor_set(v_reuseFailAlloc_2776_, 24, v_enableArtifactCache_x3f_2763_);
lean_ctor_set(v_reuseFailAlloc_2776_, 25, v_restoreAllArtifacts_x3f_2764_);
lean_ctor_set(v_reuseFailAlloc_2776_, 26, v_builtinLint_x3f_2767_);
lean_ctor_set(v_reuseFailAlloc_2776_, 27, v_checks_2768_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, sizeof(void*)*28, v_bootstrap_2737_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, sizeof(void*)*28 + 1, v_precompileModules_2739_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2749_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, sizeof(void*)*28 + 3, v_reservoir_2762_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2765_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, sizeof(void*)*28 + 5, v_allowImportAll_2766_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, sizeof(void*)*28 + 6, v_fixedToolchain_2769_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
lean_object* l_Lake_PackageConfig_keywords___proj___redArg(){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = ((lean_object*)(l_Lake_PackageConfig_keywords___proj___redArg___closed__3));
return v___x_2787_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_keywords___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2788_;
v_res_2788_ = l_Lake_PackageConfig_keywords___proj___redArg();
stack->m_obj
 = v_res_2788_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___boxed(lean_object* v___dummy_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lake_PackageConfig_keywords___proj___redArg();
return v_res_2790_;
}
}
static lean_object* _init_l_Lake_PackageConfig_keywords___proj___closed__0(void){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lake_PackageConfig_keywords___proj___redArg();
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object* v_p_2792_, lean_object* v_n_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_obj_once(&l_Lake_PackageConfig_keywords___proj___closed__0, &l_Lake_PackageConfig_keywords___proj___closed__0_once, _init_l_Lake_PackageConfig_keywords___proj___closed__0);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object* v_p_2795_, lean_object* v_n_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lake_PackageConfig_keywords___proj(v_p_2795_, v_n_2796_);
lean_dec(v_n_2796_);
lean_dec(v_p_2795_);
return v_res_2797_;
}
}
lean_object* l_Lake_PackageConfig_keywords_instConfigField___redArg(){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_obj_once(&l_Lake_PackageConfig_keywords___proj___closed__0, &l_Lake_PackageConfig_keywords___proj___closed__0_once, _init_l_Lake_PackageConfig_keywords___proj___closed__0);
return v___x_2799_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_keywords_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2800_;
v_res_2800_ = l_Lake_PackageConfig_keywords_instConfigField___redArg();
stack->m_obj
 = v_res_2800_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___redArg___boxed(lean_object* v___dummy_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lake_PackageConfig_keywords_instConfigField___redArg();
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object* v_p_2803_, lean_object* v_n_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_obj_once(&l_Lake_PackageConfig_keywords___proj___closed__0, &l_Lake_PackageConfig_keywords___proj___closed__0_once, _init_l_Lake_PackageConfig_keywords___proj___closed__0);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object* v_p_2806_, lean_object* v_n_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lake_PackageConfig_keywords_instConfigField(v_p_2806_, v_n_2807_);
lean_dec(v_n_2807_);
lean_dec(v_p_2806_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__0(lean_object* v_cfg_2809_){
_start:
{
lean_object* v_homepage_2810_; 
v_homepage_2810_ = lean_ctor_get(v_cfg_2809_, 20);
lean_inc_ref(v_homepage_2810_);
return v_homepage_2810_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__0___boxed(lean_object* v_cfg_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lake_PackageConfig_homepage___proj___redArg___lam__0(v_cfg_2811_);
lean_dec_ref(v_cfg_2811_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__1(lean_object* v_val_2813_, lean_object* v_cfg_2814_){
_start:
{
lean_object* v_toWorkspaceConfig_2815_; lean_object* v_toLeanConfig_2816_; uint8_t v_bootstrap_2817_; lean_object* v_extraDepTargets_2818_; uint8_t v_precompileModules_2819_; lean_object* v_moreGlobalServerArgs_2820_; lean_object* v_srcDir_2821_; lean_object* v_buildDir_2822_; lean_object* v_leanLibDir_2823_; lean_object* v_nativeLibDir_2824_; lean_object* v_binDir_2825_; lean_object* v_irDir_2826_; lean_object* v_releaseRepo_2827_; lean_object* v_buildArchive_2828_; uint8_t v_preferReleaseBuild_2829_; lean_object* v_testDriver_2830_; lean_object* v_testDriverArgs_2831_; lean_object* v_lintDriver_2832_; lean_object* v_lintDriverArgs_2833_; lean_object* v_version_2834_; lean_object* v_versionTags_2835_; lean_object* v_description_2836_; lean_object* v_keywords_2837_; lean_object* v_license_2838_; lean_object* v_licenseFiles_2839_; lean_object* v_readmeFile_2840_; uint8_t v_reservoir_2841_; lean_object* v_enableArtifactCache_x3f_2842_; lean_object* v_restoreAllArtifacts_x3f_2843_; uint8_t v_libPrefixOnWindows_2844_; uint8_t v_allowImportAll_2845_; lean_object* v_builtinLint_x3f_2846_; lean_object* v_checks_2847_; uint8_t v_fixedToolchain_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
v_toWorkspaceConfig_2815_ = lean_ctor_get(v_cfg_2814_, 0);
v_toLeanConfig_2816_ = lean_ctor_get(v_cfg_2814_, 1);
v_bootstrap_2817_ = lean_ctor_get_uint8(v_cfg_2814_, sizeof(void*)*28);
v_extraDepTargets_2818_ = lean_ctor_get(v_cfg_2814_, 2);
v_precompileModules_2819_ = lean_ctor_get_uint8(v_cfg_2814_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2820_ = lean_ctor_get(v_cfg_2814_, 3);
v_srcDir_2821_ = lean_ctor_get(v_cfg_2814_, 4);
v_buildDir_2822_ = lean_ctor_get(v_cfg_2814_, 5);
v_leanLibDir_2823_ = lean_ctor_get(v_cfg_2814_, 6);
v_nativeLibDir_2824_ = lean_ctor_get(v_cfg_2814_, 7);
v_binDir_2825_ = lean_ctor_get(v_cfg_2814_, 8);
v_irDir_2826_ = lean_ctor_get(v_cfg_2814_, 9);
v_releaseRepo_2827_ = lean_ctor_get(v_cfg_2814_, 10);
v_buildArchive_2828_ = lean_ctor_get(v_cfg_2814_, 11);
v_preferReleaseBuild_2829_ = lean_ctor_get_uint8(v_cfg_2814_, sizeof(void*)*28 + 2);
v_testDriver_2830_ = lean_ctor_get(v_cfg_2814_, 12);
v_testDriverArgs_2831_ = lean_ctor_get(v_cfg_2814_, 13);
v_lintDriver_2832_ = lean_ctor_get(v_cfg_2814_, 14);
v_lintDriverArgs_2833_ = lean_ctor_get(v_cfg_2814_, 15);
v_version_2834_ = lean_ctor_get(v_cfg_2814_, 16);
v_versionTags_2835_ = lean_ctor_get(v_cfg_2814_, 17);
v_description_2836_ = lean_ctor_get(v_cfg_2814_, 18);
v_keywords_2837_ = lean_ctor_get(v_cfg_2814_, 19);
v_license_2838_ = lean_ctor_get(v_cfg_2814_, 21);
v_licenseFiles_2839_ = lean_ctor_get(v_cfg_2814_, 22);
v_readmeFile_2840_ = lean_ctor_get(v_cfg_2814_, 23);
v_reservoir_2841_ = lean_ctor_get_uint8(v_cfg_2814_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2842_ = lean_ctor_get(v_cfg_2814_, 24);
v_restoreAllArtifacts_x3f_2843_ = lean_ctor_get(v_cfg_2814_, 25);
v_libPrefixOnWindows_2844_ = lean_ctor_get_uint8(v_cfg_2814_, sizeof(void*)*28 + 4);
v_allowImportAll_2845_ = lean_ctor_get_uint8(v_cfg_2814_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2846_ = lean_ctor_get(v_cfg_2814_, 26);
v_checks_2847_ = lean_ctor_get(v_cfg_2814_, 27);
v_fixedToolchain_2848_ = lean_ctor_get_uint8(v_cfg_2814_, sizeof(void*)*28 + 6);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_cfg_2814_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v_cfg_2814_, 20);
lean_dec(v_unused_2856_);
v___x_2850_ = v_cfg_2814_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_checks_2847_);
lean_inc(v_builtinLint_x3f_2846_);
lean_inc(v_restoreAllArtifacts_x3f_2843_);
lean_inc(v_enableArtifactCache_x3f_2842_);
lean_inc(v_readmeFile_2840_);
lean_inc(v_licenseFiles_2839_);
lean_inc(v_license_2838_);
lean_inc(v_keywords_2837_);
lean_inc(v_description_2836_);
lean_inc(v_versionTags_2835_);
lean_inc(v_version_2834_);
lean_inc(v_lintDriverArgs_2833_);
lean_inc(v_lintDriver_2832_);
lean_inc(v_testDriverArgs_2831_);
lean_inc(v_testDriver_2830_);
lean_inc(v_buildArchive_2828_);
lean_inc(v_releaseRepo_2827_);
lean_inc(v_irDir_2826_);
lean_inc(v_binDir_2825_);
lean_inc(v_nativeLibDir_2824_);
lean_inc(v_leanLibDir_2823_);
lean_inc(v_buildDir_2822_);
lean_inc(v_srcDir_2821_);
lean_inc(v_moreGlobalServerArgs_2820_);
lean_inc(v_extraDepTargets_2818_);
lean_inc(v_toLeanConfig_2816_);
lean_inc(v_toWorkspaceConfig_2815_);
lean_dec(v_cfg_2814_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 20, v_val_2813_);
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_toWorkspaceConfig_2815_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_toLeanConfig_2816_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_extraDepTargets_2818_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_moreGlobalServerArgs_2820_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_srcDir_2821_);
lean_ctor_set(v_reuseFailAlloc_2854_, 5, v_buildDir_2822_);
lean_ctor_set(v_reuseFailAlloc_2854_, 6, v_leanLibDir_2823_);
lean_ctor_set(v_reuseFailAlloc_2854_, 7, v_nativeLibDir_2824_);
lean_ctor_set(v_reuseFailAlloc_2854_, 8, v_binDir_2825_);
lean_ctor_set(v_reuseFailAlloc_2854_, 9, v_irDir_2826_);
lean_ctor_set(v_reuseFailAlloc_2854_, 10, v_releaseRepo_2827_);
lean_ctor_set(v_reuseFailAlloc_2854_, 11, v_buildArchive_2828_);
lean_ctor_set(v_reuseFailAlloc_2854_, 12, v_testDriver_2830_);
lean_ctor_set(v_reuseFailAlloc_2854_, 13, v_testDriverArgs_2831_);
lean_ctor_set(v_reuseFailAlloc_2854_, 14, v_lintDriver_2832_);
lean_ctor_set(v_reuseFailAlloc_2854_, 15, v_lintDriverArgs_2833_);
lean_ctor_set(v_reuseFailAlloc_2854_, 16, v_version_2834_);
lean_ctor_set(v_reuseFailAlloc_2854_, 17, v_versionTags_2835_);
lean_ctor_set(v_reuseFailAlloc_2854_, 18, v_description_2836_);
lean_ctor_set(v_reuseFailAlloc_2854_, 19, v_keywords_2837_);
lean_ctor_set(v_reuseFailAlloc_2854_, 20, v_val_2813_);
lean_ctor_set(v_reuseFailAlloc_2854_, 21, v_license_2838_);
lean_ctor_set(v_reuseFailAlloc_2854_, 22, v_licenseFiles_2839_);
lean_ctor_set(v_reuseFailAlloc_2854_, 23, v_readmeFile_2840_);
lean_ctor_set(v_reuseFailAlloc_2854_, 24, v_enableArtifactCache_x3f_2842_);
lean_ctor_set(v_reuseFailAlloc_2854_, 25, v_restoreAllArtifacts_x3f_2843_);
lean_ctor_set(v_reuseFailAlloc_2854_, 26, v_builtinLint_x3f_2846_);
lean_ctor_set(v_reuseFailAlloc_2854_, 27, v_checks_2847_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, sizeof(void*)*28, v_bootstrap_2817_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, sizeof(void*)*28 + 1, v_precompileModules_2819_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2829_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, sizeof(void*)*28 + 3, v_reservoir_2841_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2844_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, sizeof(void*)*28 + 5, v_allowImportAll_2845_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, sizeof(void*)*28 + 6, v_fixedToolchain_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__2(lean_object* v_f_2857_, lean_object* v_cfg_2858_){
_start:
{
lean_object* v_toWorkspaceConfig_2859_; lean_object* v_toLeanConfig_2860_; uint8_t v_bootstrap_2861_; lean_object* v_extraDepTargets_2862_; uint8_t v_precompileModules_2863_; lean_object* v_moreGlobalServerArgs_2864_; lean_object* v_srcDir_2865_; lean_object* v_buildDir_2866_; lean_object* v_leanLibDir_2867_; lean_object* v_nativeLibDir_2868_; lean_object* v_binDir_2869_; lean_object* v_irDir_2870_; lean_object* v_releaseRepo_2871_; lean_object* v_buildArchive_2872_; uint8_t v_preferReleaseBuild_2873_; lean_object* v_testDriver_2874_; lean_object* v_testDriverArgs_2875_; lean_object* v_lintDriver_2876_; lean_object* v_lintDriverArgs_2877_; lean_object* v_version_2878_; lean_object* v_versionTags_2879_; lean_object* v_description_2880_; lean_object* v_keywords_2881_; lean_object* v_homepage_2882_; lean_object* v_license_2883_; lean_object* v_licenseFiles_2884_; lean_object* v_readmeFile_2885_; uint8_t v_reservoir_2886_; lean_object* v_enableArtifactCache_x3f_2887_; lean_object* v_restoreAllArtifacts_x3f_2888_; uint8_t v_libPrefixOnWindows_2889_; uint8_t v_allowImportAll_2890_; lean_object* v_builtinLint_x3f_2891_; lean_object* v_checks_2892_; uint8_t v_fixedToolchain_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2901_; 
v_toWorkspaceConfig_2859_ = lean_ctor_get(v_cfg_2858_, 0);
v_toLeanConfig_2860_ = lean_ctor_get(v_cfg_2858_, 1);
v_bootstrap_2861_ = lean_ctor_get_uint8(v_cfg_2858_, sizeof(void*)*28);
v_extraDepTargets_2862_ = lean_ctor_get(v_cfg_2858_, 2);
v_precompileModules_2863_ = lean_ctor_get_uint8(v_cfg_2858_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2864_ = lean_ctor_get(v_cfg_2858_, 3);
v_srcDir_2865_ = lean_ctor_get(v_cfg_2858_, 4);
v_buildDir_2866_ = lean_ctor_get(v_cfg_2858_, 5);
v_leanLibDir_2867_ = lean_ctor_get(v_cfg_2858_, 6);
v_nativeLibDir_2868_ = lean_ctor_get(v_cfg_2858_, 7);
v_binDir_2869_ = lean_ctor_get(v_cfg_2858_, 8);
v_irDir_2870_ = lean_ctor_get(v_cfg_2858_, 9);
v_releaseRepo_2871_ = lean_ctor_get(v_cfg_2858_, 10);
v_buildArchive_2872_ = lean_ctor_get(v_cfg_2858_, 11);
v_preferReleaseBuild_2873_ = lean_ctor_get_uint8(v_cfg_2858_, sizeof(void*)*28 + 2);
v_testDriver_2874_ = lean_ctor_get(v_cfg_2858_, 12);
v_testDriverArgs_2875_ = lean_ctor_get(v_cfg_2858_, 13);
v_lintDriver_2876_ = lean_ctor_get(v_cfg_2858_, 14);
v_lintDriverArgs_2877_ = lean_ctor_get(v_cfg_2858_, 15);
v_version_2878_ = lean_ctor_get(v_cfg_2858_, 16);
v_versionTags_2879_ = lean_ctor_get(v_cfg_2858_, 17);
v_description_2880_ = lean_ctor_get(v_cfg_2858_, 18);
v_keywords_2881_ = lean_ctor_get(v_cfg_2858_, 19);
v_homepage_2882_ = lean_ctor_get(v_cfg_2858_, 20);
v_license_2883_ = lean_ctor_get(v_cfg_2858_, 21);
v_licenseFiles_2884_ = lean_ctor_get(v_cfg_2858_, 22);
v_readmeFile_2885_ = lean_ctor_get(v_cfg_2858_, 23);
v_reservoir_2886_ = lean_ctor_get_uint8(v_cfg_2858_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2887_ = lean_ctor_get(v_cfg_2858_, 24);
v_restoreAllArtifacts_x3f_2888_ = lean_ctor_get(v_cfg_2858_, 25);
v_libPrefixOnWindows_2889_ = lean_ctor_get_uint8(v_cfg_2858_, sizeof(void*)*28 + 4);
v_allowImportAll_2890_ = lean_ctor_get_uint8(v_cfg_2858_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2891_ = lean_ctor_get(v_cfg_2858_, 26);
v_checks_2892_ = lean_ctor_get(v_cfg_2858_, 27);
v_fixedToolchain_2893_ = lean_ctor_get_uint8(v_cfg_2858_, sizeof(void*)*28 + 6);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_cfg_2858_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2895_ = v_cfg_2858_;
v_isShared_2896_ = v_isSharedCheck_2901_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_checks_2892_);
lean_inc(v_builtinLint_x3f_2891_);
lean_inc(v_restoreAllArtifacts_x3f_2888_);
lean_inc(v_enableArtifactCache_x3f_2887_);
lean_inc(v_readmeFile_2885_);
lean_inc(v_licenseFiles_2884_);
lean_inc(v_license_2883_);
lean_inc(v_homepage_2882_);
lean_inc(v_keywords_2881_);
lean_inc(v_description_2880_);
lean_inc(v_versionTags_2879_);
lean_inc(v_version_2878_);
lean_inc(v_lintDriverArgs_2877_);
lean_inc(v_lintDriver_2876_);
lean_inc(v_testDriverArgs_2875_);
lean_inc(v_testDriver_2874_);
lean_inc(v_buildArchive_2872_);
lean_inc(v_releaseRepo_2871_);
lean_inc(v_irDir_2870_);
lean_inc(v_binDir_2869_);
lean_inc(v_nativeLibDir_2868_);
lean_inc(v_leanLibDir_2867_);
lean_inc(v_buildDir_2866_);
lean_inc(v_srcDir_2865_);
lean_inc(v_moreGlobalServerArgs_2864_);
lean_inc(v_extraDepTargets_2862_);
lean_inc(v_toLeanConfig_2860_);
lean_inc(v_toWorkspaceConfig_2859_);
lean_dec(v_cfg_2858_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2901_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2897_ = lean_apply_1(v_f_2857_, v_homepage_2882_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 20, v___x_2897_);
v___x_2899_ = v___x_2895_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_toWorkspaceConfig_2859_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_toLeanConfig_2860_);
lean_ctor_set(v_reuseFailAlloc_2900_, 2, v_extraDepTargets_2862_);
lean_ctor_set(v_reuseFailAlloc_2900_, 3, v_moreGlobalServerArgs_2864_);
lean_ctor_set(v_reuseFailAlloc_2900_, 4, v_srcDir_2865_);
lean_ctor_set(v_reuseFailAlloc_2900_, 5, v_buildDir_2866_);
lean_ctor_set(v_reuseFailAlloc_2900_, 6, v_leanLibDir_2867_);
lean_ctor_set(v_reuseFailAlloc_2900_, 7, v_nativeLibDir_2868_);
lean_ctor_set(v_reuseFailAlloc_2900_, 8, v_binDir_2869_);
lean_ctor_set(v_reuseFailAlloc_2900_, 9, v_irDir_2870_);
lean_ctor_set(v_reuseFailAlloc_2900_, 10, v_releaseRepo_2871_);
lean_ctor_set(v_reuseFailAlloc_2900_, 11, v_buildArchive_2872_);
lean_ctor_set(v_reuseFailAlloc_2900_, 12, v_testDriver_2874_);
lean_ctor_set(v_reuseFailAlloc_2900_, 13, v_testDriverArgs_2875_);
lean_ctor_set(v_reuseFailAlloc_2900_, 14, v_lintDriver_2876_);
lean_ctor_set(v_reuseFailAlloc_2900_, 15, v_lintDriverArgs_2877_);
lean_ctor_set(v_reuseFailAlloc_2900_, 16, v_version_2878_);
lean_ctor_set(v_reuseFailAlloc_2900_, 17, v_versionTags_2879_);
lean_ctor_set(v_reuseFailAlloc_2900_, 18, v_description_2880_);
lean_ctor_set(v_reuseFailAlloc_2900_, 19, v_keywords_2881_);
lean_ctor_set(v_reuseFailAlloc_2900_, 20, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2900_, 21, v_license_2883_);
lean_ctor_set(v_reuseFailAlloc_2900_, 22, v_licenseFiles_2884_);
lean_ctor_set(v_reuseFailAlloc_2900_, 23, v_readmeFile_2885_);
lean_ctor_set(v_reuseFailAlloc_2900_, 24, v_enableArtifactCache_x3f_2887_);
lean_ctor_set(v_reuseFailAlloc_2900_, 25, v_restoreAllArtifacts_x3f_2888_);
lean_ctor_set(v_reuseFailAlloc_2900_, 26, v_builtinLint_x3f_2891_);
lean_ctor_set(v_reuseFailAlloc_2900_, 27, v_checks_2892_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*28, v_bootstrap_2861_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*28 + 1, v_precompileModules_2863_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2873_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*28 + 3, v_reservoir_2886_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2889_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*28 + 5, v_allowImportAll_2890_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*28 + 6, v_fixedToolchain_2893_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
lean_object* l_Lake_PackageConfig_homepage___proj___redArg(){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = ((lean_object*)(l_Lake_PackageConfig_homepage___proj___redArg___closed__3));
return v___x_2911_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_homepage___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2912_;
v_res_2912_ = l_Lake_PackageConfig_homepage___proj___redArg();
stack->m_obj
 = v_res_2912_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___boxed(lean_object* v___dummy_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lake_PackageConfig_homepage___proj___redArg();
return v_res_2914_;
}
}
static lean_object* _init_l_Lake_PackageConfig_homepage___proj___closed__0(void){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lake_PackageConfig_homepage___proj___redArg();
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object* v_p_2916_, lean_object* v_n_2917_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = lean_obj_once(&l_Lake_PackageConfig_homepage___proj___closed__0, &l_Lake_PackageConfig_homepage___proj___closed__0_once, _init_l_Lake_PackageConfig_homepage___proj___closed__0);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object* v_p_2919_, lean_object* v_n_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lake_PackageConfig_homepage___proj(v_p_2919_, v_n_2920_);
lean_dec(v_n_2920_);
lean_dec(v_p_2919_);
return v_res_2921_;
}
}
lean_object* l_Lake_PackageConfig_homepage_instConfigField___redArg(){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_obj_once(&l_Lake_PackageConfig_homepage___proj___closed__0, &l_Lake_PackageConfig_homepage___proj___closed__0_once, _init_l_Lake_PackageConfig_homepage___proj___closed__0);
return v___x_2923_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_homepage_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2924_;
v_res_2924_ = l_Lake_PackageConfig_homepage_instConfigField___redArg();
stack->m_obj
 = v_res_2924_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___redArg___boxed(lean_object* v___dummy_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lake_PackageConfig_homepage_instConfigField___redArg();
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object* v_p_2927_, lean_object* v_n_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_obj_once(&l_Lake_PackageConfig_homepage___proj___closed__0, &l_Lake_PackageConfig_homepage___proj___closed__0_once, _init_l_Lake_PackageConfig_homepage___proj___closed__0);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object* v_p_2930_, lean_object* v_n_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lake_PackageConfig_homepage_instConfigField(v_p_2930_, v_n_2931_);
lean_dec(v_n_2931_);
lean_dec(v_p_2930_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__0(lean_object* v_cfg_2933_){
_start:
{
lean_object* v_license_2934_; 
v_license_2934_ = lean_ctor_get(v_cfg_2933_, 21);
lean_inc_ref(v_license_2934_);
return v_license_2934_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__0___boxed(lean_object* v_cfg_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lake_PackageConfig_license___proj___redArg___lam__0(v_cfg_2935_);
lean_dec_ref(v_cfg_2935_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__1(lean_object* v_val_2937_, lean_object* v_cfg_2938_){
_start:
{
lean_object* v_toWorkspaceConfig_2939_; lean_object* v_toLeanConfig_2940_; uint8_t v_bootstrap_2941_; lean_object* v_extraDepTargets_2942_; uint8_t v_precompileModules_2943_; lean_object* v_moreGlobalServerArgs_2944_; lean_object* v_srcDir_2945_; lean_object* v_buildDir_2946_; lean_object* v_leanLibDir_2947_; lean_object* v_nativeLibDir_2948_; lean_object* v_binDir_2949_; lean_object* v_irDir_2950_; lean_object* v_releaseRepo_2951_; lean_object* v_buildArchive_2952_; uint8_t v_preferReleaseBuild_2953_; lean_object* v_testDriver_2954_; lean_object* v_testDriverArgs_2955_; lean_object* v_lintDriver_2956_; lean_object* v_lintDriverArgs_2957_; lean_object* v_version_2958_; lean_object* v_versionTags_2959_; lean_object* v_description_2960_; lean_object* v_keywords_2961_; lean_object* v_homepage_2962_; lean_object* v_licenseFiles_2963_; lean_object* v_readmeFile_2964_; uint8_t v_reservoir_2965_; lean_object* v_enableArtifactCache_x3f_2966_; lean_object* v_restoreAllArtifacts_x3f_2967_; uint8_t v_libPrefixOnWindows_2968_; uint8_t v_allowImportAll_2969_; lean_object* v_builtinLint_x3f_2970_; lean_object* v_checks_2971_; uint8_t v_fixedToolchain_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
v_toWorkspaceConfig_2939_ = lean_ctor_get(v_cfg_2938_, 0);
v_toLeanConfig_2940_ = lean_ctor_get(v_cfg_2938_, 1);
v_bootstrap_2941_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*28);
v_extraDepTargets_2942_ = lean_ctor_get(v_cfg_2938_, 2);
v_precompileModules_2943_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2944_ = lean_ctor_get(v_cfg_2938_, 3);
v_srcDir_2945_ = lean_ctor_get(v_cfg_2938_, 4);
v_buildDir_2946_ = lean_ctor_get(v_cfg_2938_, 5);
v_leanLibDir_2947_ = lean_ctor_get(v_cfg_2938_, 6);
v_nativeLibDir_2948_ = lean_ctor_get(v_cfg_2938_, 7);
v_binDir_2949_ = lean_ctor_get(v_cfg_2938_, 8);
v_irDir_2950_ = lean_ctor_get(v_cfg_2938_, 9);
v_releaseRepo_2951_ = lean_ctor_get(v_cfg_2938_, 10);
v_buildArchive_2952_ = lean_ctor_get(v_cfg_2938_, 11);
v_preferReleaseBuild_2953_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*28 + 2);
v_testDriver_2954_ = lean_ctor_get(v_cfg_2938_, 12);
v_testDriverArgs_2955_ = lean_ctor_get(v_cfg_2938_, 13);
v_lintDriver_2956_ = lean_ctor_get(v_cfg_2938_, 14);
v_lintDriverArgs_2957_ = lean_ctor_get(v_cfg_2938_, 15);
v_version_2958_ = lean_ctor_get(v_cfg_2938_, 16);
v_versionTags_2959_ = lean_ctor_get(v_cfg_2938_, 17);
v_description_2960_ = lean_ctor_get(v_cfg_2938_, 18);
v_keywords_2961_ = lean_ctor_get(v_cfg_2938_, 19);
v_homepage_2962_ = lean_ctor_get(v_cfg_2938_, 20);
v_licenseFiles_2963_ = lean_ctor_get(v_cfg_2938_, 22);
v_readmeFile_2964_ = lean_ctor_get(v_cfg_2938_, 23);
v_reservoir_2965_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2966_ = lean_ctor_get(v_cfg_2938_, 24);
v_restoreAllArtifacts_x3f_2967_ = lean_ctor_get(v_cfg_2938_, 25);
v_libPrefixOnWindows_2968_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*28 + 4);
v_allowImportAll_2969_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2970_ = lean_ctor_get(v_cfg_2938_, 26);
v_checks_2971_ = lean_ctor_get(v_cfg_2938_, 27);
v_fixedToolchain_2972_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*28 + 6);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_cfg_2938_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; 
v_unused_2980_ = lean_ctor_get(v_cfg_2938_, 21);
lean_dec(v_unused_2980_);
v___x_2974_ = v_cfg_2938_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_checks_2971_);
lean_inc(v_builtinLint_x3f_2970_);
lean_inc(v_restoreAllArtifacts_x3f_2967_);
lean_inc(v_enableArtifactCache_x3f_2966_);
lean_inc(v_readmeFile_2964_);
lean_inc(v_licenseFiles_2963_);
lean_inc(v_homepage_2962_);
lean_inc(v_keywords_2961_);
lean_inc(v_description_2960_);
lean_inc(v_versionTags_2959_);
lean_inc(v_version_2958_);
lean_inc(v_lintDriverArgs_2957_);
lean_inc(v_lintDriver_2956_);
lean_inc(v_testDriverArgs_2955_);
lean_inc(v_testDriver_2954_);
lean_inc(v_buildArchive_2952_);
lean_inc(v_releaseRepo_2951_);
lean_inc(v_irDir_2950_);
lean_inc(v_binDir_2949_);
lean_inc(v_nativeLibDir_2948_);
lean_inc(v_leanLibDir_2947_);
lean_inc(v_buildDir_2946_);
lean_inc(v_srcDir_2945_);
lean_inc(v_moreGlobalServerArgs_2944_);
lean_inc(v_extraDepTargets_2942_);
lean_inc(v_toLeanConfig_2940_);
lean_inc(v_toWorkspaceConfig_2939_);
lean_dec(v_cfg_2938_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 21, v_val_2937_);
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_toWorkspaceConfig_2939_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_toLeanConfig_2940_);
lean_ctor_set(v_reuseFailAlloc_2978_, 2, v_extraDepTargets_2942_);
lean_ctor_set(v_reuseFailAlloc_2978_, 3, v_moreGlobalServerArgs_2944_);
lean_ctor_set(v_reuseFailAlloc_2978_, 4, v_srcDir_2945_);
lean_ctor_set(v_reuseFailAlloc_2978_, 5, v_buildDir_2946_);
lean_ctor_set(v_reuseFailAlloc_2978_, 6, v_leanLibDir_2947_);
lean_ctor_set(v_reuseFailAlloc_2978_, 7, v_nativeLibDir_2948_);
lean_ctor_set(v_reuseFailAlloc_2978_, 8, v_binDir_2949_);
lean_ctor_set(v_reuseFailAlloc_2978_, 9, v_irDir_2950_);
lean_ctor_set(v_reuseFailAlloc_2978_, 10, v_releaseRepo_2951_);
lean_ctor_set(v_reuseFailAlloc_2978_, 11, v_buildArchive_2952_);
lean_ctor_set(v_reuseFailAlloc_2978_, 12, v_testDriver_2954_);
lean_ctor_set(v_reuseFailAlloc_2978_, 13, v_testDriverArgs_2955_);
lean_ctor_set(v_reuseFailAlloc_2978_, 14, v_lintDriver_2956_);
lean_ctor_set(v_reuseFailAlloc_2978_, 15, v_lintDriverArgs_2957_);
lean_ctor_set(v_reuseFailAlloc_2978_, 16, v_version_2958_);
lean_ctor_set(v_reuseFailAlloc_2978_, 17, v_versionTags_2959_);
lean_ctor_set(v_reuseFailAlloc_2978_, 18, v_description_2960_);
lean_ctor_set(v_reuseFailAlloc_2978_, 19, v_keywords_2961_);
lean_ctor_set(v_reuseFailAlloc_2978_, 20, v_homepage_2962_);
lean_ctor_set(v_reuseFailAlloc_2978_, 21, v_val_2937_);
lean_ctor_set(v_reuseFailAlloc_2978_, 22, v_licenseFiles_2963_);
lean_ctor_set(v_reuseFailAlloc_2978_, 23, v_readmeFile_2964_);
lean_ctor_set(v_reuseFailAlloc_2978_, 24, v_enableArtifactCache_x3f_2966_);
lean_ctor_set(v_reuseFailAlloc_2978_, 25, v_restoreAllArtifacts_x3f_2967_);
lean_ctor_set(v_reuseFailAlloc_2978_, 26, v_builtinLint_x3f_2970_);
lean_ctor_set(v_reuseFailAlloc_2978_, 27, v_checks_2971_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*28, v_bootstrap_2941_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*28 + 1, v_precompileModules_2943_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*28 + 3, v_reservoir_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2968_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*28 + 5, v_allowImportAll_2969_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*28 + 6, v_fixedToolchain_2972_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__2(lean_object* v_f_2981_, lean_object* v_cfg_2982_){
_start:
{
lean_object* v_toWorkspaceConfig_2983_; lean_object* v_toLeanConfig_2984_; uint8_t v_bootstrap_2985_; lean_object* v_extraDepTargets_2986_; uint8_t v_precompileModules_2987_; lean_object* v_moreGlobalServerArgs_2988_; lean_object* v_srcDir_2989_; lean_object* v_buildDir_2990_; lean_object* v_leanLibDir_2991_; lean_object* v_nativeLibDir_2992_; lean_object* v_binDir_2993_; lean_object* v_irDir_2994_; lean_object* v_releaseRepo_2995_; lean_object* v_buildArchive_2996_; uint8_t v_preferReleaseBuild_2997_; lean_object* v_testDriver_2998_; lean_object* v_testDriverArgs_2999_; lean_object* v_lintDriver_3000_; lean_object* v_lintDriverArgs_3001_; lean_object* v_version_3002_; lean_object* v_versionTags_3003_; lean_object* v_description_3004_; lean_object* v_keywords_3005_; lean_object* v_homepage_3006_; lean_object* v_license_3007_; lean_object* v_licenseFiles_3008_; lean_object* v_readmeFile_3009_; uint8_t v_reservoir_3010_; lean_object* v_enableArtifactCache_x3f_3011_; lean_object* v_restoreAllArtifacts_x3f_3012_; uint8_t v_libPrefixOnWindows_3013_; uint8_t v_allowImportAll_3014_; lean_object* v_builtinLint_x3f_3015_; lean_object* v_checks_3016_; uint8_t v_fixedToolchain_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3025_; 
v_toWorkspaceConfig_2983_ = lean_ctor_get(v_cfg_2982_, 0);
v_toLeanConfig_2984_ = lean_ctor_get(v_cfg_2982_, 1);
v_bootstrap_2985_ = lean_ctor_get_uint8(v_cfg_2982_, sizeof(void*)*28);
v_extraDepTargets_2986_ = lean_ctor_get(v_cfg_2982_, 2);
v_precompileModules_2987_ = lean_ctor_get_uint8(v_cfg_2982_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2988_ = lean_ctor_get(v_cfg_2982_, 3);
v_srcDir_2989_ = lean_ctor_get(v_cfg_2982_, 4);
v_buildDir_2990_ = lean_ctor_get(v_cfg_2982_, 5);
v_leanLibDir_2991_ = lean_ctor_get(v_cfg_2982_, 6);
v_nativeLibDir_2992_ = lean_ctor_get(v_cfg_2982_, 7);
v_binDir_2993_ = lean_ctor_get(v_cfg_2982_, 8);
v_irDir_2994_ = lean_ctor_get(v_cfg_2982_, 9);
v_releaseRepo_2995_ = lean_ctor_get(v_cfg_2982_, 10);
v_buildArchive_2996_ = lean_ctor_get(v_cfg_2982_, 11);
v_preferReleaseBuild_2997_ = lean_ctor_get_uint8(v_cfg_2982_, sizeof(void*)*28 + 2);
v_testDriver_2998_ = lean_ctor_get(v_cfg_2982_, 12);
v_testDriverArgs_2999_ = lean_ctor_get(v_cfg_2982_, 13);
v_lintDriver_3000_ = lean_ctor_get(v_cfg_2982_, 14);
v_lintDriverArgs_3001_ = lean_ctor_get(v_cfg_2982_, 15);
v_version_3002_ = lean_ctor_get(v_cfg_2982_, 16);
v_versionTags_3003_ = lean_ctor_get(v_cfg_2982_, 17);
v_description_3004_ = lean_ctor_get(v_cfg_2982_, 18);
v_keywords_3005_ = lean_ctor_get(v_cfg_2982_, 19);
v_homepage_3006_ = lean_ctor_get(v_cfg_2982_, 20);
v_license_3007_ = lean_ctor_get(v_cfg_2982_, 21);
v_licenseFiles_3008_ = lean_ctor_get(v_cfg_2982_, 22);
v_readmeFile_3009_ = lean_ctor_get(v_cfg_2982_, 23);
v_reservoir_3010_ = lean_ctor_get_uint8(v_cfg_2982_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3011_ = lean_ctor_get(v_cfg_2982_, 24);
v_restoreAllArtifacts_x3f_3012_ = lean_ctor_get(v_cfg_2982_, 25);
v_libPrefixOnWindows_3013_ = lean_ctor_get_uint8(v_cfg_2982_, sizeof(void*)*28 + 4);
v_allowImportAll_3014_ = lean_ctor_get_uint8(v_cfg_2982_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3015_ = lean_ctor_get(v_cfg_2982_, 26);
v_checks_3016_ = lean_ctor_get(v_cfg_2982_, 27);
v_fixedToolchain_3017_ = lean_ctor_get_uint8(v_cfg_2982_, sizeof(void*)*28 + 6);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_cfg_2982_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3019_ = v_cfg_2982_;
v_isShared_3020_ = v_isSharedCheck_3025_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_checks_3016_);
lean_inc(v_builtinLint_x3f_3015_);
lean_inc(v_restoreAllArtifacts_x3f_3012_);
lean_inc(v_enableArtifactCache_x3f_3011_);
lean_inc(v_readmeFile_3009_);
lean_inc(v_licenseFiles_3008_);
lean_inc(v_license_3007_);
lean_inc(v_homepage_3006_);
lean_inc(v_keywords_3005_);
lean_inc(v_description_3004_);
lean_inc(v_versionTags_3003_);
lean_inc(v_version_3002_);
lean_inc(v_lintDriverArgs_3001_);
lean_inc(v_lintDriver_3000_);
lean_inc(v_testDriverArgs_2999_);
lean_inc(v_testDriver_2998_);
lean_inc(v_buildArchive_2996_);
lean_inc(v_releaseRepo_2995_);
lean_inc(v_irDir_2994_);
lean_inc(v_binDir_2993_);
lean_inc(v_nativeLibDir_2992_);
lean_inc(v_leanLibDir_2991_);
lean_inc(v_buildDir_2990_);
lean_inc(v_srcDir_2989_);
lean_inc(v_moreGlobalServerArgs_2988_);
lean_inc(v_extraDepTargets_2986_);
lean_inc(v_toLeanConfig_2984_);
lean_inc(v_toWorkspaceConfig_2983_);
lean_dec(v_cfg_2982_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3025_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3021_ = lean_apply_1(v_f_2981_, v_license_3007_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 21, v___x_3021_);
v___x_3023_ = v___x_3019_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_toWorkspaceConfig_2983_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_toLeanConfig_2984_);
lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_extraDepTargets_2986_);
lean_ctor_set(v_reuseFailAlloc_3024_, 3, v_moreGlobalServerArgs_2988_);
lean_ctor_set(v_reuseFailAlloc_3024_, 4, v_srcDir_2989_);
lean_ctor_set(v_reuseFailAlloc_3024_, 5, v_buildDir_2990_);
lean_ctor_set(v_reuseFailAlloc_3024_, 6, v_leanLibDir_2991_);
lean_ctor_set(v_reuseFailAlloc_3024_, 7, v_nativeLibDir_2992_);
lean_ctor_set(v_reuseFailAlloc_3024_, 8, v_binDir_2993_);
lean_ctor_set(v_reuseFailAlloc_3024_, 9, v_irDir_2994_);
lean_ctor_set(v_reuseFailAlloc_3024_, 10, v_releaseRepo_2995_);
lean_ctor_set(v_reuseFailAlloc_3024_, 11, v_buildArchive_2996_);
lean_ctor_set(v_reuseFailAlloc_3024_, 12, v_testDriver_2998_);
lean_ctor_set(v_reuseFailAlloc_3024_, 13, v_testDriverArgs_2999_);
lean_ctor_set(v_reuseFailAlloc_3024_, 14, v_lintDriver_3000_);
lean_ctor_set(v_reuseFailAlloc_3024_, 15, v_lintDriverArgs_3001_);
lean_ctor_set(v_reuseFailAlloc_3024_, 16, v_version_3002_);
lean_ctor_set(v_reuseFailAlloc_3024_, 17, v_versionTags_3003_);
lean_ctor_set(v_reuseFailAlloc_3024_, 18, v_description_3004_);
lean_ctor_set(v_reuseFailAlloc_3024_, 19, v_keywords_3005_);
lean_ctor_set(v_reuseFailAlloc_3024_, 20, v_homepage_3006_);
lean_ctor_set(v_reuseFailAlloc_3024_, 21, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3024_, 22, v_licenseFiles_3008_);
lean_ctor_set(v_reuseFailAlloc_3024_, 23, v_readmeFile_3009_);
lean_ctor_set(v_reuseFailAlloc_3024_, 24, v_enableArtifactCache_x3f_3011_);
lean_ctor_set(v_reuseFailAlloc_3024_, 25, v_restoreAllArtifacts_x3f_3012_);
lean_ctor_set(v_reuseFailAlloc_3024_, 26, v_builtinLint_x3f_3015_);
lean_ctor_set(v_reuseFailAlloc_3024_, 27, v_checks_3016_);
lean_ctor_set_uint8(v_reuseFailAlloc_3024_, sizeof(void*)*28, v_bootstrap_2985_);
lean_ctor_set_uint8(v_reuseFailAlloc_3024_, sizeof(void*)*28 + 1, v_precompileModules_2987_);
lean_ctor_set_uint8(v_reuseFailAlloc_3024_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2997_);
lean_ctor_set_uint8(v_reuseFailAlloc_3024_, sizeof(void*)*28 + 3, v_reservoir_3010_);
lean_ctor_set_uint8(v_reuseFailAlloc_3024_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3013_);
lean_ctor_set_uint8(v_reuseFailAlloc_3024_, sizeof(void*)*28 + 5, v_allowImportAll_3014_);
lean_ctor_set_uint8(v_reuseFailAlloc_3024_, sizeof(void*)*28 + 6, v_fixedToolchain_3017_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
lean_object* l_Lake_PackageConfig_license___proj___redArg(){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = ((lean_object*)(l_Lake_PackageConfig_license___proj___redArg___closed__3));
return v___x_3035_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_license___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3036_;
v_res_3036_ = l_Lake_PackageConfig_license___proj___redArg();
stack->m_obj
 = v_res_3036_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___boxed(lean_object* v___dummy_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lake_PackageConfig_license___proj___redArg();
return v_res_3038_;
}
}
static lean_object* _init_l_Lake_PackageConfig_license___proj___closed__0(void){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lake_PackageConfig_license___proj___redArg();
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object* v_p_3040_, lean_object* v_n_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_obj_once(&l_Lake_PackageConfig_license___proj___closed__0, &l_Lake_PackageConfig_license___proj___closed__0_once, _init_l_Lake_PackageConfig_license___proj___closed__0);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object* v_p_3043_, lean_object* v_n_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lake_PackageConfig_license___proj(v_p_3043_, v_n_3044_);
lean_dec(v_n_3044_);
lean_dec(v_p_3043_);
return v_res_3045_;
}
}
lean_object* l_Lake_PackageConfig_license_instConfigField___redArg(){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_obj_once(&l_Lake_PackageConfig_license___proj___closed__0, &l_Lake_PackageConfig_license___proj___closed__0_once, _init_l_Lake_PackageConfig_license___proj___closed__0);
return v___x_3047_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_license_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3048_;
v_res_3048_ = l_Lake_PackageConfig_license_instConfigField___redArg();
stack->m_obj
 = v_res_3048_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___redArg___boxed(lean_object* v___dummy_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lake_PackageConfig_license_instConfigField___redArg();
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object* v_p_3051_, lean_object* v_n_3052_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_obj_once(&l_Lake_PackageConfig_license___proj___closed__0, &l_Lake_PackageConfig_license___proj___closed__0_once, _init_l_Lake_PackageConfig_license___proj___closed__0);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object* v_p_3054_, lean_object* v_n_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lake_PackageConfig_license_instConfigField(v_p_3054_, v_n_3055_);
lean_dec(v_n_3055_);
lean_dec(v_p_3054_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0(lean_object* v_cfg_3057_){
_start:
{
lean_object* v_licenseFiles_3058_; 
v_licenseFiles_3058_ = lean_ctor_get(v_cfg_3057_, 22);
lean_inc_ref(v_licenseFiles_3058_);
return v_licenseFiles_3058_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0___boxed(lean_object* v_cfg_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0(v_cfg_3059_);
lean_dec_ref(v_cfg_3059_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__1(lean_object* v_val_3061_, lean_object* v_cfg_3062_){
_start:
{
lean_object* v_toWorkspaceConfig_3063_; lean_object* v_toLeanConfig_3064_; uint8_t v_bootstrap_3065_; lean_object* v_extraDepTargets_3066_; uint8_t v_precompileModules_3067_; lean_object* v_moreGlobalServerArgs_3068_; lean_object* v_srcDir_3069_; lean_object* v_buildDir_3070_; lean_object* v_leanLibDir_3071_; lean_object* v_nativeLibDir_3072_; lean_object* v_binDir_3073_; lean_object* v_irDir_3074_; lean_object* v_releaseRepo_3075_; lean_object* v_buildArchive_3076_; uint8_t v_preferReleaseBuild_3077_; lean_object* v_testDriver_3078_; lean_object* v_testDriverArgs_3079_; lean_object* v_lintDriver_3080_; lean_object* v_lintDriverArgs_3081_; lean_object* v_version_3082_; lean_object* v_versionTags_3083_; lean_object* v_description_3084_; lean_object* v_keywords_3085_; lean_object* v_homepage_3086_; lean_object* v_license_3087_; lean_object* v_readmeFile_3088_; uint8_t v_reservoir_3089_; lean_object* v_enableArtifactCache_x3f_3090_; lean_object* v_restoreAllArtifacts_x3f_3091_; uint8_t v_libPrefixOnWindows_3092_; uint8_t v_allowImportAll_3093_; lean_object* v_builtinLint_x3f_3094_; lean_object* v_checks_3095_; uint8_t v_fixedToolchain_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
v_toWorkspaceConfig_3063_ = lean_ctor_get(v_cfg_3062_, 0);
v_toLeanConfig_3064_ = lean_ctor_get(v_cfg_3062_, 1);
v_bootstrap_3065_ = lean_ctor_get_uint8(v_cfg_3062_, sizeof(void*)*28);
v_extraDepTargets_3066_ = lean_ctor_get(v_cfg_3062_, 2);
v_precompileModules_3067_ = lean_ctor_get_uint8(v_cfg_3062_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3068_ = lean_ctor_get(v_cfg_3062_, 3);
v_srcDir_3069_ = lean_ctor_get(v_cfg_3062_, 4);
v_buildDir_3070_ = lean_ctor_get(v_cfg_3062_, 5);
v_leanLibDir_3071_ = lean_ctor_get(v_cfg_3062_, 6);
v_nativeLibDir_3072_ = lean_ctor_get(v_cfg_3062_, 7);
v_binDir_3073_ = lean_ctor_get(v_cfg_3062_, 8);
v_irDir_3074_ = lean_ctor_get(v_cfg_3062_, 9);
v_releaseRepo_3075_ = lean_ctor_get(v_cfg_3062_, 10);
v_buildArchive_3076_ = lean_ctor_get(v_cfg_3062_, 11);
v_preferReleaseBuild_3077_ = lean_ctor_get_uint8(v_cfg_3062_, sizeof(void*)*28 + 2);
v_testDriver_3078_ = lean_ctor_get(v_cfg_3062_, 12);
v_testDriverArgs_3079_ = lean_ctor_get(v_cfg_3062_, 13);
v_lintDriver_3080_ = lean_ctor_get(v_cfg_3062_, 14);
v_lintDriverArgs_3081_ = lean_ctor_get(v_cfg_3062_, 15);
v_version_3082_ = lean_ctor_get(v_cfg_3062_, 16);
v_versionTags_3083_ = lean_ctor_get(v_cfg_3062_, 17);
v_description_3084_ = lean_ctor_get(v_cfg_3062_, 18);
v_keywords_3085_ = lean_ctor_get(v_cfg_3062_, 19);
v_homepage_3086_ = lean_ctor_get(v_cfg_3062_, 20);
v_license_3087_ = lean_ctor_get(v_cfg_3062_, 21);
v_readmeFile_3088_ = lean_ctor_get(v_cfg_3062_, 23);
v_reservoir_3089_ = lean_ctor_get_uint8(v_cfg_3062_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3090_ = lean_ctor_get(v_cfg_3062_, 24);
v_restoreAllArtifacts_x3f_3091_ = lean_ctor_get(v_cfg_3062_, 25);
v_libPrefixOnWindows_3092_ = lean_ctor_get_uint8(v_cfg_3062_, sizeof(void*)*28 + 4);
v_allowImportAll_3093_ = lean_ctor_get_uint8(v_cfg_3062_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3094_ = lean_ctor_get(v_cfg_3062_, 26);
v_checks_3095_ = lean_ctor_get(v_cfg_3062_, 27);
v_fixedToolchain_3096_ = lean_ctor_get_uint8(v_cfg_3062_, sizeof(void*)*28 + 6);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_cfg_3062_);
if (v_isSharedCheck_3103_ == 0)
{
lean_object* v_unused_3104_; 
v_unused_3104_ = lean_ctor_get(v_cfg_3062_, 22);
lean_dec(v_unused_3104_);
v___x_3098_ = v_cfg_3062_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_checks_3095_);
lean_inc(v_builtinLint_x3f_3094_);
lean_inc(v_restoreAllArtifacts_x3f_3091_);
lean_inc(v_enableArtifactCache_x3f_3090_);
lean_inc(v_readmeFile_3088_);
lean_inc(v_license_3087_);
lean_inc(v_homepage_3086_);
lean_inc(v_keywords_3085_);
lean_inc(v_description_3084_);
lean_inc(v_versionTags_3083_);
lean_inc(v_version_3082_);
lean_inc(v_lintDriverArgs_3081_);
lean_inc(v_lintDriver_3080_);
lean_inc(v_testDriverArgs_3079_);
lean_inc(v_testDriver_3078_);
lean_inc(v_buildArchive_3076_);
lean_inc(v_releaseRepo_3075_);
lean_inc(v_irDir_3074_);
lean_inc(v_binDir_3073_);
lean_inc(v_nativeLibDir_3072_);
lean_inc(v_leanLibDir_3071_);
lean_inc(v_buildDir_3070_);
lean_inc(v_srcDir_3069_);
lean_inc(v_moreGlobalServerArgs_3068_);
lean_inc(v_extraDepTargets_3066_);
lean_inc(v_toLeanConfig_3064_);
lean_inc(v_toWorkspaceConfig_3063_);
lean_dec(v_cfg_3062_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 22, v_val_3061_);
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_toWorkspaceConfig_3063_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_toLeanConfig_3064_);
lean_ctor_set(v_reuseFailAlloc_3102_, 2, v_extraDepTargets_3066_);
lean_ctor_set(v_reuseFailAlloc_3102_, 3, v_moreGlobalServerArgs_3068_);
lean_ctor_set(v_reuseFailAlloc_3102_, 4, v_srcDir_3069_);
lean_ctor_set(v_reuseFailAlloc_3102_, 5, v_buildDir_3070_);
lean_ctor_set(v_reuseFailAlloc_3102_, 6, v_leanLibDir_3071_);
lean_ctor_set(v_reuseFailAlloc_3102_, 7, v_nativeLibDir_3072_);
lean_ctor_set(v_reuseFailAlloc_3102_, 8, v_binDir_3073_);
lean_ctor_set(v_reuseFailAlloc_3102_, 9, v_irDir_3074_);
lean_ctor_set(v_reuseFailAlloc_3102_, 10, v_releaseRepo_3075_);
lean_ctor_set(v_reuseFailAlloc_3102_, 11, v_buildArchive_3076_);
lean_ctor_set(v_reuseFailAlloc_3102_, 12, v_testDriver_3078_);
lean_ctor_set(v_reuseFailAlloc_3102_, 13, v_testDriverArgs_3079_);
lean_ctor_set(v_reuseFailAlloc_3102_, 14, v_lintDriver_3080_);
lean_ctor_set(v_reuseFailAlloc_3102_, 15, v_lintDriverArgs_3081_);
lean_ctor_set(v_reuseFailAlloc_3102_, 16, v_version_3082_);
lean_ctor_set(v_reuseFailAlloc_3102_, 17, v_versionTags_3083_);
lean_ctor_set(v_reuseFailAlloc_3102_, 18, v_description_3084_);
lean_ctor_set(v_reuseFailAlloc_3102_, 19, v_keywords_3085_);
lean_ctor_set(v_reuseFailAlloc_3102_, 20, v_homepage_3086_);
lean_ctor_set(v_reuseFailAlloc_3102_, 21, v_license_3087_);
lean_ctor_set(v_reuseFailAlloc_3102_, 22, v_val_3061_);
lean_ctor_set(v_reuseFailAlloc_3102_, 23, v_readmeFile_3088_);
lean_ctor_set(v_reuseFailAlloc_3102_, 24, v_enableArtifactCache_x3f_3090_);
lean_ctor_set(v_reuseFailAlloc_3102_, 25, v_restoreAllArtifacts_x3f_3091_);
lean_ctor_set(v_reuseFailAlloc_3102_, 26, v_builtinLint_x3f_3094_);
lean_ctor_set(v_reuseFailAlloc_3102_, 27, v_checks_3095_);
lean_ctor_set_uint8(v_reuseFailAlloc_3102_, sizeof(void*)*28, v_bootstrap_3065_);
lean_ctor_set_uint8(v_reuseFailAlloc_3102_, sizeof(void*)*28 + 1, v_precompileModules_3067_);
lean_ctor_set_uint8(v_reuseFailAlloc_3102_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3077_);
lean_ctor_set_uint8(v_reuseFailAlloc_3102_, sizeof(void*)*28 + 3, v_reservoir_3089_);
lean_ctor_set_uint8(v_reuseFailAlloc_3102_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3092_);
lean_ctor_set_uint8(v_reuseFailAlloc_3102_, sizeof(void*)*28 + 5, v_allowImportAll_3093_);
lean_ctor_set_uint8(v_reuseFailAlloc_3102_, sizeof(void*)*28 + 6, v_fixedToolchain_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__2(lean_object* v_f_3105_, lean_object* v_cfg_3106_){
_start:
{
lean_object* v_toWorkspaceConfig_3107_; lean_object* v_toLeanConfig_3108_; uint8_t v_bootstrap_3109_; lean_object* v_extraDepTargets_3110_; uint8_t v_precompileModules_3111_; lean_object* v_moreGlobalServerArgs_3112_; lean_object* v_srcDir_3113_; lean_object* v_buildDir_3114_; lean_object* v_leanLibDir_3115_; lean_object* v_nativeLibDir_3116_; lean_object* v_binDir_3117_; lean_object* v_irDir_3118_; lean_object* v_releaseRepo_3119_; lean_object* v_buildArchive_3120_; uint8_t v_preferReleaseBuild_3121_; lean_object* v_testDriver_3122_; lean_object* v_testDriverArgs_3123_; lean_object* v_lintDriver_3124_; lean_object* v_lintDriverArgs_3125_; lean_object* v_version_3126_; lean_object* v_versionTags_3127_; lean_object* v_description_3128_; lean_object* v_keywords_3129_; lean_object* v_homepage_3130_; lean_object* v_license_3131_; lean_object* v_licenseFiles_3132_; lean_object* v_readmeFile_3133_; uint8_t v_reservoir_3134_; lean_object* v_enableArtifactCache_x3f_3135_; lean_object* v_restoreAllArtifacts_x3f_3136_; uint8_t v_libPrefixOnWindows_3137_; uint8_t v_allowImportAll_3138_; lean_object* v_builtinLint_x3f_3139_; lean_object* v_checks_3140_; uint8_t v_fixedToolchain_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3149_; 
v_toWorkspaceConfig_3107_ = lean_ctor_get(v_cfg_3106_, 0);
v_toLeanConfig_3108_ = lean_ctor_get(v_cfg_3106_, 1);
v_bootstrap_3109_ = lean_ctor_get_uint8(v_cfg_3106_, sizeof(void*)*28);
v_extraDepTargets_3110_ = lean_ctor_get(v_cfg_3106_, 2);
v_precompileModules_3111_ = lean_ctor_get_uint8(v_cfg_3106_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3112_ = lean_ctor_get(v_cfg_3106_, 3);
v_srcDir_3113_ = lean_ctor_get(v_cfg_3106_, 4);
v_buildDir_3114_ = lean_ctor_get(v_cfg_3106_, 5);
v_leanLibDir_3115_ = lean_ctor_get(v_cfg_3106_, 6);
v_nativeLibDir_3116_ = lean_ctor_get(v_cfg_3106_, 7);
v_binDir_3117_ = lean_ctor_get(v_cfg_3106_, 8);
v_irDir_3118_ = lean_ctor_get(v_cfg_3106_, 9);
v_releaseRepo_3119_ = lean_ctor_get(v_cfg_3106_, 10);
v_buildArchive_3120_ = lean_ctor_get(v_cfg_3106_, 11);
v_preferReleaseBuild_3121_ = lean_ctor_get_uint8(v_cfg_3106_, sizeof(void*)*28 + 2);
v_testDriver_3122_ = lean_ctor_get(v_cfg_3106_, 12);
v_testDriverArgs_3123_ = lean_ctor_get(v_cfg_3106_, 13);
v_lintDriver_3124_ = lean_ctor_get(v_cfg_3106_, 14);
v_lintDriverArgs_3125_ = lean_ctor_get(v_cfg_3106_, 15);
v_version_3126_ = lean_ctor_get(v_cfg_3106_, 16);
v_versionTags_3127_ = lean_ctor_get(v_cfg_3106_, 17);
v_description_3128_ = lean_ctor_get(v_cfg_3106_, 18);
v_keywords_3129_ = lean_ctor_get(v_cfg_3106_, 19);
v_homepage_3130_ = lean_ctor_get(v_cfg_3106_, 20);
v_license_3131_ = lean_ctor_get(v_cfg_3106_, 21);
v_licenseFiles_3132_ = lean_ctor_get(v_cfg_3106_, 22);
v_readmeFile_3133_ = lean_ctor_get(v_cfg_3106_, 23);
v_reservoir_3134_ = lean_ctor_get_uint8(v_cfg_3106_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3135_ = lean_ctor_get(v_cfg_3106_, 24);
v_restoreAllArtifacts_x3f_3136_ = lean_ctor_get(v_cfg_3106_, 25);
v_libPrefixOnWindows_3137_ = lean_ctor_get_uint8(v_cfg_3106_, sizeof(void*)*28 + 4);
v_allowImportAll_3138_ = lean_ctor_get_uint8(v_cfg_3106_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3139_ = lean_ctor_get(v_cfg_3106_, 26);
v_checks_3140_ = lean_ctor_get(v_cfg_3106_, 27);
v_fixedToolchain_3141_ = lean_ctor_get_uint8(v_cfg_3106_, sizeof(void*)*28 + 6);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_cfg_3106_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3143_ = v_cfg_3106_;
v_isShared_3144_ = v_isSharedCheck_3149_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_checks_3140_);
lean_inc(v_builtinLint_x3f_3139_);
lean_inc(v_restoreAllArtifacts_x3f_3136_);
lean_inc(v_enableArtifactCache_x3f_3135_);
lean_inc(v_readmeFile_3133_);
lean_inc(v_licenseFiles_3132_);
lean_inc(v_license_3131_);
lean_inc(v_homepage_3130_);
lean_inc(v_keywords_3129_);
lean_inc(v_description_3128_);
lean_inc(v_versionTags_3127_);
lean_inc(v_version_3126_);
lean_inc(v_lintDriverArgs_3125_);
lean_inc(v_lintDriver_3124_);
lean_inc(v_testDriverArgs_3123_);
lean_inc(v_testDriver_3122_);
lean_inc(v_buildArchive_3120_);
lean_inc(v_releaseRepo_3119_);
lean_inc(v_irDir_3118_);
lean_inc(v_binDir_3117_);
lean_inc(v_nativeLibDir_3116_);
lean_inc(v_leanLibDir_3115_);
lean_inc(v_buildDir_3114_);
lean_inc(v_srcDir_3113_);
lean_inc(v_moreGlobalServerArgs_3112_);
lean_inc(v_extraDepTargets_3110_);
lean_inc(v_toLeanConfig_3108_);
lean_inc(v_toWorkspaceConfig_3107_);
lean_dec(v_cfg_3106_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3149_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3145_ = lean_apply_1(v_f_3105_, v_licenseFiles_3132_);
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 22, v___x_3145_);
v___x_3147_ = v___x_3143_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_toWorkspaceConfig_3107_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_toLeanConfig_3108_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_extraDepTargets_3110_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v_moreGlobalServerArgs_3112_);
lean_ctor_set(v_reuseFailAlloc_3148_, 4, v_srcDir_3113_);
lean_ctor_set(v_reuseFailAlloc_3148_, 5, v_buildDir_3114_);
lean_ctor_set(v_reuseFailAlloc_3148_, 6, v_leanLibDir_3115_);
lean_ctor_set(v_reuseFailAlloc_3148_, 7, v_nativeLibDir_3116_);
lean_ctor_set(v_reuseFailAlloc_3148_, 8, v_binDir_3117_);
lean_ctor_set(v_reuseFailAlloc_3148_, 9, v_irDir_3118_);
lean_ctor_set(v_reuseFailAlloc_3148_, 10, v_releaseRepo_3119_);
lean_ctor_set(v_reuseFailAlloc_3148_, 11, v_buildArchive_3120_);
lean_ctor_set(v_reuseFailAlloc_3148_, 12, v_testDriver_3122_);
lean_ctor_set(v_reuseFailAlloc_3148_, 13, v_testDriverArgs_3123_);
lean_ctor_set(v_reuseFailAlloc_3148_, 14, v_lintDriver_3124_);
lean_ctor_set(v_reuseFailAlloc_3148_, 15, v_lintDriverArgs_3125_);
lean_ctor_set(v_reuseFailAlloc_3148_, 16, v_version_3126_);
lean_ctor_set(v_reuseFailAlloc_3148_, 17, v_versionTags_3127_);
lean_ctor_set(v_reuseFailAlloc_3148_, 18, v_description_3128_);
lean_ctor_set(v_reuseFailAlloc_3148_, 19, v_keywords_3129_);
lean_ctor_set(v_reuseFailAlloc_3148_, 20, v_homepage_3130_);
lean_ctor_set(v_reuseFailAlloc_3148_, 21, v_license_3131_);
lean_ctor_set(v_reuseFailAlloc_3148_, 22, v___x_3145_);
lean_ctor_set(v_reuseFailAlloc_3148_, 23, v_readmeFile_3133_);
lean_ctor_set(v_reuseFailAlloc_3148_, 24, v_enableArtifactCache_x3f_3135_);
lean_ctor_set(v_reuseFailAlloc_3148_, 25, v_restoreAllArtifacts_x3f_3136_);
lean_ctor_set(v_reuseFailAlloc_3148_, 26, v_builtinLint_x3f_3139_);
lean_ctor_set(v_reuseFailAlloc_3148_, 27, v_checks_3140_);
lean_ctor_set_uint8(v_reuseFailAlloc_3148_, sizeof(void*)*28, v_bootstrap_3109_);
lean_ctor_set_uint8(v_reuseFailAlloc_3148_, sizeof(void*)*28 + 1, v_precompileModules_3111_);
lean_ctor_set_uint8(v_reuseFailAlloc_3148_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3121_);
lean_ctor_set_uint8(v_reuseFailAlloc_3148_, sizeof(void*)*28 + 3, v_reservoir_3134_);
lean_ctor_set_uint8(v_reuseFailAlloc_3148_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3137_);
lean_ctor_set_uint8(v_reuseFailAlloc_3148_, sizeof(void*)*28 + 5, v_allowImportAll_3138_);
lean_ctor_set_uint8(v_reuseFailAlloc_3148_, sizeof(void*)*28 + 6, v_fixedToolchain_3141_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3(lean_object* v_x_3150_){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3151_ = lean_unsigned_to_nat(1u);
v___x_3152_ = lean_mk_empty_array_with_capacity(v___x_3151_);
lean_dec_ref(v___x_3152_);
v___x_3153_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__6));
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3___boxed(lean_object* v_x_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3(v_x_3154_);
lean_dec_ref(v_x_3154_);
return v_res_3155_;
}
}
lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg(){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__4));
return v___x_3166_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_licenseFiles___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3167_;
v_res_3167_ = l_Lake_PackageConfig_licenseFiles___proj___redArg();
stack->m_obj
 = v_res_3167_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___boxed(lean_object* v___dummy_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lake_PackageConfig_licenseFiles___proj___redArg();
return v_res_3169_;
}
}
static lean_object* _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0(void){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Lake_PackageConfig_licenseFiles___proj___redArg();
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object* v_p_3171_, lean_object* v_n_3172_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = lean_obj_once(&l_Lake_PackageConfig_licenseFiles___proj___closed__0, &l_Lake_PackageConfig_licenseFiles___proj___closed__0_once, _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object* v_p_3174_, lean_object* v_n_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_3174_, v_n_3175_);
lean_dec(v_n_3175_);
lean_dec(v_p_3174_);
return v_res_3176_;
}
}
lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___redArg(){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = lean_obj_once(&l_Lake_PackageConfig_licenseFiles___proj___closed__0, &l_Lake_PackageConfig_licenseFiles___proj___closed__0_once, _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0);
return v___x_3178_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_licenseFiles_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3179_;
v_res_3179_ = l_Lake_PackageConfig_licenseFiles_instConfigField___redArg();
stack->m_obj
 = v_res_3179_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___redArg___boxed(lean_object* v___dummy_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_Lake_PackageConfig_licenseFiles_instConfigField___redArg();
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object* v_p_3182_, lean_object* v_n_3183_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_obj_once(&l_Lake_PackageConfig_licenseFiles___proj___closed__0, &l_Lake_PackageConfig_licenseFiles___proj___closed__0_once, _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object* v_p_3185_, lean_object* v_n_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lake_PackageConfig_licenseFiles_instConfigField(v_p_3185_, v_n_3186_);
lean_dec(v_n_3186_);
lean_dec(v_p_3185_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0(lean_object* v_cfg_3188_){
_start:
{
lean_object* v_readmeFile_3189_; 
v_readmeFile_3189_ = lean_ctor_get(v_cfg_3188_, 23);
lean_inc_ref(v_readmeFile_3189_);
return v_readmeFile_3189_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0___boxed(lean_object* v_cfg_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0(v_cfg_3190_);
lean_dec_ref(v_cfg_3190_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__1(lean_object* v_val_3192_, lean_object* v_cfg_3193_){
_start:
{
lean_object* v_toWorkspaceConfig_3194_; lean_object* v_toLeanConfig_3195_; uint8_t v_bootstrap_3196_; lean_object* v_extraDepTargets_3197_; uint8_t v_precompileModules_3198_; lean_object* v_moreGlobalServerArgs_3199_; lean_object* v_srcDir_3200_; lean_object* v_buildDir_3201_; lean_object* v_leanLibDir_3202_; lean_object* v_nativeLibDir_3203_; lean_object* v_binDir_3204_; lean_object* v_irDir_3205_; lean_object* v_releaseRepo_3206_; lean_object* v_buildArchive_3207_; uint8_t v_preferReleaseBuild_3208_; lean_object* v_testDriver_3209_; lean_object* v_testDriverArgs_3210_; lean_object* v_lintDriver_3211_; lean_object* v_lintDriverArgs_3212_; lean_object* v_version_3213_; lean_object* v_versionTags_3214_; lean_object* v_description_3215_; lean_object* v_keywords_3216_; lean_object* v_homepage_3217_; lean_object* v_license_3218_; lean_object* v_licenseFiles_3219_; uint8_t v_reservoir_3220_; lean_object* v_enableArtifactCache_x3f_3221_; lean_object* v_restoreAllArtifacts_x3f_3222_; uint8_t v_libPrefixOnWindows_3223_; uint8_t v_allowImportAll_3224_; lean_object* v_builtinLint_x3f_3225_; lean_object* v_checks_3226_; uint8_t v_fixedToolchain_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
v_toWorkspaceConfig_3194_ = lean_ctor_get(v_cfg_3193_, 0);
v_toLeanConfig_3195_ = lean_ctor_get(v_cfg_3193_, 1);
v_bootstrap_3196_ = lean_ctor_get_uint8(v_cfg_3193_, sizeof(void*)*28);
v_extraDepTargets_3197_ = lean_ctor_get(v_cfg_3193_, 2);
v_precompileModules_3198_ = lean_ctor_get_uint8(v_cfg_3193_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3199_ = lean_ctor_get(v_cfg_3193_, 3);
v_srcDir_3200_ = lean_ctor_get(v_cfg_3193_, 4);
v_buildDir_3201_ = lean_ctor_get(v_cfg_3193_, 5);
v_leanLibDir_3202_ = lean_ctor_get(v_cfg_3193_, 6);
v_nativeLibDir_3203_ = lean_ctor_get(v_cfg_3193_, 7);
v_binDir_3204_ = lean_ctor_get(v_cfg_3193_, 8);
v_irDir_3205_ = lean_ctor_get(v_cfg_3193_, 9);
v_releaseRepo_3206_ = lean_ctor_get(v_cfg_3193_, 10);
v_buildArchive_3207_ = lean_ctor_get(v_cfg_3193_, 11);
v_preferReleaseBuild_3208_ = lean_ctor_get_uint8(v_cfg_3193_, sizeof(void*)*28 + 2);
v_testDriver_3209_ = lean_ctor_get(v_cfg_3193_, 12);
v_testDriverArgs_3210_ = lean_ctor_get(v_cfg_3193_, 13);
v_lintDriver_3211_ = lean_ctor_get(v_cfg_3193_, 14);
v_lintDriverArgs_3212_ = lean_ctor_get(v_cfg_3193_, 15);
v_version_3213_ = lean_ctor_get(v_cfg_3193_, 16);
v_versionTags_3214_ = lean_ctor_get(v_cfg_3193_, 17);
v_description_3215_ = lean_ctor_get(v_cfg_3193_, 18);
v_keywords_3216_ = lean_ctor_get(v_cfg_3193_, 19);
v_homepage_3217_ = lean_ctor_get(v_cfg_3193_, 20);
v_license_3218_ = lean_ctor_get(v_cfg_3193_, 21);
v_licenseFiles_3219_ = lean_ctor_get(v_cfg_3193_, 22);
v_reservoir_3220_ = lean_ctor_get_uint8(v_cfg_3193_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3221_ = lean_ctor_get(v_cfg_3193_, 24);
v_restoreAllArtifacts_x3f_3222_ = lean_ctor_get(v_cfg_3193_, 25);
v_libPrefixOnWindows_3223_ = lean_ctor_get_uint8(v_cfg_3193_, sizeof(void*)*28 + 4);
v_allowImportAll_3224_ = lean_ctor_get_uint8(v_cfg_3193_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3225_ = lean_ctor_get(v_cfg_3193_, 26);
v_checks_3226_ = lean_ctor_get(v_cfg_3193_, 27);
v_fixedToolchain_3227_ = lean_ctor_get_uint8(v_cfg_3193_, sizeof(void*)*28 + 6);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_cfg_3193_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; 
v_unused_3235_ = lean_ctor_get(v_cfg_3193_, 23);
lean_dec(v_unused_3235_);
v___x_3229_ = v_cfg_3193_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_checks_3226_);
lean_inc(v_builtinLint_x3f_3225_);
lean_inc(v_restoreAllArtifacts_x3f_3222_);
lean_inc(v_enableArtifactCache_x3f_3221_);
lean_inc(v_licenseFiles_3219_);
lean_inc(v_license_3218_);
lean_inc(v_homepage_3217_);
lean_inc(v_keywords_3216_);
lean_inc(v_description_3215_);
lean_inc(v_versionTags_3214_);
lean_inc(v_version_3213_);
lean_inc(v_lintDriverArgs_3212_);
lean_inc(v_lintDriver_3211_);
lean_inc(v_testDriverArgs_3210_);
lean_inc(v_testDriver_3209_);
lean_inc(v_buildArchive_3207_);
lean_inc(v_releaseRepo_3206_);
lean_inc(v_irDir_3205_);
lean_inc(v_binDir_3204_);
lean_inc(v_nativeLibDir_3203_);
lean_inc(v_leanLibDir_3202_);
lean_inc(v_buildDir_3201_);
lean_inc(v_srcDir_3200_);
lean_inc(v_moreGlobalServerArgs_3199_);
lean_inc(v_extraDepTargets_3197_);
lean_inc(v_toLeanConfig_3195_);
lean_inc(v_toWorkspaceConfig_3194_);
lean_dec(v_cfg_3193_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 23, v_val_3192_);
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_toWorkspaceConfig_3194_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_toLeanConfig_3195_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_extraDepTargets_3197_);
lean_ctor_set(v_reuseFailAlloc_3233_, 3, v_moreGlobalServerArgs_3199_);
lean_ctor_set(v_reuseFailAlloc_3233_, 4, v_srcDir_3200_);
lean_ctor_set(v_reuseFailAlloc_3233_, 5, v_buildDir_3201_);
lean_ctor_set(v_reuseFailAlloc_3233_, 6, v_leanLibDir_3202_);
lean_ctor_set(v_reuseFailAlloc_3233_, 7, v_nativeLibDir_3203_);
lean_ctor_set(v_reuseFailAlloc_3233_, 8, v_binDir_3204_);
lean_ctor_set(v_reuseFailAlloc_3233_, 9, v_irDir_3205_);
lean_ctor_set(v_reuseFailAlloc_3233_, 10, v_releaseRepo_3206_);
lean_ctor_set(v_reuseFailAlloc_3233_, 11, v_buildArchive_3207_);
lean_ctor_set(v_reuseFailAlloc_3233_, 12, v_testDriver_3209_);
lean_ctor_set(v_reuseFailAlloc_3233_, 13, v_testDriverArgs_3210_);
lean_ctor_set(v_reuseFailAlloc_3233_, 14, v_lintDriver_3211_);
lean_ctor_set(v_reuseFailAlloc_3233_, 15, v_lintDriverArgs_3212_);
lean_ctor_set(v_reuseFailAlloc_3233_, 16, v_version_3213_);
lean_ctor_set(v_reuseFailAlloc_3233_, 17, v_versionTags_3214_);
lean_ctor_set(v_reuseFailAlloc_3233_, 18, v_description_3215_);
lean_ctor_set(v_reuseFailAlloc_3233_, 19, v_keywords_3216_);
lean_ctor_set(v_reuseFailAlloc_3233_, 20, v_homepage_3217_);
lean_ctor_set(v_reuseFailAlloc_3233_, 21, v_license_3218_);
lean_ctor_set(v_reuseFailAlloc_3233_, 22, v_licenseFiles_3219_);
lean_ctor_set(v_reuseFailAlloc_3233_, 23, v_val_3192_);
lean_ctor_set(v_reuseFailAlloc_3233_, 24, v_enableArtifactCache_x3f_3221_);
lean_ctor_set(v_reuseFailAlloc_3233_, 25, v_restoreAllArtifacts_x3f_3222_);
lean_ctor_set(v_reuseFailAlloc_3233_, 26, v_builtinLint_x3f_3225_);
lean_ctor_set(v_reuseFailAlloc_3233_, 27, v_checks_3226_);
lean_ctor_set_uint8(v_reuseFailAlloc_3233_, sizeof(void*)*28, v_bootstrap_3196_);
lean_ctor_set_uint8(v_reuseFailAlloc_3233_, sizeof(void*)*28 + 1, v_precompileModules_3198_);
lean_ctor_set_uint8(v_reuseFailAlloc_3233_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3208_);
lean_ctor_set_uint8(v_reuseFailAlloc_3233_, sizeof(void*)*28 + 3, v_reservoir_3220_);
lean_ctor_set_uint8(v_reuseFailAlloc_3233_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3223_);
lean_ctor_set_uint8(v_reuseFailAlloc_3233_, sizeof(void*)*28 + 5, v_allowImportAll_3224_);
lean_ctor_set_uint8(v_reuseFailAlloc_3233_, sizeof(void*)*28 + 6, v_fixedToolchain_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__2(lean_object* v_f_3236_, lean_object* v_cfg_3237_){
_start:
{
lean_object* v_toWorkspaceConfig_3238_; lean_object* v_toLeanConfig_3239_; uint8_t v_bootstrap_3240_; lean_object* v_extraDepTargets_3241_; uint8_t v_precompileModules_3242_; lean_object* v_moreGlobalServerArgs_3243_; lean_object* v_srcDir_3244_; lean_object* v_buildDir_3245_; lean_object* v_leanLibDir_3246_; lean_object* v_nativeLibDir_3247_; lean_object* v_binDir_3248_; lean_object* v_irDir_3249_; lean_object* v_releaseRepo_3250_; lean_object* v_buildArchive_3251_; uint8_t v_preferReleaseBuild_3252_; lean_object* v_testDriver_3253_; lean_object* v_testDriverArgs_3254_; lean_object* v_lintDriver_3255_; lean_object* v_lintDriverArgs_3256_; lean_object* v_version_3257_; lean_object* v_versionTags_3258_; lean_object* v_description_3259_; lean_object* v_keywords_3260_; lean_object* v_homepage_3261_; lean_object* v_license_3262_; lean_object* v_licenseFiles_3263_; lean_object* v_readmeFile_3264_; uint8_t v_reservoir_3265_; lean_object* v_enableArtifactCache_x3f_3266_; lean_object* v_restoreAllArtifacts_x3f_3267_; uint8_t v_libPrefixOnWindows_3268_; uint8_t v_allowImportAll_3269_; lean_object* v_builtinLint_x3f_3270_; lean_object* v_checks_3271_; uint8_t v_fixedToolchain_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3280_; 
v_toWorkspaceConfig_3238_ = lean_ctor_get(v_cfg_3237_, 0);
v_toLeanConfig_3239_ = lean_ctor_get(v_cfg_3237_, 1);
v_bootstrap_3240_ = lean_ctor_get_uint8(v_cfg_3237_, sizeof(void*)*28);
v_extraDepTargets_3241_ = lean_ctor_get(v_cfg_3237_, 2);
v_precompileModules_3242_ = lean_ctor_get_uint8(v_cfg_3237_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3243_ = lean_ctor_get(v_cfg_3237_, 3);
v_srcDir_3244_ = lean_ctor_get(v_cfg_3237_, 4);
v_buildDir_3245_ = lean_ctor_get(v_cfg_3237_, 5);
v_leanLibDir_3246_ = lean_ctor_get(v_cfg_3237_, 6);
v_nativeLibDir_3247_ = lean_ctor_get(v_cfg_3237_, 7);
v_binDir_3248_ = lean_ctor_get(v_cfg_3237_, 8);
v_irDir_3249_ = lean_ctor_get(v_cfg_3237_, 9);
v_releaseRepo_3250_ = lean_ctor_get(v_cfg_3237_, 10);
v_buildArchive_3251_ = lean_ctor_get(v_cfg_3237_, 11);
v_preferReleaseBuild_3252_ = lean_ctor_get_uint8(v_cfg_3237_, sizeof(void*)*28 + 2);
v_testDriver_3253_ = lean_ctor_get(v_cfg_3237_, 12);
v_testDriverArgs_3254_ = lean_ctor_get(v_cfg_3237_, 13);
v_lintDriver_3255_ = lean_ctor_get(v_cfg_3237_, 14);
v_lintDriverArgs_3256_ = lean_ctor_get(v_cfg_3237_, 15);
v_version_3257_ = lean_ctor_get(v_cfg_3237_, 16);
v_versionTags_3258_ = lean_ctor_get(v_cfg_3237_, 17);
v_description_3259_ = lean_ctor_get(v_cfg_3237_, 18);
v_keywords_3260_ = lean_ctor_get(v_cfg_3237_, 19);
v_homepage_3261_ = lean_ctor_get(v_cfg_3237_, 20);
v_license_3262_ = lean_ctor_get(v_cfg_3237_, 21);
v_licenseFiles_3263_ = lean_ctor_get(v_cfg_3237_, 22);
v_readmeFile_3264_ = lean_ctor_get(v_cfg_3237_, 23);
v_reservoir_3265_ = lean_ctor_get_uint8(v_cfg_3237_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3266_ = lean_ctor_get(v_cfg_3237_, 24);
v_restoreAllArtifacts_x3f_3267_ = lean_ctor_get(v_cfg_3237_, 25);
v_libPrefixOnWindows_3268_ = lean_ctor_get_uint8(v_cfg_3237_, sizeof(void*)*28 + 4);
v_allowImportAll_3269_ = lean_ctor_get_uint8(v_cfg_3237_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3270_ = lean_ctor_get(v_cfg_3237_, 26);
v_checks_3271_ = lean_ctor_get(v_cfg_3237_, 27);
v_fixedToolchain_3272_ = lean_ctor_get_uint8(v_cfg_3237_, sizeof(void*)*28 + 6);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_cfg_3237_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3274_ = v_cfg_3237_;
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_checks_3271_);
lean_inc(v_builtinLint_x3f_3270_);
lean_inc(v_restoreAllArtifacts_x3f_3267_);
lean_inc(v_enableArtifactCache_x3f_3266_);
lean_inc(v_readmeFile_3264_);
lean_inc(v_licenseFiles_3263_);
lean_inc(v_license_3262_);
lean_inc(v_homepage_3261_);
lean_inc(v_keywords_3260_);
lean_inc(v_description_3259_);
lean_inc(v_versionTags_3258_);
lean_inc(v_version_3257_);
lean_inc(v_lintDriverArgs_3256_);
lean_inc(v_lintDriver_3255_);
lean_inc(v_testDriverArgs_3254_);
lean_inc(v_testDriver_3253_);
lean_inc(v_buildArchive_3251_);
lean_inc(v_releaseRepo_3250_);
lean_inc(v_irDir_3249_);
lean_inc(v_binDir_3248_);
lean_inc(v_nativeLibDir_3247_);
lean_inc(v_leanLibDir_3246_);
lean_inc(v_buildDir_3245_);
lean_inc(v_srcDir_3244_);
lean_inc(v_moreGlobalServerArgs_3243_);
lean_inc(v_extraDepTargets_3241_);
lean_inc(v_toLeanConfig_3239_);
lean_inc(v_toWorkspaceConfig_3238_);
lean_dec(v_cfg_3237_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3276_ = lean_apply_1(v_f_3236_, v_readmeFile_3264_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 23, v___x_3276_);
v___x_3278_ = v___x_3274_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_toWorkspaceConfig_3238_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_toLeanConfig_3239_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v_extraDepTargets_3241_);
lean_ctor_set(v_reuseFailAlloc_3279_, 3, v_moreGlobalServerArgs_3243_);
lean_ctor_set(v_reuseFailAlloc_3279_, 4, v_srcDir_3244_);
lean_ctor_set(v_reuseFailAlloc_3279_, 5, v_buildDir_3245_);
lean_ctor_set(v_reuseFailAlloc_3279_, 6, v_leanLibDir_3246_);
lean_ctor_set(v_reuseFailAlloc_3279_, 7, v_nativeLibDir_3247_);
lean_ctor_set(v_reuseFailAlloc_3279_, 8, v_binDir_3248_);
lean_ctor_set(v_reuseFailAlloc_3279_, 9, v_irDir_3249_);
lean_ctor_set(v_reuseFailAlloc_3279_, 10, v_releaseRepo_3250_);
lean_ctor_set(v_reuseFailAlloc_3279_, 11, v_buildArchive_3251_);
lean_ctor_set(v_reuseFailAlloc_3279_, 12, v_testDriver_3253_);
lean_ctor_set(v_reuseFailAlloc_3279_, 13, v_testDriverArgs_3254_);
lean_ctor_set(v_reuseFailAlloc_3279_, 14, v_lintDriver_3255_);
lean_ctor_set(v_reuseFailAlloc_3279_, 15, v_lintDriverArgs_3256_);
lean_ctor_set(v_reuseFailAlloc_3279_, 16, v_version_3257_);
lean_ctor_set(v_reuseFailAlloc_3279_, 17, v_versionTags_3258_);
lean_ctor_set(v_reuseFailAlloc_3279_, 18, v_description_3259_);
lean_ctor_set(v_reuseFailAlloc_3279_, 19, v_keywords_3260_);
lean_ctor_set(v_reuseFailAlloc_3279_, 20, v_homepage_3261_);
lean_ctor_set(v_reuseFailAlloc_3279_, 21, v_license_3262_);
lean_ctor_set(v_reuseFailAlloc_3279_, 22, v_licenseFiles_3263_);
lean_ctor_set(v_reuseFailAlloc_3279_, 23, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3279_, 24, v_enableArtifactCache_x3f_3266_);
lean_ctor_set(v_reuseFailAlloc_3279_, 25, v_restoreAllArtifacts_x3f_3267_);
lean_ctor_set(v_reuseFailAlloc_3279_, 26, v_builtinLint_x3f_3270_);
lean_ctor_set(v_reuseFailAlloc_3279_, 27, v_checks_3271_);
lean_ctor_set_uint8(v_reuseFailAlloc_3279_, sizeof(void*)*28, v_bootstrap_3240_);
lean_ctor_set_uint8(v_reuseFailAlloc_3279_, sizeof(void*)*28 + 1, v_precompileModules_3242_);
lean_ctor_set_uint8(v_reuseFailAlloc_3279_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3252_);
lean_ctor_set_uint8(v_reuseFailAlloc_3279_, sizeof(void*)*28 + 3, v_reservoir_3265_);
lean_ctor_set_uint8(v_reuseFailAlloc_3279_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3268_);
lean_ctor_set_uint8(v_reuseFailAlloc_3279_, sizeof(void*)*28 + 5, v_allowImportAll_3269_);
lean_ctor_set_uint8(v_reuseFailAlloc_3279_, sizeof(void*)*28 + 6, v_fixedToolchain_3272_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3(lean_object* v_x_3281_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__7));
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3___boxed(lean_object* v_x_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3(v_x_3283_);
lean_dec_ref(v_x_3283_);
return v_res_3284_;
}
}
lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg(){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___redArg___closed__4));
return v___x_3295_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_readmeFile___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3296_;
v_res_3296_ = l_Lake_PackageConfig_readmeFile___proj___redArg();
stack->m_obj
 = v_res_3296_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___boxed(lean_object* v___dummy_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lake_PackageConfig_readmeFile___proj___redArg();
return v_res_3298_;
}
}
static lean_object* _init_l_Lake_PackageConfig_readmeFile___proj___closed__0(void){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lake_PackageConfig_readmeFile___proj___redArg();
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object* v_p_3300_, lean_object* v_n_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_obj_once(&l_Lake_PackageConfig_readmeFile___proj___closed__0, &l_Lake_PackageConfig_readmeFile___proj___closed__0_once, _init_l_Lake_PackageConfig_readmeFile___proj___closed__0);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object* v_p_3303_, lean_object* v_n_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lake_PackageConfig_readmeFile___proj(v_p_3303_, v_n_3304_);
lean_dec(v_n_3304_);
lean_dec(v_p_3303_);
return v_res_3305_;
}
}
lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___redArg(){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_obj_once(&l_Lake_PackageConfig_readmeFile___proj___closed__0, &l_Lake_PackageConfig_readmeFile___proj___closed__0_once, _init_l_Lake_PackageConfig_readmeFile___proj___closed__0);
return v___x_3307_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_readmeFile_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3308_;
v_res_3308_ = l_Lake_PackageConfig_readmeFile_instConfigField___redArg();
stack->m_obj
 = v_res_3308_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___redArg___boxed(lean_object* v___dummy_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lake_PackageConfig_readmeFile_instConfigField___redArg();
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object* v_p_3311_, lean_object* v_n_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_obj_once(&l_Lake_PackageConfig_readmeFile___proj___closed__0, &l_Lake_PackageConfig_readmeFile___proj___closed__0_once, _init_l_Lake_PackageConfig_readmeFile___proj___closed__0);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object* v_p_3314_, lean_object* v_n_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lake_PackageConfig_readmeFile_instConfigField(v_p_3314_, v_n_3315_);
lean_dec(v_n_3315_);
lean_dec(v_p_3314_);
return v_res_3316_;
}
}
uint8_t l_Lake_PackageConfig_reservoir___proj___redArg___lam__0(lean_object* v_cfg_3317_){
_start:
{
uint8_t v_reservoir_3318_; 
v_reservoir_3318_ = lean_ctor_get_uint8(v_cfg_3317_, sizeof(void*)*28 + 3);
return v_reservoir_3318_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_reservoir___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_3317_ = stack[0].m_obj;
uint8_t v_res_3319_;
v_res_3319_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__0(v_cfg_3317_);
stack->m_num = v_res_3319_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__0___boxed(lean_object* v_cfg_3320_){
_start:
{
uint8_t v_res_3321_; lean_object* v_r_3322_; 
v_res_3321_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__0(v_cfg_3320_);
lean_dec_ref(v_cfg_3320_);
v_r_3322_ = lean_box(v_res_3321_);
return v_r_3322_;
}
}
lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__1(uint8_t v_val_3323_, lean_object* v_cfg_3324_){
_start:
{
lean_object* v_toWorkspaceConfig_3325_; lean_object* v_toLeanConfig_3326_; uint8_t v_bootstrap_3327_; lean_object* v_extraDepTargets_3328_; uint8_t v_precompileModules_3329_; lean_object* v_moreGlobalServerArgs_3330_; lean_object* v_srcDir_3331_; lean_object* v_buildDir_3332_; lean_object* v_leanLibDir_3333_; lean_object* v_nativeLibDir_3334_; lean_object* v_binDir_3335_; lean_object* v_irDir_3336_; lean_object* v_releaseRepo_3337_; lean_object* v_buildArchive_3338_; uint8_t v_preferReleaseBuild_3339_; lean_object* v_testDriver_3340_; lean_object* v_testDriverArgs_3341_; lean_object* v_lintDriver_3342_; lean_object* v_lintDriverArgs_3343_; lean_object* v_version_3344_; lean_object* v_versionTags_3345_; lean_object* v_description_3346_; lean_object* v_keywords_3347_; lean_object* v_homepage_3348_; lean_object* v_license_3349_; lean_object* v_licenseFiles_3350_; lean_object* v_readmeFile_3351_; lean_object* v_enableArtifactCache_x3f_3352_; lean_object* v_restoreAllArtifacts_x3f_3353_; uint8_t v_libPrefixOnWindows_3354_; uint8_t v_allowImportAll_3355_; lean_object* v_builtinLint_x3f_3356_; lean_object* v_checks_3357_; uint8_t v_fixedToolchain_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
v_toWorkspaceConfig_3325_ = lean_ctor_get(v_cfg_3324_, 0);
v_toLeanConfig_3326_ = lean_ctor_get(v_cfg_3324_, 1);
v_bootstrap_3327_ = lean_ctor_get_uint8(v_cfg_3324_, sizeof(void*)*28);
v_extraDepTargets_3328_ = lean_ctor_get(v_cfg_3324_, 2);
v_precompileModules_3329_ = lean_ctor_get_uint8(v_cfg_3324_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3330_ = lean_ctor_get(v_cfg_3324_, 3);
v_srcDir_3331_ = lean_ctor_get(v_cfg_3324_, 4);
v_buildDir_3332_ = lean_ctor_get(v_cfg_3324_, 5);
v_leanLibDir_3333_ = lean_ctor_get(v_cfg_3324_, 6);
v_nativeLibDir_3334_ = lean_ctor_get(v_cfg_3324_, 7);
v_binDir_3335_ = lean_ctor_get(v_cfg_3324_, 8);
v_irDir_3336_ = lean_ctor_get(v_cfg_3324_, 9);
v_releaseRepo_3337_ = lean_ctor_get(v_cfg_3324_, 10);
v_buildArchive_3338_ = lean_ctor_get(v_cfg_3324_, 11);
v_preferReleaseBuild_3339_ = lean_ctor_get_uint8(v_cfg_3324_, sizeof(void*)*28 + 2);
v_testDriver_3340_ = lean_ctor_get(v_cfg_3324_, 12);
v_testDriverArgs_3341_ = lean_ctor_get(v_cfg_3324_, 13);
v_lintDriver_3342_ = lean_ctor_get(v_cfg_3324_, 14);
v_lintDriverArgs_3343_ = lean_ctor_get(v_cfg_3324_, 15);
v_version_3344_ = lean_ctor_get(v_cfg_3324_, 16);
v_versionTags_3345_ = lean_ctor_get(v_cfg_3324_, 17);
v_description_3346_ = lean_ctor_get(v_cfg_3324_, 18);
v_keywords_3347_ = lean_ctor_get(v_cfg_3324_, 19);
v_homepage_3348_ = lean_ctor_get(v_cfg_3324_, 20);
v_license_3349_ = lean_ctor_get(v_cfg_3324_, 21);
v_licenseFiles_3350_ = lean_ctor_get(v_cfg_3324_, 22);
v_readmeFile_3351_ = lean_ctor_get(v_cfg_3324_, 23);
v_enableArtifactCache_x3f_3352_ = lean_ctor_get(v_cfg_3324_, 24);
v_restoreAllArtifacts_x3f_3353_ = lean_ctor_get(v_cfg_3324_, 25);
v_libPrefixOnWindows_3354_ = lean_ctor_get_uint8(v_cfg_3324_, sizeof(void*)*28 + 4);
v_allowImportAll_3355_ = lean_ctor_get_uint8(v_cfg_3324_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3356_ = lean_ctor_get(v_cfg_3324_, 26);
v_checks_3357_ = lean_ctor_get(v_cfg_3324_, 27);
v_fixedToolchain_3358_ = lean_ctor_get_uint8(v_cfg_3324_, sizeof(void*)*28 + 6);
v_isSharedCheck_3365_ = !lean_is_exclusive(v_cfg_3324_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v_cfg_3324_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_checks_3357_);
lean_inc(v_builtinLint_x3f_3356_);
lean_inc(v_restoreAllArtifacts_x3f_3353_);
lean_inc(v_enableArtifactCache_x3f_3352_);
lean_inc(v_readmeFile_3351_);
lean_inc(v_licenseFiles_3350_);
lean_inc(v_license_3349_);
lean_inc(v_homepage_3348_);
lean_inc(v_keywords_3347_);
lean_inc(v_description_3346_);
lean_inc(v_versionTags_3345_);
lean_inc(v_version_3344_);
lean_inc(v_lintDriverArgs_3343_);
lean_inc(v_lintDriver_3342_);
lean_inc(v_testDriverArgs_3341_);
lean_inc(v_testDriver_3340_);
lean_inc(v_buildArchive_3338_);
lean_inc(v_releaseRepo_3337_);
lean_inc(v_irDir_3336_);
lean_inc(v_binDir_3335_);
lean_inc(v_nativeLibDir_3334_);
lean_inc(v_leanLibDir_3333_);
lean_inc(v_buildDir_3332_);
lean_inc(v_srcDir_3331_);
lean_inc(v_moreGlobalServerArgs_3330_);
lean_inc(v_extraDepTargets_3328_);
lean_inc(v_toLeanConfig_3326_);
lean_inc(v_toWorkspaceConfig_3325_);
lean_dec(v_cfg_3324_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_toWorkspaceConfig_3325_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_toLeanConfig_3326_);
lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_extraDepTargets_3328_);
lean_ctor_set(v_reuseFailAlloc_3364_, 3, v_moreGlobalServerArgs_3330_);
lean_ctor_set(v_reuseFailAlloc_3364_, 4, v_srcDir_3331_);
lean_ctor_set(v_reuseFailAlloc_3364_, 5, v_buildDir_3332_);
lean_ctor_set(v_reuseFailAlloc_3364_, 6, v_leanLibDir_3333_);
lean_ctor_set(v_reuseFailAlloc_3364_, 7, v_nativeLibDir_3334_);
lean_ctor_set(v_reuseFailAlloc_3364_, 8, v_binDir_3335_);
lean_ctor_set(v_reuseFailAlloc_3364_, 9, v_irDir_3336_);
lean_ctor_set(v_reuseFailAlloc_3364_, 10, v_releaseRepo_3337_);
lean_ctor_set(v_reuseFailAlloc_3364_, 11, v_buildArchive_3338_);
lean_ctor_set(v_reuseFailAlloc_3364_, 12, v_testDriver_3340_);
lean_ctor_set(v_reuseFailAlloc_3364_, 13, v_testDriverArgs_3341_);
lean_ctor_set(v_reuseFailAlloc_3364_, 14, v_lintDriver_3342_);
lean_ctor_set(v_reuseFailAlloc_3364_, 15, v_lintDriverArgs_3343_);
lean_ctor_set(v_reuseFailAlloc_3364_, 16, v_version_3344_);
lean_ctor_set(v_reuseFailAlloc_3364_, 17, v_versionTags_3345_);
lean_ctor_set(v_reuseFailAlloc_3364_, 18, v_description_3346_);
lean_ctor_set(v_reuseFailAlloc_3364_, 19, v_keywords_3347_);
lean_ctor_set(v_reuseFailAlloc_3364_, 20, v_homepage_3348_);
lean_ctor_set(v_reuseFailAlloc_3364_, 21, v_license_3349_);
lean_ctor_set(v_reuseFailAlloc_3364_, 22, v_licenseFiles_3350_);
lean_ctor_set(v_reuseFailAlloc_3364_, 23, v_readmeFile_3351_);
lean_ctor_set(v_reuseFailAlloc_3364_, 24, v_enableArtifactCache_x3f_3352_);
lean_ctor_set(v_reuseFailAlloc_3364_, 25, v_restoreAllArtifacts_x3f_3353_);
lean_ctor_set(v_reuseFailAlloc_3364_, 26, v_builtinLint_x3f_3356_);
lean_ctor_set(v_reuseFailAlloc_3364_, 27, v_checks_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3364_, sizeof(void*)*28, v_bootstrap_3327_);
lean_ctor_set_uint8(v_reuseFailAlloc_3364_, sizeof(void*)*28 + 1, v_precompileModules_3329_);
lean_ctor_set_uint8(v_reuseFailAlloc_3364_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3339_);
lean_ctor_set_uint8(v_reuseFailAlloc_3364_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3354_);
lean_ctor_set_uint8(v_reuseFailAlloc_3364_, sizeof(void*)*28 + 5, v_allowImportAll_3355_);
lean_ctor_set_uint8(v_reuseFailAlloc_3364_, sizeof(void*)*28 + 6, v_fixedToolchain_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*28 + 3, v_val_3323_);
return v___x_3363_;
}
}
}
}
LEAN_EXPORT void l_Lake_PackageConfig_reservoir___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_3323_ = stack[0].m_num;
lean_object* v_cfg_3324_ = stack[1].m_obj;
lean_object* v_res_3366_;
v_res_3366_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__1(v_val_3323_, v_cfg_3324_);
stack->m_obj
 = v_res_3366_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__1___boxed(lean_object* v_val_3367_, lean_object* v_cfg_3368_){
_start:
{
uint8_t v_val_143__boxed_3369_; lean_object* v_res_3370_; 
v_val_143__boxed_3369_ = lean_unbox(v_val_3367_);
v_res_3370_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__1(v_val_143__boxed_3369_, v_cfg_3368_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__2(lean_object* v_f_3371_, lean_object* v_cfg_3372_){
_start:
{
lean_object* v_toWorkspaceConfig_3373_; lean_object* v_toLeanConfig_3374_; uint8_t v_bootstrap_3375_; lean_object* v_extraDepTargets_3376_; uint8_t v_precompileModules_3377_; lean_object* v_moreGlobalServerArgs_3378_; lean_object* v_srcDir_3379_; lean_object* v_buildDir_3380_; lean_object* v_leanLibDir_3381_; lean_object* v_nativeLibDir_3382_; lean_object* v_binDir_3383_; lean_object* v_irDir_3384_; lean_object* v_releaseRepo_3385_; lean_object* v_buildArchive_3386_; uint8_t v_preferReleaseBuild_3387_; lean_object* v_testDriver_3388_; lean_object* v_testDriverArgs_3389_; lean_object* v_lintDriver_3390_; lean_object* v_lintDriverArgs_3391_; lean_object* v_version_3392_; lean_object* v_versionTags_3393_; lean_object* v_description_3394_; lean_object* v_keywords_3395_; lean_object* v_homepage_3396_; lean_object* v_license_3397_; lean_object* v_licenseFiles_3398_; lean_object* v_readmeFile_3399_; uint8_t v_reservoir_3400_; lean_object* v_enableArtifactCache_x3f_3401_; lean_object* v_restoreAllArtifacts_x3f_3402_; uint8_t v_libPrefixOnWindows_3403_; uint8_t v_allowImportAll_3404_; lean_object* v_builtinLint_x3f_3405_; lean_object* v_checks_3406_; uint8_t v_fixedToolchain_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3417_; 
v_toWorkspaceConfig_3373_ = lean_ctor_get(v_cfg_3372_, 0);
v_toLeanConfig_3374_ = lean_ctor_get(v_cfg_3372_, 1);
v_bootstrap_3375_ = lean_ctor_get_uint8(v_cfg_3372_, sizeof(void*)*28);
v_extraDepTargets_3376_ = lean_ctor_get(v_cfg_3372_, 2);
v_precompileModules_3377_ = lean_ctor_get_uint8(v_cfg_3372_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3378_ = lean_ctor_get(v_cfg_3372_, 3);
v_srcDir_3379_ = lean_ctor_get(v_cfg_3372_, 4);
v_buildDir_3380_ = lean_ctor_get(v_cfg_3372_, 5);
v_leanLibDir_3381_ = lean_ctor_get(v_cfg_3372_, 6);
v_nativeLibDir_3382_ = lean_ctor_get(v_cfg_3372_, 7);
v_binDir_3383_ = lean_ctor_get(v_cfg_3372_, 8);
v_irDir_3384_ = lean_ctor_get(v_cfg_3372_, 9);
v_releaseRepo_3385_ = lean_ctor_get(v_cfg_3372_, 10);
v_buildArchive_3386_ = lean_ctor_get(v_cfg_3372_, 11);
v_preferReleaseBuild_3387_ = lean_ctor_get_uint8(v_cfg_3372_, sizeof(void*)*28 + 2);
v_testDriver_3388_ = lean_ctor_get(v_cfg_3372_, 12);
v_testDriverArgs_3389_ = lean_ctor_get(v_cfg_3372_, 13);
v_lintDriver_3390_ = lean_ctor_get(v_cfg_3372_, 14);
v_lintDriverArgs_3391_ = lean_ctor_get(v_cfg_3372_, 15);
v_version_3392_ = lean_ctor_get(v_cfg_3372_, 16);
v_versionTags_3393_ = lean_ctor_get(v_cfg_3372_, 17);
v_description_3394_ = lean_ctor_get(v_cfg_3372_, 18);
v_keywords_3395_ = lean_ctor_get(v_cfg_3372_, 19);
v_homepage_3396_ = lean_ctor_get(v_cfg_3372_, 20);
v_license_3397_ = lean_ctor_get(v_cfg_3372_, 21);
v_licenseFiles_3398_ = lean_ctor_get(v_cfg_3372_, 22);
v_readmeFile_3399_ = lean_ctor_get(v_cfg_3372_, 23);
v_reservoir_3400_ = lean_ctor_get_uint8(v_cfg_3372_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3401_ = lean_ctor_get(v_cfg_3372_, 24);
v_restoreAllArtifacts_x3f_3402_ = lean_ctor_get(v_cfg_3372_, 25);
v_libPrefixOnWindows_3403_ = lean_ctor_get_uint8(v_cfg_3372_, sizeof(void*)*28 + 4);
v_allowImportAll_3404_ = lean_ctor_get_uint8(v_cfg_3372_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3405_ = lean_ctor_get(v_cfg_3372_, 26);
v_checks_3406_ = lean_ctor_get(v_cfg_3372_, 27);
v_fixedToolchain_3407_ = lean_ctor_get_uint8(v_cfg_3372_, sizeof(void*)*28 + 6);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_cfg_3372_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3409_ = v_cfg_3372_;
v_isShared_3410_ = v_isSharedCheck_3417_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_checks_3406_);
lean_inc(v_builtinLint_x3f_3405_);
lean_inc(v_restoreAllArtifacts_x3f_3402_);
lean_inc(v_enableArtifactCache_x3f_3401_);
lean_inc(v_readmeFile_3399_);
lean_inc(v_licenseFiles_3398_);
lean_inc(v_license_3397_);
lean_inc(v_homepage_3396_);
lean_inc(v_keywords_3395_);
lean_inc(v_description_3394_);
lean_inc(v_versionTags_3393_);
lean_inc(v_version_3392_);
lean_inc(v_lintDriverArgs_3391_);
lean_inc(v_lintDriver_3390_);
lean_inc(v_testDriverArgs_3389_);
lean_inc(v_testDriver_3388_);
lean_inc(v_buildArchive_3386_);
lean_inc(v_releaseRepo_3385_);
lean_inc(v_irDir_3384_);
lean_inc(v_binDir_3383_);
lean_inc(v_nativeLibDir_3382_);
lean_inc(v_leanLibDir_3381_);
lean_inc(v_buildDir_3380_);
lean_inc(v_srcDir_3379_);
lean_inc(v_moreGlobalServerArgs_3378_);
lean_inc(v_extraDepTargets_3376_);
lean_inc(v_toLeanConfig_3374_);
lean_inc(v_toWorkspaceConfig_3373_);
lean_dec(v_cfg_3372_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3417_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3411_ = lean_box(v_reservoir_3400_);
v___x_3412_ = lean_apply_1(v_f_3371_, v___x_3411_);
if (v_isShared_3410_ == 0)
{
v___x_3414_ = v___x_3409_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_toWorkspaceConfig_3373_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_toLeanConfig_3374_);
lean_ctor_set(v_reuseFailAlloc_3416_, 2, v_extraDepTargets_3376_);
lean_ctor_set(v_reuseFailAlloc_3416_, 3, v_moreGlobalServerArgs_3378_);
lean_ctor_set(v_reuseFailAlloc_3416_, 4, v_srcDir_3379_);
lean_ctor_set(v_reuseFailAlloc_3416_, 5, v_buildDir_3380_);
lean_ctor_set(v_reuseFailAlloc_3416_, 6, v_leanLibDir_3381_);
lean_ctor_set(v_reuseFailAlloc_3416_, 7, v_nativeLibDir_3382_);
lean_ctor_set(v_reuseFailAlloc_3416_, 8, v_binDir_3383_);
lean_ctor_set(v_reuseFailAlloc_3416_, 9, v_irDir_3384_);
lean_ctor_set(v_reuseFailAlloc_3416_, 10, v_releaseRepo_3385_);
lean_ctor_set(v_reuseFailAlloc_3416_, 11, v_buildArchive_3386_);
lean_ctor_set(v_reuseFailAlloc_3416_, 12, v_testDriver_3388_);
lean_ctor_set(v_reuseFailAlloc_3416_, 13, v_testDriverArgs_3389_);
lean_ctor_set(v_reuseFailAlloc_3416_, 14, v_lintDriver_3390_);
lean_ctor_set(v_reuseFailAlloc_3416_, 15, v_lintDriverArgs_3391_);
lean_ctor_set(v_reuseFailAlloc_3416_, 16, v_version_3392_);
lean_ctor_set(v_reuseFailAlloc_3416_, 17, v_versionTags_3393_);
lean_ctor_set(v_reuseFailAlloc_3416_, 18, v_description_3394_);
lean_ctor_set(v_reuseFailAlloc_3416_, 19, v_keywords_3395_);
lean_ctor_set(v_reuseFailAlloc_3416_, 20, v_homepage_3396_);
lean_ctor_set(v_reuseFailAlloc_3416_, 21, v_license_3397_);
lean_ctor_set(v_reuseFailAlloc_3416_, 22, v_licenseFiles_3398_);
lean_ctor_set(v_reuseFailAlloc_3416_, 23, v_readmeFile_3399_);
lean_ctor_set(v_reuseFailAlloc_3416_, 24, v_enableArtifactCache_x3f_3401_);
lean_ctor_set(v_reuseFailAlloc_3416_, 25, v_restoreAllArtifacts_x3f_3402_);
lean_ctor_set(v_reuseFailAlloc_3416_, 26, v_builtinLint_x3f_3405_);
lean_ctor_set(v_reuseFailAlloc_3416_, 27, v_checks_3406_);
lean_ctor_set_uint8(v_reuseFailAlloc_3416_, sizeof(void*)*28, v_bootstrap_3375_);
lean_ctor_set_uint8(v_reuseFailAlloc_3416_, sizeof(void*)*28 + 1, v_precompileModules_3377_);
lean_ctor_set_uint8(v_reuseFailAlloc_3416_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3387_);
v___x_3414_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
uint8_t v___x_3415_; 
v___x_3415_ = lean_unbox(v___x_3412_);
lean_ctor_set_uint8(v___x_3414_, sizeof(void*)*28 + 3, v___x_3415_);
lean_ctor_set_uint8(v___x_3414_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3403_);
lean_ctor_set_uint8(v___x_3414_, sizeof(void*)*28 + 5, v_allowImportAll_3404_);
lean_ctor_set_uint8(v___x_3414_, sizeof(void*)*28 + 6, v_fixedToolchain_3407_);
return v___x_3414_;
}
}
}
}
uint8_t l_Lake_PackageConfig_reservoir___proj___redArg___lam__3(lean_object* v_x_3418_){
_start:
{
uint8_t v___x_3419_; 
v___x_3419_ = 1;
return v___x_3419_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_reservoir___proj___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3418_ = stack[0].m_obj;
uint8_t v_res_3420_;
v_res_3420_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__3(v_x_3418_);
stack->m_num = v_res_3420_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__3___boxed(lean_object* v_x_3421_){
_start:
{
uint8_t v_res_3422_; lean_object* v_r_3423_; 
v_res_3422_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__3(v_x_3421_);
lean_dec_ref(v_x_3421_);
v_r_3423_ = lean_box(v_res_3422_);
return v_r_3423_;
}
}
lean_object* l_Lake_PackageConfig_reservoir___proj___redArg(){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = ((lean_object*)(l_Lake_PackageConfig_reservoir___proj___redArg___closed__4));
return v___x_3434_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_reservoir___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3435_;
v_res_3435_ = l_Lake_PackageConfig_reservoir___proj___redArg();
stack->m_obj
 = v_res_3435_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___boxed(lean_object* v___dummy_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lake_PackageConfig_reservoir___proj___redArg();
return v_res_3437_;
}
}
static lean_object* _init_l_Lake_PackageConfig_reservoir___proj___closed__0(void){
_start:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Lake_PackageConfig_reservoir___proj___redArg();
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object* v_p_3439_, lean_object* v_n_3440_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = lean_obj_once(&l_Lake_PackageConfig_reservoir___proj___closed__0, &l_Lake_PackageConfig_reservoir___proj___closed__0_once, _init_l_Lake_PackageConfig_reservoir___proj___closed__0);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object* v_p_3442_, lean_object* v_n_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lake_PackageConfig_reservoir___proj(v_p_3442_, v_n_3443_);
lean_dec(v_n_3443_);
lean_dec(v_p_3442_);
return v_res_3444_;
}
}
lean_object* l_Lake_PackageConfig_reservoir_instConfigField___redArg(){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_obj_once(&l_Lake_PackageConfig_reservoir___proj___closed__0, &l_Lake_PackageConfig_reservoir___proj___closed__0_once, _init_l_Lake_PackageConfig_reservoir___proj___closed__0);
return v___x_3446_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_reservoir_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3447_;
v_res_3447_ = l_Lake_PackageConfig_reservoir_instConfigField___redArg();
stack->m_obj
 = v_res_3447_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___redArg___boxed(lean_object* v___dummy_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lake_PackageConfig_reservoir_instConfigField___redArg();
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object* v_p_3450_, lean_object* v_n_3451_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_obj_once(&l_Lake_PackageConfig_reservoir___proj___closed__0, &l_Lake_PackageConfig_reservoir___proj___closed__0_once, _init_l_Lake_PackageConfig_reservoir___proj___closed__0);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object* v_p_3453_, lean_object* v_n_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lake_PackageConfig_reservoir_instConfigField(v_p_3453_, v_n_3454_);
lean_dec(v_n_3454_);
lean_dec(v_p_3453_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0(lean_object* v_cfg_3456_){
_start:
{
lean_object* v_enableArtifactCache_x3f_3457_; 
v_enableArtifactCache_x3f_3457_ = lean_ctor_get(v_cfg_3456_, 24);
lean_inc(v_enableArtifactCache_x3f_3457_);
return v_enableArtifactCache_x3f_3457_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0___boxed(lean_object* v_cfg_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0(v_cfg_3458_);
lean_dec_ref(v_cfg_3458_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__1(lean_object* v_val_3460_, lean_object* v_cfg_3461_){
_start:
{
lean_object* v_toWorkspaceConfig_3462_; lean_object* v_toLeanConfig_3463_; uint8_t v_bootstrap_3464_; lean_object* v_extraDepTargets_3465_; uint8_t v_precompileModules_3466_; lean_object* v_moreGlobalServerArgs_3467_; lean_object* v_srcDir_3468_; lean_object* v_buildDir_3469_; lean_object* v_leanLibDir_3470_; lean_object* v_nativeLibDir_3471_; lean_object* v_binDir_3472_; lean_object* v_irDir_3473_; lean_object* v_releaseRepo_3474_; lean_object* v_buildArchive_3475_; uint8_t v_preferReleaseBuild_3476_; lean_object* v_testDriver_3477_; lean_object* v_testDriverArgs_3478_; lean_object* v_lintDriver_3479_; lean_object* v_lintDriverArgs_3480_; lean_object* v_version_3481_; lean_object* v_versionTags_3482_; lean_object* v_description_3483_; lean_object* v_keywords_3484_; lean_object* v_homepage_3485_; lean_object* v_license_3486_; lean_object* v_licenseFiles_3487_; lean_object* v_readmeFile_3488_; uint8_t v_reservoir_3489_; lean_object* v_restoreAllArtifacts_x3f_3490_; uint8_t v_libPrefixOnWindows_3491_; uint8_t v_allowImportAll_3492_; lean_object* v_builtinLint_x3f_3493_; lean_object* v_checks_3494_; uint8_t v_fixedToolchain_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
v_toWorkspaceConfig_3462_ = lean_ctor_get(v_cfg_3461_, 0);
v_toLeanConfig_3463_ = lean_ctor_get(v_cfg_3461_, 1);
v_bootstrap_3464_ = lean_ctor_get_uint8(v_cfg_3461_, sizeof(void*)*28);
v_extraDepTargets_3465_ = lean_ctor_get(v_cfg_3461_, 2);
v_precompileModules_3466_ = lean_ctor_get_uint8(v_cfg_3461_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3467_ = lean_ctor_get(v_cfg_3461_, 3);
v_srcDir_3468_ = lean_ctor_get(v_cfg_3461_, 4);
v_buildDir_3469_ = lean_ctor_get(v_cfg_3461_, 5);
v_leanLibDir_3470_ = lean_ctor_get(v_cfg_3461_, 6);
v_nativeLibDir_3471_ = lean_ctor_get(v_cfg_3461_, 7);
v_binDir_3472_ = lean_ctor_get(v_cfg_3461_, 8);
v_irDir_3473_ = lean_ctor_get(v_cfg_3461_, 9);
v_releaseRepo_3474_ = lean_ctor_get(v_cfg_3461_, 10);
v_buildArchive_3475_ = lean_ctor_get(v_cfg_3461_, 11);
v_preferReleaseBuild_3476_ = lean_ctor_get_uint8(v_cfg_3461_, sizeof(void*)*28 + 2);
v_testDriver_3477_ = lean_ctor_get(v_cfg_3461_, 12);
v_testDriverArgs_3478_ = lean_ctor_get(v_cfg_3461_, 13);
v_lintDriver_3479_ = lean_ctor_get(v_cfg_3461_, 14);
v_lintDriverArgs_3480_ = lean_ctor_get(v_cfg_3461_, 15);
v_version_3481_ = lean_ctor_get(v_cfg_3461_, 16);
v_versionTags_3482_ = lean_ctor_get(v_cfg_3461_, 17);
v_description_3483_ = lean_ctor_get(v_cfg_3461_, 18);
v_keywords_3484_ = lean_ctor_get(v_cfg_3461_, 19);
v_homepage_3485_ = lean_ctor_get(v_cfg_3461_, 20);
v_license_3486_ = lean_ctor_get(v_cfg_3461_, 21);
v_licenseFiles_3487_ = lean_ctor_get(v_cfg_3461_, 22);
v_readmeFile_3488_ = lean_ctor_get(v_cfg_3461_, 23);
v_reservoir_3489_ = lean_ctor_get_uint8(v_cfg_3461_, sizeof(void*)*28 + 3);
v_restoreAllArtifacts_x3f_3490_ = lean_ctor_get(v_cfg_3461_, 25);
v_libPrefixOnWindows_3491_ = lean_ctor_get_uint8(v_cfg_3461_, sizeof(void*)*28 + 4);
v_allowImportAll_3492_ = lean_ctor_get_uint8(v_cfg_3461_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3493_ = lean_ctor_get(v_cfg_3461_, 26);
v_checks_3494_ = lean_ctor_get(v_cfg_3461_, 27);
v_fixedToolchain_3495_ = lean_ctor_get_uint8(v_cfg_3461_, sizeof(void*)*28 + 6);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_cfg_3461_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; 
v_unused_3503_ = lean_ctor_get(v_cfg_3461_, 24);
lean_dec(v_unused_3503_);
v___x_3497_ = v_cfg_3461_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_checks_3494_);
lean_inc(v_builtinLint_x3f_3493_);
lean_inc(v_restoreAllArtifacts_x3f_3490_);
lean_inc(v_readmeFile_3488_);
lean_inc(v_licenseFiles_3487_);
lean_inc(v_license_3486_);
lean_inc(v_homepage_3485_);
lean_inc(v_keywords_3484_);
lean_inc(v_description_3483_);
lean_inc(v_versionTags_3482_);
lean_inc(v_version_3481_);
lean_inc(v_lintDriverArgs_3480_);
lean_inc(v_lintDriver_3479_);
lean_inc(v_testDriverArgs_3478_);
lean_inc(v_testDriver_3477_);
lean_inc(v_buildArchive_3475_);
lean_inc(v_releaseRepo_3474_);
lean_inc(v_irDir_3473_);
lean_inc(v_binDir_3472_);
lean_inc(v_nativeLibDir_3471_);
lean_inc(v_leanLibDir_3470_);
lean_inc(v_buildDir_3469_);
lean_inc(v_srcDir_3468_);
lean_inc(v_moreGlobalServerArgs_3467_);
lean_inc(v_extraDepTargets_3465_);
lean_inc(v_toLeanConfig_3463_);
lean_inc(v_toWorkspaceConfig_3462_);
lean_dec(v_cfg_3461_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 24, v_val_3460_);
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_toWorkspaceConfig_3462_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_toLeanConfig_3463_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_extraDepTargets_3465_);
lean_ctor_set(v_reuseFailAlloc_3501_, 3, v_moreGlobalServerArgs_3467_);
lean_ctor_set(v_reuseFailAlloc_3501_, 4, v_srcDir_3468_);
lean_ctor_set(v_reuseFailAlloc_3501_, 5, v_buildDir_3469_);
lean_ctor_set(v_reuseFailAlloc_3501_, 6, v_leanLibDir_3470_);
lean_ctor_set(v_reuseFailAlloc_3501_, 7, v_nativeLibDir_3471_);
lean_ctor_set(v_reuseFailAlloc_3501_, 8, v_binDir_3472_);
lean_ctor_set(v_reuseFailAlloc_3501_, 9, v_irDir_3473_);
lean_ctor_set(v_reuseFailAlloc_3501_, 10, v_releaseRepo_3474_);
lean_ctor_set(v_reuseFailAlloc_3501_, 11, v_buildArchive_3475_);
lean_ctor_set(v_reuseFailAlloc_3501_, 12, v_testDriver_3477_);
lean_ctor_set(v_reuseFailAlloc_3501_, 13, v_testDriverArgs_3478_);
lean_ctor_set(v_reuseFailAlloc_3501_, 14, v_lintDriver_3479_);
lean_ctor_set(v_reuseFailAlloc_3501_, 15, v_lintDriverArgs_3480_);
lean_ctor_set(v_reuseFailAlloc_3501_, 16, v_version_3481_);
lean_ctor_set(v_reuseFailAlloc_3501_, 17, v_versionTags_3482_);
lean_ctor_set(v_reuseFailAlloc_3501_, 18, v_description_3483_);
lean_ctor_set(v_reuseFailAlloc_3501_, 19, v_keywords_3484_);
lean_ctor_set(v_reuseFailAlloc_3501_, 20, v_homepage_3485_);
lean_ctor_set(v_reuseFailAlloc_3501_, 21, v_license_3486_);
lean_ctor_set(v_reuseFailAlloc_3501_, 22, v_licenseFiles_3487_);
lean_ctor_set(v_reuseFailAlloc_3501_, 23, v_readmeFile_3488_);
lean_ctor_set(v_reuseFailAlloc_3501_, 24, v_val_3460_);
lean_ctor_set(v_reuseFailAlloc_3501_, 25, v_restoreAllArtifacts_x3f_3490_);
lean_ctor_set(v_reuseFailAlloc_3501_, 26, v_builtinLint_x3f_3493_);
lean_ctor_set(v_reuseFailAlloc_3501_, 27, v_checks_3494_);
lean_ctor_set_uint8(v_reuseFailAlloc_3501_, sizeof(void*)*28, v_bootstrap_3464_);
lean_ctor_set_uint8(v_reuseFailAlloc_3501_, sizeof(void*)*28 + 1, v_precompileModules_3466_);
lean_ctor_set_uint8(v_reuseFailAlloc_3501_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3476_);
lean_ctor_set_uint8(v_reuseFailAlloc_3501_, sizeof(void*)*28 + 3, v_reservoir_3489_);
lean_ctor_set_uint8(v_reuseFailAlloc_3501_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3491_);
lean_ctor_set_uint8(v_reuseFailAlloc_3501_, sizeof(void*)*28 + 5, v_allowImportAll_3492_);
lean_ctor_set_uint8(v_reuseFailAlloc_3501_, sizeof(void*)*28 + 6, v_fixedToolchain_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__2(lean_object* v_f_3504_, lean_object* v_cfg_3505_){
_start:
{
lean_object* v_toWorkspaceConfig_3506_; lean_object* v_toLeanConfig_3507_; uint8_t v_bootstrap_3508_; lean_object* v_extraDepTargets_3509_; uint8_t v_precompileModules_3510_; lean_object* v_moreGlobalServerArgs_3511_; lean_object* v_srcDir_3512_; lean_object* v_buildDir_3513_; lean_object* v_leanLibDir_3514_; lean_object* v_nativeLibDir_3515_; lean_object* v_binDir_3516_; lean_object* v_irDir_3517_; lean_object* v_releaseRepo_3518_; lean_object* v_buildArchive_3519_; uint8_t v_preferReleaseBuild_3520_; lean_object* v_testDriver_3521_; lean_object* v_testDriverArgs_3522_; lean_object* v_lintDriver_3523_; lean_object* v_lintDriverArgs_3524_; lean_object* v_version_3525_; lean_object* v_versionTags_3526_; lean_object* v_description_3527_; lean_object* v_keywords_3528_; lean_object* v_homepage_3529_; lean_object* v_license_3530_; lean_object* v_licenseFiles_3531_; lean_object* v_readmeFile_3532_; uint8_t v_reservoir_3533_; lean_object* v_enableArtifactCache_x3f_3534_; lean_object* v_restoreAllArtifacts_x3f_3535_; uint8_t v_libPrefixOnWindows_3536_; uint8_t v_allowImportAll_3537_; lean_object* v_builtinLint_x3f_3538_; lean_object* v_checks_3539_; uint8_t v_fixedToolchain_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3548_; 
v_toWorkspaceConfig_3506_ = lean_ctor_get(v_cfg_3505_, 0);
v_toLeanConfig_3507_ = lean_ctor_get(v_cfg_3505_, 1);
v_bootstrap_3508_ = lean_ctor_get_uint8(v_cfg_3505_, sizeof(void*)*28);
v_extraDepTargets_3509_ = lean_ctor_get(v_cfg_3505_, 2);
v_precompileModules_3510_ = lean_ctor_get_uint8(v_cfg_3505_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3511_ = lean_ctor_get(v_cfg_3505_, 3);
v_srcDir_3512_ = lean_ctor_get(v_cfg_3505_, 4);
v_buildDir_3513_ = lean_ctor_get(v_cfg_3505_, 5);
v_leanLibDir_3514_ = lean_ctor_get(v_cfg_3505_, 6);
v_nativeLibDir_3515_ = lean_ctor_get(v_cfg_3505_, 7);
v_binDir_3516_ = lean_ctor_get(v_cfg_3505_, 8);
v_irDir_3517_ = lean_ctor_get(v_cfg_3505_, 9);
v_releaseRepo_3518_ = lean_ctor_get(v_cfg_3505_, 10);
v_buildArchive_3519_ = lean_ctor_get(v_cfg_3505_, 11);
v_preferReleaseBuild_3520_ = lean_ctor_get_uint8(v_cfg_3505_, sizeof(void*)*28 + 2);
v_testDriver_3521_ = lean_ctor_get(v_cfg_3505_, 12);
v_testDriverArgs_3522_ = lean_ctor_get(v_cfg_3505_, 13);
v_lintDriver_3523_ = lean_ctor_get(v_cfg_3505_, 14);
v_lintDriverArgs_3524_ = lean_ctor_get(v_cfg_3505_, 15);
v_version_3525_ = lean_ctor_get(v_cfg_3505_, 16);
v_versionTags_3526_ = lean_ctor_get(v_cfg_3505_, 17);
v_description_3527_ = lean_ctor_get(v_cfg_3505_, 18);
v_keywords_3528_ = lean_ctor_get(v_cfg_3505_, 19);
v_homepage_3529_ = lean_ctor_get(v_cfg_3505_, 20);
v_license_3530_ = lean_ctor_get(v_cfg_3505_, 21);
v_licenseFiles_3531_ = lean_ctor_get(v_cfg_3505_, 22);
v_readmeFile_3532_ = lean_ctor_get(v_cfg_3505_, 23);
v_reservoir_3533_ = lean_ctor_get_uint8(v_cfg_3505_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3534_ = lean_ctor_get(v_cfg_3505_, 24);
v_restoreAllArtifacts_x3f_3535_ = lean_ctor_get(v_cfg_3505_, 25);
v_libPrefixOnWindows_3536_ = lean_ctor_get_uint8(v_cfg_3505_, sizeof(void*)*28 + 4);
v_allowImportAll_3537_ = lean_ctor_get_uint8(v_cfg_3505_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3538_ = lean_ctor_get(v_cfg_3505_, 26);
v_checks_3539_ = lean_ctor_get(v_cfg_3505_, 27);
v_fixedToolchain_3540_ = lean_ctor_get_uint8(v_cfg_3505_, sizeof(void*)*28 + 6);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_cfg_3505_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3542_ = v_cfg_3505_;
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_checks_3539_);
lean_inc(v_builtinLint_x3f_3538_);
lean_inc(v_restoreAllArtifacts_x3f_3535_);
lean_inc(v_enableArtifactCache_x3f_3534_);
lean_inc(v_readmeFile_3532_);
lean_inc(v_licenseFiles_3531_);
lean_inc(v_license_3530_);
lean_inc(v_homepage_3529_);
lean_inc(v_keywords_3528_);
lean_inc(v_description_3527_);
lean_inc(v_versionTags_3526_);
lean_inc(v_version_3525_);
lean_inc(v_lintDriverArgs_3524_);
lean_inc(v_lintDriver_3523_);
lean_inc(v_testDriverArgs_3522_);
lean_inc(v_testDriver_3521_);
lean_inc(v_buildArchive_3519_);
lean_inc(v_releaseRepo_3518_);
lean_inc(v_irDir_3517_);
lean_inc(v_binDir_3516_);
lean_inc(v_nativeLibDir_3515_);
lean_inc(v_leanLibDir_3514_);
lean_inc(v_buildDir_3513_);
lean_inc(v_srcDir_3512_);
lean_inc(v_moreGlobalServerArgs_3511_);
lean_inc(v_extraDepTargets_3509_);
lean_inc(v_toLeanConfig_3507_);
lean_inc(v_toWorkspaceConfig_3506_);
lean_dec(v_cfg_3505_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
v___x_3544_ = lean_apply_1(v_f_3504_, v_enableArtifactCache_x3f_3534_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 24, v___x_3544_);
v___x_3546_ = v___x_3542_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_toWorkspaceConfig_3506_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v_toLeanConfig_3507_);
lean_ctor_set(v_reuseFailAlloc_3547_, 2, v_extraDepTargets_3509_);
lean_ctor_set(v_reuseFailAlloc_3547_, 3, v_moreGlobalServerArgs_3511_);
lean_ctor_set(v_reuseFailAlloc_3547_, 4, v_srcDir_3512_);
lean_ctor_set(v_reuseFailAlloc_3547_, 5, v_buildDir_3513_);
lean_ctor_set(v_reuseFailAlloc_3547_, 6, v_leanLibDir_3514_);
lean_ctor_set(v_reuseFailAlloc_3547_, 7, v_nativeLibDir_3515_);
lean_ctor_set(v_reuseFailAlloc_3547_, 8, v_binDir_3516_);
lean_ctor_set(v_reuseFailAlloc_3547_, 9, v_irDir_3517_);
lean_ctor_set(v_reuseFailAlloc_3547_, 10, v_releaseRepo_3518_);
lean_ctor_set(v_reuseFailAlloc_3547_, 11, v_buildArchive_3519_);
lean_ctor_set(v_reuseFailAlloc_3547_, 12, v_testDriver_3521_);
lean_ctor_set(v_reuseFailAlloc_3547_, 13, v_testDriverArgs_3522_);
lean_ctor_set(v_reuseFailAlloc_3547_, 14, v_lintDriver_3523_);
lean_ctor_set(v_reuseFailAlloc_3547_, 15, v_lintDriverArgs_3524_);
lean_ctor_set(v_reuseFailAlloc_3547_, 16, v_version_3525_);
lean_ctor_set(v_reuseFailAlloc_3547_, 17, v_versionTags_3526_);
lean_ctor_set(v_reuseFailAlloc_3547_, 18, v_description_3527_);
lean_ctor_set(v_reuseFailAlloc_3547_, 19, v_keywords_3528_);
lean_ctor_set(v_reuseFailAlloc_3547_, 20, v_homepage_3529_);
lean_ctor_set(v_reuseFailAlloc_3547_, 21, v_license_3530_);
lean_ctor_set(v_reuseFailAlloc_3547_, 22, v_licenseFiles_3531_);
lean_ctor_set(v_reuseFailAlloc_3547_, 23, v_readmeFile_3532_);
lean_ctor_set(v_reuseFailAlloc_3547_, 24, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3547_, 25, v_restoreAllArtifacts_x3f_3535_);
lean_ctor_set(v_reuseFailAlloc_3547_, 26, v_builtinLint_x3f_3538_);
lean_ctor_set(v_reuseFailAlloc_3547_, 27, v_checks_3539_);
lean_ctor_set_uint8(v_reuseFailAlloc_3547_, sizeof(void*)*28, v_bootstrap_3508_);
lean_ctor_set_uint8(v_reuseFailAlloc_3547_, sizeof(void*)*28 + 1, v_precompileModules_3510_);
lean_ctor_set_uint8(v_reuseFailAlloc_3547_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3520_);
lean_ctor_set_uint8(v_reuseFailAlloc_3547_, sizeof(void*)*28 + 3, v_reservoir_3533_);
lean_ctor_set_uint8(v_reuseFailAlloc_3547_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3536_);
lean_ctor_set_uint8(v_reuseFailAlloc_3547_, sizeof(void*)*28 + 5, v_allowImportAll_3537_);
lean_ctor_set_uint8(v_reuseFailAlloc_3547_, sizeof(void*)*28 + 6, v_fixedToolchain_3540_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3(lean_object* v_x_3549_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_box(0);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3___boxed(lean_object* v_x_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3(v_x_3551_);
lean_dec_ref(v_x_3551_);
return v_res_3552_;
}
}
lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg(){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = ((lean_object*)(l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__4));
return v___x_3563_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3564_;
v_res_3564_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg();
stack->m_obj
 = v_res_3564_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___boxed(lean_object* v___dummy_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg();
return v_res_3566_;
}
}
static lean_object* _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0(void){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg();
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object* v_p_3568_, lean_object* v_n_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object* v_p_3571_, lean_object* v_n_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3571_, v_n_3572_);
lean_dec(v_n_3572_);
lean_dec(v_p_3571_);
return v_res_3573_;
}
}
lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3575_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3576_;
v_res_3576_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg();
stack->m_obj
 = v_res_3576_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg();
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object* v_p_3579_, lean_object* v_n_3580_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object* v_p_3582_, lean_object* v_n_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(v_p_3582_, v_n_3583_);
lean_dec(v_n_3583_);
lean_dec(v_p_3582_);
return v_res_3584_;
}
}
lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg(){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3586_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3587_;
v_res_3587_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg();
stack->m_obj
 = v_res_3587_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg___boxed(lean_object* v___dummy_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg();
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object* v_p_3590_, lean_object* v_n_3591_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object* v_p_3593_, lean_object* v_n_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField(v_p_3593_, v_n_3594_);
lean_dec(v_n_3594_);
lean_dec(v_p_3593_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0(lean_object* v_cfg_3596_){
_start:
{
lean_object* v_restoreAllArtifacts_x3f_3597_; 
v_restoreAllArtifacts_x3f_3597_ = lean_ctor_get(v_cfg_3596_, 25);
lean_inc(v_restoreAllArtifacts_x3f_3597_);
return v_restoreAllArtifacts_x3f_3597_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0___boxed(lean_object* v_cfg_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0(v_cfg_3598_);
lean_dec_ref(v_cfg_3598_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__1(lean_object* v_val_3600_, lean_object* v_cfg_3601_){
_start:
{
lean_object* v_toWorkspaceConfig_3602_; lean_object* v_toLeanConfig_3603_; uint8_t v_bootstrap_3604_; lean_object* v_extraDepTargets_3605_; uint8_t v_precompileModules_3606_; lean_object* v_moreGlobalServerArgs_3607_; lean_object* v_srcDir_3608_; lean_object* v_buildDir_3609_; lean_object* v_leanLibDir_3610_; lean_object* v_nativeLibDir_3611_; lean_object* v_binDir_3612_; lean_object* v_irDir_3613_; lean_object* v_releaseRepo_3614_; lean_object* v_buildArchive_3615_; uint8_t v_preferReleaseBuild_3616_; lean_object* v_testDriver_3617_; lean_object* v_testDriverArgs_3618_; lean_object* v_lintDriver_3619_; lean_object* v_lintDriverArgs_3620_; lean_object* v_version_3621_; lean_object* v_versionTags_3622_; lean_object* v_description_3623_; lean_object* v_keywords_3624_; lean_object* v_homepage_3625_; lean_object* v_license_3626_; lean_object* v_licenseFiles_3627_; lean_object* v_readmeFile_3628_; uint8_t v_reservoir_3629_; lean_object* v_enableArtifactCache_x3f_3630_; uint8_t v_libPrefixOnWindows_3631_; uint8_t v_allowImportAll_3632_; lean_object* v_builtinLint_x3f_3633_; lean_object* v_checks_3634_; uint8_t v_fixedToolchain_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_toWorkspaceConfig_3602_ = lean_ctor_get(v_cfg_3601_, 0);
v_toLeanConfig_3603_ = lean_ctor_get(v_cfg_3601_, 1);
v_bootstrap_3604_ = lean_ctor_get_uint8(v_cfg_3601_, sizeof(void*)*28);
v_extraDepTargets_3605_ = lean_ctor_get(v_cfg_3601_, 2);
v_precompileModules_3606_ = lean_ctor_get_uint8(v_cfg_3601_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3607_ = lean_ctor_get(v_cfg_3601_, 3);
v_srcDir_3608_ = lean_ctor_get(v_cfg_3601_, 4);
v_buildDir_3609_ = lean_ctor_get(v_cfg_3601_, 5);
v_leanLibDir_3610_ = lean_ctor_get(v_cfg_3601_, 6);
v_nativeLibDir_3611_ = lean_ctor_get(v_cfg_3601_, 7);
v_binDir_3612_ = lean_ctor_get(v_cfg_3601_, 8);
v_irDir_3613_ = lean_ctor_get(v_cfg_3601_, 9);
v_releaseRepo_3614_ = lean_ctor_get(v_cfg_3601_, 10);
v_buildArchive_3615_ = lean_ctor_get(v_cfg_3601_, 11);
v_preferReleaseBuild_3616_ = lean_ctor_get_uint8(v_cfg_3601_, sizeof(void*)*28 + 2);
v_testDriver_3617_ = lean_ctor_get(v_cfg_3601_, 12);
v_testDriverArgs_3618_ = lean_ctor_get(v_cfg_3601_, 13);
v_lintDriver_3619_ = lean_ctor_get(v_cfg_3601_, 14);
v_lintDriverArgs_3620_ = lean_ctor_get(v_cfg_3601_, 15);
v_version_3621_ = lean_ctor_get(v_cfg_3601_, 16);
v_versionTags_3622_ = lean_ctor_get(v_cfg_3601_, 17);
v_description_3623_ = lean_ctor_get(v_cfg_3601_, 18);
v_keywords_3624_ = lean_ctor_get(v_cfg_3601_, 19);
v_homepage_3625_ = lean_ctor_get(v_cfg_3601_, 20);
v_license_3626_ = lean_ctor_get(v_cfg_3601_, 21);
v_licenseFiles_3627_ = lean_ctor_get(v_cfg_3601_, 22);
v_readmeFile_3628_ = lean_ctor_get(v_cfg_3601_, 23);
v_reservoir_3629_ = lean_ctor_get_uint8(v_cfg_3601_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3630_ = lean_ctor_get(v_cfg_3601_, 24);
v_libPrefixOnWindows_3631_ = lean_ctor_get_uint8(v_cfg_3601_, sizeof(void*)*28 + 4);
v_allowImportAll_3632_ = lean_ctor_get_uint8(v_cfg_3601_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3633_ = lean_ctor_get(v_cfg_3601_, 26);
v_checks_3634_ = lean_ctor_get(v_cfg_3601_, 27);
v_fixedToolchain_3635_ = lean_ctor_get_uint8(v_cfg_3601_, sizeof(void*)*28 + 6);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_cfg_3601_);
if (v_isSharedCheck_3642_ == 0)
{
lean_object* v_unused_3643_; 
v_unused_3643_ = lean_ctor_get(v_cfg_3601_, 25);
lean_dec(v_unused_3643_);
v___x_3637_ = v_cfg_3601_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_checks_3634_);
lean_inc(v_builtinLint_x3f_3633_);
lean_inc(v_enableArtifactCache_x3f_3630_);
lean_inc(v_readmeFile_3628_);
lean_inc(v_licenseFiles_3627_);
lean_inc(v_license_3626_);
lean_inc(v_homepage_3625_);
lean_inc(v_keywords_3624_);
lean_inc(v_description_3623_);
lean_inc(v_versionTags_3622_);
lean_inc(v_version_3621_);
lean_inc(v_lintDriverArgs_3620_);
lean_inc(v_lintDriver_3619_);
lean_inc(v_testDriverArgs_3618_);
lean_inc(v_testDriver_3617_);
lean_inc(v_buildArchive_3615_);
lean_inc(v_releaseRepo_3614_);
lean_inc(v_irDir_3613_);
lean_inc(v_binDir_3612_);
lean_inc(v_nativeLibDir_3611_);
lean_inc(v_leanLibDir_3610_);
lean_inc(v_buildDir_3609_);
lean_inc(v_srcDir_3608_);
lean_inc(v_moreGlobalServerArgs_3607_);
lean_inc(v_extraDepTargets_3605_);
lean_inc(v_toLeanConfig_3603_);
lean_inc(v_toWorkspaceConfig_3602_);
lean_dec(v_cfg_3601_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 25, v_val_3600_);
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_toWorkspaceConfig_3602_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_toLeanConfig_3603_);
lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_extraDepTargets_3605_);
lean_ctor_set(v_reuseFailAlloc_3641_, 3, v_moreGlobalServerArgs_3607_);
lean_ctor_set(v_reuseFailAlloc_3641_, 4, v_srcDir_3608_);
lean_ctor_set(v_reuseFailAlloc_3641_, 5, v_buildDir_3609_);
lean_ctor_set(v_reuseFailAlloc_3641_, 6, v_leanLibDir_3610_);
lean_ctor_set(v_reuseFailAlloc_3641_, 7, v_nativeLibDir_3611_);
lean_ctor_set(v_reuseFailAlloc_3641_, 8, v_binDir_3612_);
lean_ctor_set(v_reuseFailAlloc_3641_, 9, v_irDir_3613_);
lean_ctor_set(v_reuseFailAlloc_3641_, 10, v_releaseRepo_3614_);
lean_ctor_set(v_reuseFailAlloc_3641_, 11, v_buildArchive_3615_);
lean_ctor_set(v_reuseFailAlloc_3641_, 12, v_testDriver_3617_);
lean_ctor_set(v_reuseFailAlloc_3641_, 13, v_testDriverArgs_3618_);
lean_ctor_set(v_reuseFailAlloc_3641_, 14, v_lintDriver_3619_);
lean_ctor_set(v_reuseFailAlloc_3641_, 15, v_lintDriverArgs_3620_);
lean_ctor_set(v_reuseFailAlloc_3641_, 16, v_version_3621_);
lean_ctor_set(v_reuseFailAlloc_3641_, 17, v_versionTags_3622_);
lean_ctor_set(v_reuseFailAlloc_3641_, 18, v_description_3623_);
lean_ctor_set(v_reuseFailAlloc_3641_, 19, v_keywords_3624_);
lean_ctor_set(v_reuseFailAlloc_3641_, 20, v_homepage_3625_);
lean_ctor_set(v_reuseFailAlloc_3641_, 21, v_license_3626_);
lean_ctor_set(v_reuseFailAlloc_3641_, 22, v_licenseFiles_3627_);
lean_ctor_set(v_reuseFailAlloc_3641_, 23, v_readmeFile_3628_);
lean_ctor_set(v_reuseFailAlloc_3641_, 24, v_enableArtifactCache_x3f_3630_);
lean_ctor_set(v_reuseFailAlloc_3641_, 25, v_val_3600_);
lean_ctor_set(v_reuseFailAlloc_3641_, 26, v_builtinLint_x3f_3633_);
lean_ctor_set(v_reuseFailAlloc_3641_, 27, v_checks_3634_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*28, v_bootstrap_3604_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*28 + 1, v_precompileModules_3606_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3616_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*28 + 3, v_reservoir_3629_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3631_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*28 + 5, v_allowImportAll_3632_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*28 + 6, v_fixedToolchain_3635_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__2(lean_object* v_f_3644_, lean_object* v_cfg_3645_){
_start:
{
lean_object* v_toWorkspaceConfig_3646_; lean_object* v_toLeanConfig_3647_; uint8_t v_bootstrap_3648_; lean_object* v_extraDepTargets_3649_; uint8_t v_precompileModules_3650_; lean_object* v_moreGlobalServerArgs_3651_; lean_object* v_srcDir_3652_; lean_object* v_buildDir_3653_; lean_object* v_leanLibDir_3654_; lean_object* v_nativeLibDir_3655_; lean_object* v_binDir_3656_; lean_object* v_irDir_3657_; lean_object* v_releaseRepo_3658_; lean_object* v_buildArchive_3659_; uint8_t v_preferReleaseBuild_3660_; lean_object* v_testDriver_3661_; lean_object* v_testDriverArgs_3662_; lean_object* v_lintDriver_3663_; lean_object* v_lintDriverArgs_3664_; lean_object* v_version_3665_; lean_object* v_versionTags_3666_; lean_object* v_description_3667_; lean_object* v_keywords_3668_; lean_object* v_homepage_3669_; lean_object* v_license_3670_; lean_object* v_licenseFiles_3671_; lean_object* v_readmeFile_3672_; uint8_t v_reservoir_3673_; lean_object* v_enableArtifactCache_x3f_3674_; lean_object* v_restoreAllArtifacts_x3f_3675_; uint8_t v_libPrefixOnWindows_3676_; uint8_t v_allowImportAll_3677_; lean_object* v_builtinLint_x3f_3678_; lean_object* v_checks_3679_; uint8_t v_fixedToolchain_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3688_; 
v_toWorkspaceConfig_3646_ = lean_ctor_get(v_cfg_3645_, 0);
v_toLeanConfig_3647_ = lean_ctor_get(v_cfg_3645_, 1);
v_bootstrap_3648_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*28);
v_extraDepTargets_3649_ = lean_ctor_get(v_cfg_3645_, 2);
v_precompileModules_3650_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3651_ = lean_ctor_get(v_cfg_3645_, 3);
v_srcDir_3652_ = lean_ctor_get(v_cfg_3645_, 4);
v_buildDir_3653_ = lean_ctor_get(v_cfg_3645_, 5);
v_leanLibDir_3654_ = lean_ctor_get(v_cfg_3645_, 6);
v_nativeLibDir_3655_ = lean_ctor_get(v_cfg_3645_, 7);
v_binDir_3656_ = lean_ctor_get(v_cfg_3645_, 8);
v_irDir_3657_ = lean_ctor_get(v_cfg_3645_, 9);
v_releaseRepo_3658_ = lean_ctor_get(v_cfg_3645_, 10);
v_buildArchive_3659_ = lean_ctor_get(v_cfg_3645_, 11);
v_preferReleaseBuild_3660_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*28 + 2);
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
v_reservoir_3673_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3674_ = lean_ctor_get(v_cfg_3645_, 24);
v_restoreAllArtifacts_x3f_3675_ = lean_ctor_get(v_cfg_3645_, 25);
v_libPrefixOnWindows_3676_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*28 + 4);
v_allowImportAll_3677_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3678_ = lean_ctor_get(v_cfg_3645_, 26);
v_checks_3679_ = lean_ctor_get(v_cfg_3645_, 27);
v_fixedToolchain_3680_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*28 + 6);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_cfg_3645_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3682_ = v_cfg_3645_;
v_isShared_3683_ = v_isSharedCheck_3688_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_checks_3679_);
lean_inc(v_builtinLint_x3f_3678_);
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
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3688_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3684_; lean_object* v___x_3686_; 
v___x_3684_ = lean_apply_1(v_f_3644_, v_restoreAllArtifacts_x3f_3675_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 25, v___x_3684_);
v___x_3686_ = v___x_3682_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_toWorkspaceConfig_3646_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_toLeanConfig_3647_);
lean_ctor_set(v_reuseFailAlloc_3687_, 2, v_extraDepTargets_3649_);
lean_ctor_set(v_reuseFailAlloc_3687_, 3, v_moreGlobalServerArgs_3651_);
lean_ctor_set(v_reuseFailAlloc_3687_, 4, v_srcDir_3652_);
lean_ctor_set(v_reuseFailAlloc_3687_, 5, v_buildDir_3653_);
lean_ctor_set(v_reuseFailAlloc_3687_, 6, v_leanLibDir_3654_);
lean_ctor_set(v_reuseFailAlloc_3687_, 7, v_nativeLibDir_3655_);
lean_ctor_set(v_reuseFailAlloc_3687_, 8, v_binDir_3656_);
lean_ctor_set(v_reuseFailAlloc_3687_, 9, v_irDir_3657_);
lean_ctor_set(v_reuseFailAlloc_3687_, 10, v_releaseRepo_3658_);
lean_ctor_set(v_reuseFailAlloc_3687_, 11, v_buildArchive_3659_);
lean_ctor_set(v_reuseFailAlloc_3687_, 12, v_testDriver_3661_);
lean_ctor_set(v_reuseFailAlloc_3687_, 13, v_testDriverArgs_3662_);
lean_ctor_set(v_reuseFailAlloc_3687_, 14, v_lintDriver_3663_);
lean_ctor_set(v_reuseFailAlloc_3687_, 15, v_lintDriverArgs_3664_);
lean_ctor_set(v_reuseFailAlloc_3687_, 16, v_version_3665_);
lean_ctor_set(v_reuseFailAlloc_3687_, 17, v_versionTags_3666_);
lean_ctor_set(v_reuseFailAlloc_3687_, 18, v_description_3667_);
lean_ctor_set(v_reuseFailAlloc_3687_, 19, v_keywords_3668_);
lean_ctor_set(v_reuseFailAlloc_3687_, 20, v_homepage_3669_);
lean_ctor_set(v_reuseFailAlloc_3687_, 21, v_license_3670_);
lean_ctor_set(v_reuseFailAlloc_3687_, 22, v_licenseFiles_3671_);
lean_ctor_set(v_reuseFailAlloc_3687_, 23, v_readmeFile_3672_);
lean_ctor_set(v_reuseFailAlloc_3687_, 24, v_enableArtifactCache_x3f_3674_);
lean_ctor_set(v_reuseFailAlloc_3687_, 25, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3687_, 26, v_builtinLint_x3f_3678_);
lean_ctor_set(v_reuseFailAlloc_3687_, 27, v_checks_3679_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*28, v_bootstrap_3648_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*28 + 1, v_precompileModules_3650_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3660_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*28 + 3, v_reservoir_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3676_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*28 + 5, v_allowImportAll_3677_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*28 + 6, v_fixedToolchain_3680_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg(){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = ((lean_object*)(l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__3));
return v___x_3698_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3699_;
v_res_3699_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg();
stack->m_obj
 = v_res_3699_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___boxed(lean_object* v___dummy_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg();
return v_res_3701_;
}
}
static lean_object* _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0(void){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg();
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object* v_p_3703_, lean_object* v_n_3704_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___boxed(lean_object* v_p_3706_, lean_object* v_n_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3706_, v_n_3707_);
lean_dec(v_n_3707_);
lean_dec(v_p_3706_);
return v_res_3708_;
}
}
lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_3710_; 
v___x_3710_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3710_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3711_;
v_res_3711_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg();
stack->m_obj
 = v_res_3711_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg();
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object* v_p_3714_, lean_object* v_n_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object* v_p_3717_, lean_object* v_n_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(v_p_3717_, v_n_3718_);
lean_dec(v_n_3718_);
lean_dec(v_p_3717_);
return v_res_3719_;
}
}
lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg(){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3721_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3722_;
v_res_3722_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg();
stack->m_obj
 = v_res_3722_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg___boxed(lean_object* v___dummy_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg();
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object* v_p_3725_, lean_object* v_n_3726_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object* v_p_3728_, lean_object* v_n_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(v_p_3728_, v_n_3729_);
lean_dec(v_n_3729_);
lean_dec(v_p_3728_);
return v_res_3730_;
}
}
uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0(lean_object* v_cfg_3731_){
_start:
{
uint8_t v_libPrefixOnWindows_3732_; 
v_libPrefixOnWindows_3732_ = lean_ctor_get_uint8(v_cfg_3731_, sizeof(void*)*28 + 4);
return v_libPrefixOnWindows_3732_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_3731_ = stack[0].m_obj;
uint8_t v_res_3733_;
v_res_3733_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0(v_cfg_3731_);
stack->m_num = v_res_3733_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0___boxed(lean_object* v_cfg_3734_){
_start:
{
uint8_t v_res_3735_; lean_object* v_r_3736_; 
v_res_3735_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0(v_cfg_3734_);
lean_dec_ref(v_cfg_3734_);
v_r_3736_ = lean_box(v_res_3735_);
return v_r_3736_;
}
}
lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1(uint8_t v_val_3737_, lean_object* v_cfg_3738_){
_start:
{
lean_object* v_toWorkspaceConfig_3739_; lean_object* v_toLeanConfig_3740_; uint8_t v_bootstrap_3741_; lean_object* v_extraDepTargets_3742_; uint8_t v_precompileModules_3743_; lean_object* v_moreGlobalServerArgs_3744_; lean_object* v_srcDir_3745_; lean_object* v_buildDir_3746_; lean_object* v_leanLibDir_3747_; lean_object* v_nativeLibDir_3748_; lean_object* v_binDir_3749_; lean_object* v_irDir_3750_; lean_object* v_releaseRepo_3751_; lean_object* v_buildArchive_3752_; uint8_t v_preferReleaseBuild_3753_; lean_object* v_testDriver_3754_; lean_object* v_testDriverArgs_3755_; lean_object* v_lintDriver_3756_; lean_object* v_lintDriverArgs_3757_; lean_object* v_version_3758_; lean_object* v_versionTags_3759_; lean_object* v_description_3760_; lean_object* v_keywords_3761_; lean_object* v_homepage_3762_; lean_object* v_license_3763_; lean_object* v_licenseFiles_3764_; lean_object* v_readmeFile_3765_; uint8_t v_reservoir_3766_; lean_object* v_enableArtifactCache_x3f_3767_; lean_object* v_restoreAllArtifacts_x3f_3768_; uint8_t v_allowImportAll_3769_; lean_object* v_builtinLint_x3f_3770_; lean_object* v_checks_3771_; uint8_t v_fixedToolchain_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
v_toWorkspaceConfig_3739_ = lean_ctor_get(v_cfg_3738_, 0);
v_toLeanConfig_3740_ = lean_ctor_get(v_cfg_3738_, 1);
v_bootstrap_3741_ = lean_ctor_get_uint8(v_cfg_3738_, sizeof(void*)*28);
v_extraDepTargets_3742_ = lean_ctor_get(v_cfg_3738_, 2);
v_precompileModules_3743_ = lean_ctor_get_uint8(v_cfg_3738_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3744_ = lean_ctor_get(v_cfg_3738_, 3);
v_srcDir_3745_ = lean_ctor_get(v_cfg_3738_, 4);
v_buildDir_3746_ = lean_ctor_get(v_cfg_3738_, 5);
v_leanLibDir_3747_ = lean_ctor_get(v_cfg_3738_, 6);
v_nativeLibDir_3748_ = lean_ctor_get(v_cfg_3738_, 7);
v_binDir_3749_ = lean_ctor_get(v_cfg_3738_, 8);
v_irDir_3750_ = lean_ctor_get(v_cfg_3738_, 9);
v_releaseRepo_3751_ = lean_ctor_get(v_cfg_3738_, 10);
v_buildArchive_3752_ = lean_ctor_get(v_cfg_3738_, 11);
v_preferReleaseBuild_3753_ = lean_ctor_get_uint8(v_cfg_3738_, sizeof(void*)*28 + 2);
v_testDriver_3754_ = lean_ctor_get(v_cfg_3738_, 12);
v_testDriverArgs_3755_ = lean_ctor_get(v_cfg_3738_, 13);
v_lintDriver_3756_ = lean_ctor_get(v_cfg_3738_, 14);
v_lintDriverArgs_3757_ = lean_ctor_get(v_cfg_3738_, 15);
v_version_3758_ = lean_ctor_get(v_cfg_3738_, 16);
v_versionTags_3759_ = lean_ctor_get(v_cfg_3738_, 17);
v_description_3760_ = lean_ctor_get(v_cfg_3738_, 18);
v_keywords_3761_ = lean_ctor_get(v_cfg_3738_, 19);
v_homepage_3762_ = lean_ctor_get(v_cfg_3738_, 20);
v_license_3763_ = lean_ctor_get(v_cfg_3738_, 21);
v_licenseFiles_3764_ = lean_ctor_get(v_cfg_3738_, 22);
v_readmeFile_3765_ = lean_ctor_get(v_cfg_3738_, 23);
v_reservoir_3766_ = lean_ctor_get_uint8(v_cfg_3738_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3767_ = lean_ctor_get(v_cfg_3738_, 24);
v_restoreAllArtifacts_x3f_3768_ = lean_ctor_get(v_cfg_3738_, 25);
v_allowImportAll_3769_ = lean_ctor_get_uint8(v_cfg_3738_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3770_ = lean_ctor_get(v_cfg_3738_, 26);
v_checks_3771_ = lean_ctor_get(v_cfg_3738_, 27);
v_fixedToolchain_3772_ = lean_ctor_get_uint8(v_cfg_3738_, sizeof(void*)*28 + 6);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_cfg_3738_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v_cfg_3738_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_checks_3771_);
lean_inc(v_builtinLint_x3f_3770_);
lean_inc(v_restoreAllArtifacts_x3f_3768_);
lean_inc(v_enableArtifactCache_x3f_3767_);
lean_inc(v_readmeFile_3765_);
lean_inc(v_licenseFiles_3764_);
lean_inc(v_license_3763_);
lean_inc(v_homepage_3762_);
lean_inc(v_keywords_3761_);
lean_inc(v_description_3760_);
lean_inc(v_versionTags_3759_);
lean_inc(v_version_3758_);
lean_inc(v_lintDriverArgs_3757_);
lean_inc(v_lintDriver_3756_);
lean_inc(v_testDriverArgs_3755_);
lean_inc(v_testDriver_3754_);
lean_inc(v_buildArchive_3752_);
lean_inc(v_releaseRepo_3751_);
lean_inc(v_irDir_3750_);
lean_inc(v_binDir_3749_);
lean_inc(v_nativeLibDir_3748_);
lean_inc(v_leanLibDir_3747_);
lean_inc(v_buildDir_3746_);
lean_inc(v_srcDir_3745_);
lean_inc(v_moreGlobalServerArgs_3744_);
lean_inc(v_extraDepTargets_3742_);
lean_inc(v_toLeanConfig_3740_);
lean_inc(v_toWorkspaceConfig_3739_);
lean_dec(v_cfg_3738_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_toWorkspaceConfig_3739_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_toLeanConfig_3740_);
lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_extraDepTargets_3742_);
lean_ctor_set(v_reuseFailAlloc_3778_, 3, v_moreGlobalServerArgs_3744_);
lean_ctor_set(v_reuseFailAlloc_3778_, 4, v_srcDir_3745_);
lean_ctor_set(v_reuseFailAlloc_3778_, 5, v_buildDir_3746_);
lean_ctor_set(v_reuseFailAlloc_3778_, 6, v_leanLibDir_3747_);
lean_ctor_set(v_reuseFailAlloc_3778_, 7, v_nativeLibDir_3748_);
lean_ctor_set(v_reuseFailAlloc_3778_, 8, v_binDir_3749_);
lean_ctor_set(v_reuseFailAlloc_3778_, 9, v_irDir_3750_);
lean_ctor_set(v_reuseFailAlloc_3778_, 10, v_releaseRepo_3751_);
lean_ctor_set(v_reuseFailAlloc_3778_, 11, v_buildArchive_3752_);
lean_ctor_set(v_reuseFailAlloc_3778_, 12, v_testDriver_3754_);
lean_ctor_set(v_reuseFailAlloc_3778_, 13, v_testDriverArgs_3755_);
lean_ctor_set(v_reuseFailAlloc_3778_, 14, v_lintDriver_3756_);
lean_ctor_set(v_reuseFailAlloc_3778_, 15, v_lintDriverArgs_3757_);
lean_ctor_set(v_reuseFailAlloc_3778_, 16, v_version_3758_);
lean_ctor_set(v_reuseFailAlloc_3778_, 17, v_versionTags_3759_);
lean_ctor_set(v_reuseFailAlloc_3778_, 18, v_description_3760_);
lean_ctor_set(v_reuseFailAlloc_3778_, 19, v_keywords_3761_);
lean_ctor_set(v_reuseFailAlloc_3778_, 20, v_homepage_3762_);
lean_ctor_set(v_reuseFailAlloc_3778_, 21, v_license_3763_);
lean_ctor_set(v_reuseFailAlloc_3778_, 22, v_licenseFiles_3764_);
lean_ctor_set(v_reuseFailAlloc_3778_, 23, v_readmeFile_3765_);
lean_ctor_set(v_reuseFailAlloc_3778_, 24, v_enableArtifactCache_x3f_3767_);
lean_ctor_set(v_reuseFailAlloc_3778_, 25, v_restoreAllArtifacts_x3f_3768_);
lean_ctor_set(v_reuseFailAlloc_3778_, 26, v_builtinLint_x3f_3770_);
lean_ctor_set(v_reuseFailAlloc_3778_, 27, v_checks_3771_);
lean_ctor_set_uint8(v_reuseFailAlloc_3778_, sizeof(void*)*28, v_bootstrap_3741_);
lean_ctor_set_uint8(v_reuseFailAlloc_3778_, sizeof(void*)*28 + 1, v_precompileModules_3743_);
lean_ctor_set_uint8(v_reuseFailAlloc_3778_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3753_);
lean_ctor_set_uint8(v_reuseFailAlloc_3778_, sizeof(void*)*28 + 3, v_reservoir_3766_);
lean_ctor_set_uint8(v_reuseFailAlloc_3778_, sizeof(void*)*28 + 5, v_allowImportAll_3769_);
lean_ctor_set_uint8(v_reuseFailAlloc_3778_, sizeof(void*)*28 + 6, v_fixedToolchain_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_ctor_set_uint8(v___x_3777_, sizeof(void*)*28 + 4, v_val_3737_);
return v___x_3777_;
}
}
}
}
LEAN_EXPORT void l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_3737_ = stack[0].m_num;
lean_object* v_cfg_3738_ = stack[1].m_obj;
lean_object* v_res_3780_;
v_res_3780_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1(v_val_3737_, v_cfg_3738_);
stack->m_obj
 = v_res_3780_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1___boxed(lean_object* v_val_3781_, lean_object* v_cfg_3782_){
_start:
{
uint8_t v_val_143__boxed_3783_; lean_object* v_res_3784_; 
v_val_143__boxed_3783_ = lean_unbox(v_val_3781_);
v_res_3784_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1(v_val_143__boxed_3783_, v_cfg_3782_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__2(lean_object* v_f_3785_, lean_object* v_cfg_3786_){
_start:
{
lean_object* v_toWorkspaceConfig_3787_; lean_object* v_toLeanConfig_3788_; uint8_t v_bootstrap_3789_; lean_object* v_extraDepTargets_3790_; uint8_t v_precompileModules_3791_; lean_object* v_moreGlobalServerArgs_3792_; lean_object* v_srcDir_3793_; lean_object* v_buildDir_3794_; lean_object* v_leanLibDir_3795_; lean_object* v_nativeLibDir_3796_; lean_object* v_binDir_3797_; lean_object* v_irDir_3798_; lean_object* v_releaseRepo_3799_; lean_object* v_buildArchive_3800_; uint8_t v_preferReleaseBuild_3801_; lean_object* v_testDriver_3802_; lean_object* v_testDriverArgs_3803_; lean_object* v_lintDriver_3804_; lean_object* v_lintDriverArgs_3805_; lean_object* v_version_3806_; lean_object* v_versionTags_3807_; lean_object* v_description_3808_; lean_object* v_keywords_3809_; lean_object* v_homepage_3810_; lean_object* v_license_3811_; lean_object* v_licenseFiles_3812_; lean_object* v_readmeFile_3813_; uint8_t v_reservoir_3814_; lean_object* v_enableArtifactCache_x3f_3815_; lean_object* v_restoreAllArtifacts_x3f_3816_; uint8_t v_libPrefixOnWindows_3817_; uint8_t v_allowImportAll_3818_; lean_object* v_builtinLint_x3f_3819_; lean_object* v_checks_3820_; uint8_t v_fixedToolchain_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3831_; 
v_toWorkspaceConfig_3787_ = lean_ctor_get(v_cfg_3786_, 0);
v_toLeanConfig_3788_ = lean_ctor_get(v_cfg_3786_, 1);
v_bootstrap_3789_ = lean_ctor_get_uint8(v_cfg_3786_, sizeof(void*)*28);
v_extraDepTargets_3790_ = lean_ctor_get(v_cfg_3786_, 2);
v_precompileModules_3791_ = lean_ctor_get_uint8(v_cfg_3786_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3792_ = lean_ctor_get(v_cfg_3786_, 3);
v_srcDir_3793_ = lean_ctor_get(v_cfg_3786_, 4);
v_buildDir_3794_ = lean_ctor_get(v_cfg_3786_, 5);
v_leanLibDir_3795_ = lean_ctor_get(v_cfg_3786_, 6);
v_nativeLibDir_3796_ = lean_ctor_get(v_cfg_3786_, 7);
v_binDir_3797_ = lean_ctor_get(v_cfg_3786_, 8);
v_irDir_3798_ = lean_ctor_get(v_cfg_3786_, 9);
v_releaseRepo_3799_ = lean_ctor_get(v_cfg_3786_, 10);
v_buildArchive_3800_ = lean_ctor_get(v_cfg_3786_, 11);
v_preferReleaseBuild_3801_ = lean_ctor_get_uint8(v_cfg_3786_, sizeof(void*)*28 + 2);
v_testDriver_3802_ = lean_ctor_get(v_cfg_3786_, 12);
v_testDriverArgs_3803_ = lean_ctor_get(v_cfg_3786_, 13);
v_lintDriver_3804_ = lean_ctor_get(v_cfg_3786_, 14);
v_lintDriverArgs_3805_ = lean_ctor_get(v_cfg_3786_, 15);
v_version_3806_ = lean_ctor_get(v_cfg_3786_, 16);
v_versionTags_3807_ = lean_ctor_get(v_cfg_3786_, 17);
v_description_3808_ = lean_ctor_get(v_cfg_3786_, 18);
v_keywords_3809_ = lean_ctor_get(v_cfg_3786_, 19);
v_homepage_3810_ = lean_ctor_get(v_cfg_3786_, 20);
v_license_3811_ = lean_ctor_get(v_cfg_3786_, 21);
v_licenseFiles_3812_ = lean_ctor_get(v_cfg_3786_, 22);
v_readmeFile_3813_ = lean_ctor_get(v_cfg_3786_, 23);
v_reservoir_3814_ = lean_ctor_get_uint8(v_cfg_3786_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3815_ = lean_ctor_get(v_cfg_3786_, 24);
v_restoreAllArtifacts_x3f_3816_ = lean_ctor_get(v_cfg_3786_, 25);
v_libPrefixOnWindows_3817_ = lean_ctor_get_uint8(v_cfg_3786_, sizeof(void*)*28 + 4);
v_allowImportAll_3818_ = lean_ctor_get_uint8(v_cfg_3786_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3819_ = lean_ctor_get(v_cfg_3786_, 26);
v_checks_3820_ = lean_ctor_get(v_cfg_3786_, 27);
v_fixedToolchain_3821_ = lean_ctor_get_uint8(v_cfg_3786_, sizeof(void*)*28 + 6);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_cfg_3786_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3823_ = v_cfg_3786_;
v_isShared_3824_ = v_isSharedCheck_3831_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_checks_3820_);
lean_inc(v_builtinLint_x3f_3819_);
lean_inc(v_restoreAllArtifacts_x3f_3816_);
lean_inc(v_enableArtifactCache_x3f_3815_);
lean_inc(v_readmeFile_3813_);
lean_inc(v_licenseFiles_3812_);
lean_inc(v_license_3811_);
lean_inc(v_homepage_3810_);
lean_inc(v_keywords_3809_);
lean_inc(v_description_3808_);
lean_inc(v_versionTags_3807_);
lean_inc(v_version_3806_);
lean_inc(v_lintDriverArgs_3805_);
lean_inc(v_lintDriver_3804_);
lean_inc(v_testDriverArgs_3803_);
lean_inc(v_testDriver_3802_);
lean_inc(v_buildArchive_3800_);
lean_inc(v_releaseRepo_3799_);
lean_inc(v_irDir_3798_);
lean_inc(v_binDir_3797_);
lean_inc(v_nativeLibDir_3796_);
lean_inc(v_leanLibDir_3795_);
lean_inc(v_buildDir_3794_);
lean_inc(v_srcDir_3793_);
lean_inc(v_moreGlobalServerArgs_3792_);
lean_inc(v_extraDepTargets_3790_);
lean_inc(v_toLeanConfig_3788_);
lean_inc(v_toWorkspaceConfig_3787_);
lean_dec(v_cfg_3786_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3831_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3828_; 
v___x_3825_ = lean_box(v_libPrefixOnWindows_3817_);
v___x_3826_ = lean_apply_1(v_f_3785_, v___x_3825_);
if (v_isShared_3824_ == 0)
{
v___x_3828_ = v___x_3823_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_toWorkspaceConfig_3787_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_toLeanConfig_3788_);
lean_ctor_set(v_reuseFailAlloc_3830_, 2, v_extraDepTargets_3790_);
lean_ctor_set(v_reuseFailAlloc_3830_, 3, v_moreGlobalServerArgs_3792_);
lean_ctor_set(v_reuseFailAlloc_3830_, 4, v_srcDir_3793_);
lean_ctor_set(v_reuseFailAlloc_3830_, 5, v_buildDir_3794_);
lean_ctor_set(v_reuseFailAlloc_3830_, 6, v_leanLibDir_3795_);
lean_ctor_set(v_reuseFailAlloc_3830_, 7, v_nativeLibDir_3796_);
lean_ctor_set(v_reuseFailAlloc_3830_, 8, v_binDir_3797_);
lean_ctor_set(v_reuseFailAlloc_3830_, 9, v_irDir_3798_);
lean_ctor_set(v_reuseFailAlloc_3830_, 10, v_releaseRepo_3799_);
lean_ctor_set(v_reuseFailAlloc_3830_, 11, v_buildArchive_3800_);
lean_ctor_set(v_reuseFailAlloc_3830_, 12, v_testDriver_3802_);
lean_ctor_set(v_reuseFailAlloc_3830_, 13, v_testDriverArgs_3803_);
lean_ctor_set(v_reuseFailAlloc_3830_, 14, v_lintDriver_3804_);
lean_ctor_set(v_reuseFailAlloc_3830_, 15, v_lintDriverArgs_3805_);
lean_ctor_set(v_reuseFailAlloc_3830_, 16, v_version_3806_);
lean_ctor_set(v_reuseFailAlloc_3830_, 17, v_versionTags_3807_);
lean_ctor_set(v_reuseFailAlloc_3830_, 18, v_description_3808_);
lean_ctor_set(v_reuseFailAlloc_3830_, 19, v_keywords_3809_);
lean_ctor_set(v_reuseFailAlloc_3830_, 20, v_homepage_3810_);
lean_ctor_set(v_reuseFailAlloc_3830_, 21, v_license_3811_);
lean_ctor_set(v_reuseFailAlloc_3830_, 22, v_licenseFiles_3812_);
lean_ctor_set(v_reuseFailAlloc_3830_, 23, v_readmeFile_3813_);
lean_ctor_set(v_reuseFailAlloc_3830_, 24, v_enableArtifactCache_x3f_3815_);
lean_ctor_set(v_reuseFailAlloc_3830_, 25, v_restoreAllArtifacts_x3f_3816_);
lean_ctor_set(v_reuseFailAlloc_3830_, 26, v_builtinLint_x3f_3819_);
lean_ctor_set(v_reuseFailAlloc_3830_, 27, v_checks_3820_);
lean_ctor_set_uint8(v_reuseFailAlloc_3830_, sizeof(void*)*28, v_bootstrap_3789_);
lean_ctor_set_uint8(v_reuseFailAlloc_3830_, sizeof(void*)*28 + 1, v_precompileModules_3791_);
lean_ctor_set_uint8(v_reuseFailAlloc_3830_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3801_);
lean_ctor_set_uint8(v_reuseFailAlloc_3830_, sizeof(void*)*28 + 3, v_reservoir_3814_);
v___x_3828_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
uint8_t v___x_3829_; 
v___x_3829_ = lean_unbox(v___x_3826_);
lean_ctor_set_uint8(v___x_3828_, sizeof(void*)*28 + 4, v___x_3829_);
lean_ctor_set_uint8(v___x_3828_, sizeof(void*)*28 + 5, v_allowImportAll_3818_);
lean_ctor_set_uint8(v___x_3828_, sizeof(void*)*28 + 6, v_fixedToolchain_3821_);
return v___x_3828_;
}
}
}
}
lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg(){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = ((lean_object*)(l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__3));
return v___x_3841_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3842_;
v_res_3842_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg();
stack->m_obj
 = v_res_3842_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___boxed(lean_object* v___dummy_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg();
return v_res_3844_;
}
}
static lean_object* _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0(void){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg();
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object* v_p_3846_, lean_object* v_n_3847_){
_start:
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_obj_once(&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object* v_p_3849_, lean_object* v_n_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3849_, v_n_3850_);
lean_dec(v_n_3850_);
lean_dec(v_p_3849_);
return v_res_3851_;
}
}
lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg(){
_start:
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_obj_once(&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0);
return v___x_3853_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3854_;
v_res_3854_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg();
stack->m_obj
 = v_res_3854_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg___boxed(lean_object* v___dummy_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg();
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object* v_p_3857_, lean_object* v_n_3858_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = lean_obj_once(&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_p_3860_, lean_object* v_n_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(v_p_3860_, v_n_3861_);
lean_dec(v_n_3861_);
lean_dec(v_p_3860_);
return v_res_3862_;
}
}
uint8_t l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0(lean_object* v_cfg_3863_){
_start:
{
uint8_t v_allowImportAll_3864_; 
v_allowImportAll_3864_ = lean_ctor_get_uint8(v_cfg_3863_, sizeof(void*)*28 + 5);
return v_allowImportAll_3864_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_3863_ = stack[0].m_obj;
uint8_t v_res_3865_;
v_res_3865_ = l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0(v_cfg_3863_);
stack->m_num = v_res_3865_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0___boxed(lean_object* v_cfg_3866_){
_start:
{
uint8_t v_res_3867_; lean_object* v_r_3868_; 
v_res_3867_ = l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0(v_cfg_3866_);
lean_dec_ref(v_cfg_3866_);
v_r_3868_ = lean_box(v_res_3867_);
return v_r_3868_;
}
}
lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1(uint8_t v_val_3869_, lean_object* v_cfg_3870_){
_start:
{
lean_object* v_toWorkspaceConfig_3871_; lean_object* v_toLeanConfig_3872_; uint8_t v_bootstrap_3873_; lean_object* v_extraDepTargets_3874_; uint8_t v_precompileModules_3875_; lean_object* v_moreGlobalServerArgs_3876_; lean_object* v_srcDir_3877_; lean_object* v_buildDir_3878_; lean_object* v_leanLibDir_3879_; lean_object* v_nativeLibDir_3880_; lean_object* v_binDir_3881_; lean_object* v_irDir_3882_; lean_object* v_releaseRepo_3883_; lean_object* v_buildArchive_3884_; uint8_t v_preferReleaseBuild_3885_; lean_object* v_testDriver_3886_; lean_object* v_testDriverArgs_3887_; lean_object* v_lintDriver_3888_; lean_object* v_lintDriverArgs_3889_; lean_object* v_version_3890_; lean_object* v_versionTags_3891_; lean_object* v_description_3892_; lean_object* v_keywords_3893_; lean_object* v_homepage_3894_; lean_object* v_license_3895_; lean_object* v_licenseFiles_3896_; lean_object* v_readmeFile_3897_; uint8_t v_reservoir_3898_; lean_object* v_enableArtifactCache_x3f_3899_; lean_object* v_restoreAllArtifacts_x3f_3900_; uint8_t v_libPrefixOnWindows_3901_; lean_object* v_builtinLint_x3f_3902_; lean_object* v_checks_3903_; uint8_t v_fixedToolchain_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
v_toWorkspaceConfig_3871_ = lean_ctor_get(v_cfg_3870_, 0);
v_toLeanConfig_3872_ = lean_ctor_get(v_cfg_3870_, 1);
v_bootstrap_3873_ = lean_ctor_get_uint8(v_cfg_3870_, sizeof(void*)*28);
v_extraDepTargets_3874_ = lean_ctor_get(v_cfg_3870_, 2);
v_precompileModules_3875_ = lean_ctor_get_uint8(v_cfg_3870_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3876_ = lean_ctor_get(v_cfg_3870_, 3);
v_srcDir_3877_ = lean_ctor_get(v_cfg_3870_, 4);
v_buildDir_3878_ = lean_ctor_get(v_cfg_3870_, 5);
v_leanLibDir_3879_ = lean_ctor_get(v_cfg_3870_, 6);
v_nativeLibDir_3880_ = lean_ctor_get(v_cfg_3870_, 7);
v_binDir_3881_ = lean_ctor_get(v_cfg_3870_, 8);
v_irDir_3882_ = lean_ctor_get(v_cfg_3870_, 9);
v_releaseRepo_3883_ = lean_ctor_get(v_cfg_3870_, 10);
v_buildArchive_3884_ = lean_ctor_get(v_cfg_3870_, 11);
v_preferReleaseBuild_3885_ = lean_ctor_get_uint8(v_cfg_3870_, sizeof(void*)*28 + 2);
v_testDriver_3886_ = lean_ctor_get(v_cfg_3870_, 12);
v_testDriverArgs_3887_ = lean_ctor_get(v_cfg_3870_, 13);
v_lintDriver_3888_ = lean_ctor_get(v_cfg_3870_, 14);
v_lintDriverArgs_3889_ = lean_ctor_get(v_cfg_3870_, 15);
v_version_3890_ = lean_ctor_get(v_cfg_3870_, 16);
v_versionTags_3891_ = lean_ctor_get(v_cfg_3870_, 17);
v_description_3892_ = lean_ctor_get(v_cfg_3870_, 18);
v_keywords_3893_ = lean_ctor_get(v_cfg_3870_, 19);
v_homepage_3894_ = lean_ctor_get(v_cfg_3870_, 20);
v_license_3895_ = lean_ctor_get(v_cfg_3870_, 21);
v_licenseFiles_3896_ = lean_ctor_get(v_cfg_3870_, 22);
v_readmeFile_3897_ = lean_ctor_get(v_cfg_3870_, 23);
v_reservoir_3898_ = lean_ctor_get_uint8(v_cfg_3870_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3899_ = lean_ctor_get(v_cfg_3870_, 24);
v_restoreAllArtifacts_x3f_3900_ = lean_ctor_get(v_cfg_3870_, 25);
v_libPrefixOnWindows_3901_ = lean_ctor_get_uint8(v_cfg_3870_, sizeof(void*)*28 + 4);
v_builtinLint_x3f_3902_ = lean_ctor_get(v_cfg_3870_, 26);
v_checks_3903_ = lean_ctor_get(v_cfg_3870_, 27);
v_fixedToolchain_3904_ = lean_ctor_get_uint8(v_cfg_3870_, sizeof(void*)*28 + 6);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_cfg_3870_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v_cfg_3870_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_checks_3903_);
lean_inc(v_builtinLint_x3f_3902_);
lean_inc(v_restoreAllArtifacts_x3f_3900_);
lean_inc(v_enableArtifactCache_x3f_3899_);
lean_inc(v_readmeFile_3897_);
lean_inc(v_licenseFiles_3896_);
lean_inc(v_license_3895_);
lean_inc(v_homepage_3894_);
lean_inc(v_keywords_3893_);
lean_inc(v_description_3892_);
lean_inc(v_versionTags_3891_);
lean_inc(v_version_3890_);
lean_inc(v_lintDriverArgs_3889_);
lean_inc(v_lintDriver_3888_);
lean_inc(v_testDriverArgs_3887_);
lean_inc(v_testDriver_3886_);
lean_inc(v_buildArchive_3884_);
lean_inc(v_releaseRepo_3883_);
lean_inc(v_irDir_3882_);
lean_inc(v_binDir_3881_);
lean_inc(v_nativeLibDir_3880_);
lean_inc(v_leanLibDir_3879_);
lean_inc(v_buildDir_3878_);
lean_inc(v_srcDir_3877_);
lean_inc(v_moreGlobalServerArgs_3876_);
lean_inc(v_extraDepTargets_3874_);
lean_inc(v_toLeanConfig_3872_);
lean_inc(v_toWorkspaceConfig_3871_);
lean_dec(v_cfg_3870_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_toWorkspaceConfig_3871_);
lean_ctor_set(v_reuseFailAlloc_3910_, 1, v_toLeanConfig_3872_);
lean_ctor_set(v_reuseFailAlloc_3910_, 2, v_extraDepTargets_3874_);
lean_ctor_set(v_reuseFailAlloc_3910_, 3, v_moreGlobalServerArgs_3876_);
lean_ctor_set(v_reuseFailAlloc_3910_, 4, v_srcDir_3877_);
lean_ctor_set(v_reuseFailAlloc_3910_, 5, v_buildDir_3878_);
lean_ctor_set(v_reuseFailAlloc_3910_, 6, v_leanLibDir_3879_);
lean_ctor_set(v_reuseFailAlloc_3910_, 7, v_nativeLibDir_3880_);
lean_ctor_set(v_reuseFailAlloc_3910_, 8, v_binDir_3881_);
lean_ctor_set(v_reuseFailAlloc_3910_, 9, v_irDir_3882_);
lean_ctor_set(v_reuseFailAlloc_3910_, 10, v_releaseRepo_3883_);
lean_ctor_set(v_reuseFailAlloc_3910_, 11, v_buildArchive_3884_);
lean_ctor_set(v_reuseFailAlloc_3910_, 12, v_testDriver_3886_);
lean_ctor_set(v_reuseFailAlloc_3910_, 13, v_testDriverArgs_3887_);
lean_ctor_set(v_reuseFailAlloc_3910_, 14, v_lintDriver_3888_);
lean_ctor_set(v_reuseFailAlloc_3910_, 15, v_lintDriverArgs_3889_);
lean_ctor_set(v_reuseFailAlloc_3910_, 16, v_version_3890_);
lean_ctor_set(v_reuseFailAlloc_3910_, 17, v_versionTags_3891_);
lean_ctor_set(v_reuseFailAlloc_3910_, 18, v_description_3892_);
lean_ctor_set(v_reuseFailAlloc_3910_, 19, v_keywords_3893_);
lean_ctor_set(v_reuseFailAlloc_3910_, 20, v_homepage_3894_);
lean_ctor_set(v_reuseFailAlloc_3910_, 21, v_license_3895_);
lean_ctor_set(v_reuseFailAlloc_3910_, 22, v_licenseFiles_3896_);
lean_ctor_set(v_reuseFailAlloc_3910_, 23, v_readmeFile_3897_);
lean_ctor_set(v_reuseFailAlloc_3910_, 24, v_enableArtifactCache_x3f_3899_);
lean_ctor_set(v_reuseFailAlloc_3910_, 25, v_restoreAllArtifacts_x3f_3900_);
lean_ctor_set(v_reuseFailAlloc_3910_, 26, v_builtinLint_x3f_3902_);
lean_ctor_set(v_reuseFailAlloc_3910_, 27, v_checks_3903_);
lean_ctor_set_uint8(v_reuseFailAlloc_3910_, sizeof(void*)*28, v_bootstrap_3873_);
lean_ctor_set_uint8(v_reuseFailAlloc_3910_, sizeof(void*)*28 + 1, v_precompileModules_3875_);
lean_ctor_set_uint8(v_reuseFailAlloc_3910_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3885_);
lean_ctor_set_uint8(v_reuseFailAlloc_3910_, sizeof(void*)*28 + 3, v_reservoir_3898_);
lean_ctor_set_uint8(v_reuseFailAlloc_3910_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3901_);
lean_ctor_set_uint8(v_reuseFailAlloc_3910_, sizeof(void*)*28 + 6, v_fixedToolchain_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_ctor_set_uint8(v___x_3909_, sizeof(void*)*28 + 5, v_val_3869_);
return v___x_3909_;
}
}
}
}
LEAN_EXPORT void l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_3869_ = stack[0].m_num;
lean_object* v_cfg_3870_ = stack[1].m_obj;
lean_object* v_res_3912_;
v_res_3912_ = l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1(v_val_3869_, v_cfg_3870_);
stack->m_obj
 = v_res_3912_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1___boxed(lean_object* v_val_3913_, lean_object* v_cfg_3914_){
_start:
{
uint8_t v_val_143__boxed_3915_; lean_object* v_res_3916_; 
v_val_143__boxed_3915_ = lean_unbox(v_val_3913_);
v_res_3916_ = l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1(v_val_143__boxed_3915_, v_cfg_3914_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__2(lean_object* v_f_3917_, lean_object* v_cfg_3918_){
_start:
{
lean_object* v_toWorkspaceConfig_3919_; lean_object* v_toLeanConfig_3920_; uint8_t v_bootstrap_3921_; lean_object* v_extraDepTargets_3922_; uint8_t v_precompileModules_3923_; lean_object* v_moreGlobalServerArgs_3924_; lean_object* v_srcDir_3925_; lean_object* v_buildDir_3926_; lean_object* v_leanLibDir_3927_; lean_object* v_nativeLibDir_3928_; lean_object* v_binDir_3929_; lean_object* v_irDir_3930_; lean_object* v_releaseRepo_3931_; lean_object* v_buildArchive_3932_; uint8_t v_preferReleaseBuild_3933_; lean_object* v_testDriver_3934_; lean_object* v_testDriverArgs_3935_; lean_object* v_lintDriver_3936_; lean_object* v_lintDriverArgs_3937_; lean_object* v_version_3938_; lean_object* v_versionTags_3939_; lean_object* v_description_3940_; lean_object* v_keywords_3941_; lean_object* v_homepage_3942_; lean_object* v_license_3943_; lean_object* v_licenseFiles_3944_; lean_object* v_readmeFile_3945_; uint8_t v_reservoir_3946_; lean_object* v_enableArtifactCache_x3f_3947_; lean_object* v_restoreAllArtifacts_x3f_3948_; uint8_t v_libPrefixOnWindows_3949_; uint8_t v_allowImportAll_3950_; lean_object* v_builtinLint_x3f_3951_; lean_object* v_checks_3952_; uint8_t v_fixedToolchain_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3963_; 
v_toWorkspaceConfig_3919_ = lean_ctor_get(v_cfg_3918_, 0);
v_toLeanConfig_3920_ = lean_ctor_get(v_cfg_3918_, 1);
v_bootstrap_3921_ = lean_ctor_get_uint8(v_cfg_3918_, sizeof(void*)*28);
v_extraDepTargets_3922_ = lean_ctor_get(v_cfg_3918_, 2);
v_precompileModules_3923_ = lean_ctor_get_uint8(v_cfg_3918_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3924_ = lean_ctor_get(v_cfg_3918_, 3);
v_srcDir_3925_ = lean_ctor_get(v_cfg_3918_, 4);
v_buildDir_3926_ = lean_ctor_get(v_cfg_3918_, 5);
v_leanLibDir_3927_ = lean_ctor_get(v_cfg_3918_, 6);
v_nativeLibDir_3928_ = lean_ctor_get(v_cfg_3918_, 7);
v_binDir_3929_ = lean_ctor_get(v_cfg_3918_, 8);
v_irDir_3930_ = lean_ctor_get(v_cfg_3918_, 9);
v_releaseRepo_3931_ = lean_ctor_get(v_cfg_3918_, 10);
v_buildArchive_3932_ = lean_ctor_get(v_cfg_3918_, 11);
v_preferReleaseBuild_3933_ = lean_ctor_get_uint8(v_cfg_3918_, sizeof(void*)*28 + 2);
v_testDriver_3934_ = lean_ctor_get(v_cfg_3918_, 12);
v_testDriverArgs_3935_ = lean_ctor_get(v_cfg_3918_, 13);
v_lintDriver_3936_ = lean_ctor_get(v_cfg_3918_, 14);
v_lintDriverArgs_3937_ = lean_ctor_get(v_cfg_3918_, 15);
v_version_3938_ = lean_ctor_get(v_cfg_3918_, 16);
v_versionTags_3939_ = lean_ctor_get(v_cfg_3918_, 17);
v_description_3940_ = lean_ctor_get(v_cfg_3918_, 18);
v_keywords_3941_ = lean_ctor_get(v_cfg_3918_, 19);
v_homepage_3942_ = lean_ctor_get(v_cfg_3918_, 20);
v_license_3943_ = lean_ctor_get(v_cfg_3918_, 21);
v_licenseFiles_3944_ = lean_ctor_get(v_cfg_3918_, 22);
v_readmeFile_3945_ = lean_ctor_get(v_cfg_3918_, 23);
v_reservoir_3946_ = lean_ctor_get_uint8(v_cfg_3918_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3947_ = lean_ctor_get(v_cfg_3918_, 24);
v_restoreAllArtifacts_x3f_3948_ = lean_ctor_get(v_cfg_3918_, 25);
v_libPrefixOnWindows_3949_ = lean_ctor_get_uint8(v_cfg_3918_, sizeof(void*)*28 + 4);
v_allowImportAll_3950_ = lean_ctor_get_uint8(v_cfg_3918_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3951_ = lean_ctor_get(v_cfg_3918_, 26);
v_checks_3952_ = lean_ctor_get(v_cfg_3918_, 27);
v_fixedToolchain_3953_ = lean_ctor_get_uint8(v_cfg_3918_, sizeof(void*)*28 + 6);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_cfg_3918_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3955_ = v_cfg_3918_;
v_isShared_3956_ = v_isSharedCheck_3963_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_checks_3952_);
lean_inc(v_builtinLint_x3f_3951_);
lean_inc(v_restoreAllArtifacts_x3f_3948_);
lean_inc(v_enableArtifactCache_x3f_3947_);
lean_inc(v_readmeFile_3945_);
lean_inc(v_licenseFiles_3944_);
lean_inc(v_license_3943_);
lean_inc(v_homepage_3942_);
lean_inc(v_keywords_3941_);
lean_inc(v_description_3940_);
lean_inc(v_versionTags_3939_);
lean_inc(v_version_3938_);
lean_inc(v_lintDriverArgs_3937_);
lean_inc(v_lintDriver_3936_);
lean_inc(v_testDriverArgs_3935_);
lean_inc(v_testDriver_3934_);
lean_inc(v_buildArchive_3932_);
lean_inc(v_releaseRepo_3931_);
lean_inc(v_irDir_3930_);
lean_inc(v_binDir_3929_);
lean_inc(v_nativeLibDir_3928_);
lean_inc(v_leanLibDir_3927_);
lean_inc(v_buildDir_3926_);
lean_inc(v_srcDir_3925_);
lean_inc(v_moreGlobalServerArgs_3924_);
lean_inc(v_extraDepTargets_3922_);
lean_inc(v_toLeanConfig_3920_);
lean_inc(v_toWorkspaceConfig_3919_);
lean_dec(v_cfg_3918_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3963_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3957_ = lean_box(v_allowImportAll_3950_);
v___x_3958_ = lean_apply_1(v_f_3917_, v___x_3957_);
if (v_isShared_3956_ == 0)
{
v___x_3960_ = v___x_3955_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_toWorkspaceConfig_3919_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_toLeanConfig_3920_);
lean_ctor_set(v_reuseFailAlloc_3962_, 2, v_extraDepTargets_3922_);
lean_ctor_set(v_reuseFailAlloc_3962_, 3, v_moreGlobalServerArgs_3924_);
lean_ctor_set(v_reuseFailAlloc_3962_, 4, v_srcDir_3925_);
lean_ctor_set(v_reuseFailAlloc_3962_, 5, v_buildDir_3926_);
lean_ctor_set(v_reuseFailAlloc_3962_, 6, v_leanLibDir_3927_);
lean_ctor_set(v_reuseFailAlloc_3962_, 7, v_nativeLibDir_3928_);
lean_ctor_set(v_reuseFailAlloc_3962_, 8, v_binDir_3929_);
lean_ctor_set(v_reuseFailAlloc_3962_, 9, v_irDir_3930_);
lean_ctor_set(v_reuseFailAlloc_3962_, 10, v_releaseRepo_3931_);
lean_ctor_set(v_reuseFailAlloc_3962_, 11, v_buildArchive_3932_);
lean_ctor_set(v_reuseFailAlloc_3962_, 12, v_testDriver_3934_);
lean_ctor_set(v_reuseFailAlloc_3962_, 13, v_testDriverArgs_3935_);
lean_ctor_set(v_reuseFailAlloc_3962_, 14, v_lintDriver_3936_);
lean_ctor_set(v_reuseFailAlloc_3962_, 15, v_lintDriverArgs_3937_);
lean_ctor_set(v_reuseFailAlloc_3962_, 16, v_version_3938_);
lean_ctor_set(v_reuseFailAlloc_3962_, 17, v_versionTags_3939_);
lean_ctor_set(v_reuseFailAlloc_3962_, 18, v_description_3940_);
lean_ctor_set(v_reuseFailAlloc_3962_, 19, v_keywords_3941_);
lean_ctor_set(v_reuseFailAlloc_3962_, 20, v_homepage_3942_);
lean_ctor_set(v_reuseFailAlloc_3962_, 21, v_license_3943_);
lean_ctor_set(v_reuseFailAlloc_3962_, 22, v_licenseFiles_3944_);
lean_ctor_set(v_reuseFailAlloc_3962_, 23, v_readmeFile_3945_);
lean_ctor_set(v_reuseFailAlloc_3962_, 24, v_enableArtifactCache_x3f_3947_);
lean_ctor_set(v_reuseFailAlloc_3962_, 25, v_restoreAllArtifacts_x3f_3948_);
lean_ctor_set(v_reuseFailAlloc_3962_, 26, v_builtinLint_x3f_3951_);
lean_ctor_set(v_reuseFailAlloc_3962_, 27, v_checks_3952_);
lean_ctor_set_uint8(v_reuseFailAlloc_3962_, sizeof(void*)*28, v_bootstrap_3921_);
lean_ctor_set_uint8(v_reuseFailAlloc_3962_, sizeof(void*)*28 + 1, v_precompileModules_3923_);
lean_ctor_set_uint8(v_reuseFailAlloc_3962_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3933_);
lean_ctor_set_uint8(v_reuseFailAlloc_3962_, sizeof(void*)*28 + 3, v_reservoir_3946_);
lean_ctor_set_uint8(v_reuseFailAlloc_3962_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3949_);
v___x_3960_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
uint8_t v___x_3961_; 
v___x_3961_ = lean_unbox(v___x_3958_);
lean_ctor_set_uint8(v___x_3960_, sizeof(void*)*28 + 5, v___x_3961_);
lean_ctor_set_uint8(v___x_3960_, sizeof(void*)*28 + 6, v_fixedToolchain_3953_);
return v___x_3960_;
}
}
}
}
lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg(){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = ((lean_object*)(l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__3));
return v___x_3973_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_allowImportAll___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3974_;
v_res_3974_ = l_Lake_PackageConfig_allowImportAll___proj___redArg();
stack->m_obj
 = v_res_3974_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___boxed(lean_object* v___dummy_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lake_PackageConfig_allowImportAll___proj___redArg();
return v_res_3976_;
}
}
static lean_object* _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0(void){
_start:
{
lean_object* v___x_3977_; 
v___x_3977_ = l_Lake_PackageConfig_allowImportAll___proj___redArg();
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object* v_p_3978_, lean_object* v_n_3979_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_obj_once(&l_Lake_PackageConfig_allowImportAll___proj___closed__0, &l_Lake_PackageConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object* v_p_3981_, lean_object* v_n_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3981_, v_n_3982_);
lean_dec(v_n_3982_);
lean_dec(v_p_3981_);
return v_res_3983_;
}
}
lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___redArg(){
_start:
{
lean_object* v___x_3985_; 
v___x_3985_ = lean_obj_once(&l_Lake_PackageConfig_allowImportAll___proj___closed__0, &l_Lake_PackageConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0);
return v___x_3985_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_allowImportAll_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3986_;
v_res_3986_ = l_Lake_PackageConfig_allowImportAll_instConfigField___redArg();
stack->m_obj
 = v_res_3986_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___redArg___boxed(lean_object* v___dummy_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lake_PackageConfig_allowImportAll_instConfigField___redArg();
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object* v_p_3989_, lean_object* v_n_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = lean_obj_once(&l_Lake_PackageConfig_allowImportAll___proj___closed__0, &l_Lake_PackageConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object* v_p_3992_, lean_object* v_n_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lake_PackageConfig_allowImportAll_instConfigField(v_p_3992_, v_n_3993_);
lean_dec(v_n_3993_);
lean_dec(v_p_3992_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0(lean_object* v_cfg_3995_){
_start:
{
lean_object* v_builtinLint_x3f_3996_; 
v_builtinLint_x3f_3996_ = lean_ctor_get(v_cfg_3995_, 26);
lean_inc(v_builtinLint_x3f_3996_);
return v_builtinLint_x3f_3996_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0___boxed(lean_object* v_cfg_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0(v_cfg_3997_);
lean_dec_ref(v_cfg_3997_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__1(lean_object* v_val_3999_, lean_object* v_cfg_4000_){
_start:
{
lean_object* v_toWorkspaceConfig_4001_; lean_object* v_toLeanConfig_4002_; uint8_t v_bootstrap_4003_; lean_object* v_extraDepTargets_4004_; uint8_t v_precompileModules_4005_; lean_object* v_moreGlobalServerArgs_4006_; lean_object* v_srcDir_4007_; lean_object* v_buildDir_4008_; lean_object* v_leanLibDir_4009_; lean_object* v_nativeLibDir_4010_; lean_object* v_binDir_4011_; lean_object* v_irDir_4012_; lean_object* v_releaseRepo_4013_; lean_object* v_buildArchive_4014_; uint8_t v_preferReleaseBuild_4015_; lean_object* v_testDriver_4016_; lean_object* v_testDriverArgs_4017_; lean_object* v_lintDriver_4018_; lean_object* v_lintDriverArgs_4019_; lean_object* v_version_4020_; lean_object* v_versionTags_4021_; lean_object* v_description_4022_; lean_object* v_keywords_4023_; lean_object* v_homepage_4024_; lean_object* v_license_4025_; lean_object* v_licenseFiles_4026_; lean_object* v_readmeFile_4027_; uint8_t v_reservoir_4028_; lean_object* v_enableArtifactCache_x3f_4029_; lean_object* v_restoreAllArtifacts_x3f_4030_; uint8_t v_libPrefixOnWindows_4031_; uint8_t v_allowImportAll_4032_; lean_object* v_checks_4033_; uint8_t v_fixedToolchain_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
v_toWorkspaceConfig_4001_ = lean_ctor_get(v_cfg_4000_, 0);
v_toLeanConfig_4002_ = lean_ctor_get(v_cfg_4000_, 1);
v_bootstrap_4003_ = lean_ctor_get_uint8(v_cfg_4000_, sizeof(void*)*28);
v_extraDepTargets_4004_ = lean_ctor_get(v_cfg_4000_, 2);
v_precompileModules_4005_ = lean_ctor_get_uint8(v_cfg_4000_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4006_ = lean_ctor_get(v_cfg_4000_, 3);
v_srcDir_4007_ = lean_ctor_get(v_cfg_4000_, 4);
v_buildDir_4008_ = lean_ctor_get(v_cfg_4000_, 5);
v_leanLibDir_4009_ = lean_ctor_get(v_cfg_4000_, 6);
v_nativeLibDir_4010_ = lean_ctor_get(v_cfg_4000_, 7);
v_binDir_4011_ = lean_ctor_get(v_cfg_4000_, 8);
v_irDir_4012_ = lean_ctor_get(v_cfg_4000_, 9);
v_releaseRepo_4013_ = lean_ctor_get(v_cfg_4000_, 10);
v_buildArchive_4014_ = lean_ctor_get(v_cfg_4000_, 11);
v_preferReleaseBuild_4015_ = lean_ctor_get_uint8(v_cfg_4000_, sizeof(void*)*28 + 2);
v_testDriver_4016_ = lean_ctor_get(v_cfg_4000_, 12);
v_testDriverArgs_4017_ = lean_ctor_get(v_cfg_4000_, 13);
v_lintDriver_4018_ = lean_ctor_get(v_cfg_4000_, 14);
v_lintDriverArgs_4019_ = lean_ctor_get(v_cfg_4000_, 15);
v_version_4020_ = lean_ctor_get(v_cfg_4000_, 16);
v_versionTags_4021_ = lean_ctor_get(v_cfg_4000_, 17);
v_description_4022_ = lean_ctor_get(v_cfg_4000_, 18);
v_keywords_4023_ = lean_ctor_get(v_cfg_4000_, 19);
v_homepage_4024_ = lean_ctor_get(v_cfg_4000_, 20);
v_license_4025_ = lean_ctor_get(v_cfg_4000_, 21);
v_licenseFiles_4026_ = lean_ctor_get(v_cfg_4000_, 22);
v_readmeFile_4027_ = lean_ctor_get(v_cfg_4000_, 23);
v_reservoir_4028_ = lean_ctor_get_uint8(v_cfg_4000_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4029_ = lean_ctor_get(v_cfg_4000_, 24);
v_restoreAllArtifacts_x3f_4030_ = lean_ctor_get(v_cfg_4000_, 25);
v_libPrefixOnWindows_4031_ = lean_ctor_get_uint8(v_cfg_4000_, sizeof(void*)*28 + 4);
v_allowImportAll_4032_ = lean_ctor_get_uint8(v_cfg_4000_, sizeof(void*)*28 + 5);
v_checks_4033_ = lean_ctor_get(v_cfg_4000_, 27);
v_fixedToolchain_4034_ = lean_ctor_get_uint8(v_cfg_4000_, sizeof(void*)*28 + 6);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_cfg_4000_);
if (v_isSharedCheck_4041_ == 0)
{
lean_object* v_unused_4042_; 
v_unused_4042_ = lean_ctor_get(v_cfg_4000_, 26);
lean_dec(v_unused_4042_);
v___x_4036_ = v_cfg_4000_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_checks_4033_);
lean_inc(v_restoreAllArtifacts_x3f_4030_);
lean_inc(v_enableArtifactCache_x3f_4029_);
lean_inc(v_readmeFile_4027_);
lean_inc(v_licenseFiles_4026_);
lean_inc(v_license_4025_);
lean_inc(v_homepage_4024_);
lean_inc(v_keywords_4023_);
lean_inc(v_description_4022_);
lean_inc(v_versionTags_4021_);
lean_inc(v_version_4020_);
lean_inc(v_lintDriverArgs_4019_);
lean_inc(v_lintDriver_4018_);
lean_inc(v_testDriverArgs_4017_);
lean_inc(v_testDriver_4016_);
lean_inc(v_buildArchive_4014_);
lean_inc(v_releaseRepo_4013_);
lean_inc(v_irDir_4012_);
lean_inc(v_binDir_4011_);
lean_inc(v_nativeLibDir_4010_);
lean_inc(v_leanLibDir_4009_);
lean_inc(v_buildDir_4008_);
lean_inc(v_srcDir_4007_);
lean_inc(v_moreGlobalServerArgs_4006_);
lean_inc(v_extraDepTargets_4004_);
lean_inc(v_toLeanConfig_4002_);
lean_inc(v_toWorkspaceConfig_4001_);
lean_dec(v_cfg_4000_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 26, v_val_3999_);
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_toWorkspaceConfig_4001_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_toLeanConfig_4002_);
lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_extraDepTargets_4004_);
lean_ctor_set(v_reuseFailAlloc_4040_, 3, v_moreGlobalServerArgs_4006_);
lean_ctor_set(v_reuseFailAlloc_4040_, 4, v_srcDir_4007_);
lean_ctor_set(v_reuseFailAlloc_4040_, 5, v_buildDir_4008_);
lean_ctor_set(v_reuseFailAlloc_4040_, 6, v_leanLibDir_4009_);
lean_ctor_set(v_reuseFailAlloc_4040_, 7, v_nativeLibDir_4010_);
lean_ctor_set(v_reuseFailAlloc_4040_, 8, v_binDir_4011_);
lean_ctor_set(v_reuseFailAlloc_4040_, 9, v_irDir_4012_);
lean_ctor_set(v_reuseFailAlloc_4040_, 10, v_releaseRepo_4013_);
lean_ctor_set(v_reuseFailAlloc_4040_, 11, v_buildArchive_4014_);
lean_ctor_set(v_reuseFailAlloc_4040_, 12, v_testDriver_4016_);
lean_ctor_set(v_reuseFailAlloc_4040_, 13, v_testDriverArgs_4017_);
lean_ctor_set(v_reuseFailAlloc_4040_, 14, v_lintDriver_4018_);
lean_ctor_set(v_reuseFailAlloc_4040_, 15, v_lintDriverArgs_4019_);
lean_ctor_set(v_reuseFailAlloc_4040_, 16, v_version_4020_);
lean_ctor_set(v_reuseFailAlloc_4040_, 17, v_versionTags_4021_);
lean_ctor_set(v_reuseFailAlloc_4040_, 18, v_description_4022_);
lean_ctor_set(v_reuseFailAlloc_4040_, 19, v_keywords_4023_);
lean_ctor_set(v_reuseFailAlloc_4040_, 20, v_homepage_4024_);
lean_ctor_set(v_reuseFailAlloc_4040_, 21, v_license_4025_);
lean_ctor_set(v_reuseFailAlloc_4040_, 22, v_licenseFiles_4026_);
lean_ctor_set(v_reuseFailAlloc_4040_, 23, v_readmeFile_4027_);
lean_ctor_set(v_reuseFailAlloc_4040_, 24, v_enableArtifactCache_x3f_4029_);
lean_ctor_set(v_reuseFailAlloc_4040_, 25, v_restoreAllArtifacts_x3f_4030_);
lean_ctor_set(v_reuseFailAlloc_4040_, 26, v_val_3999_);
lean_ctor_set(v_reuseFailAlloc_4040_, 27, v_checks_4033_);
lean_ctor_set_uint8(v_reuseFailAlloc_4040_, sizeof(void*)*28, v_bootstrap_4003_);
lean_ctor_set_uint8(v_reuseFailAlloc_4040_, sizeof(void*)*28 + 1, v_precompileModules_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4040_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4015_);
lean_ctor_set_uint8(v_reuseFailAlloc_4040_, sizeof(void*)*28 + 3, v_reservoir_4028_);
lean_ctor_set_uint8(v_reuseFailAlloc_4040_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4031_);
lean_ctor_set_uint8(v_reuseFailAlloc_4040_, sizeof(void*)*28 + 5, v_allowImportAll_4032_);
lean_ctor_set_uint8(v_reuseFailAlloc_4040_, sizeof(void*)*28 + 6, v_fixedToolchain_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__2(lean_object* v_f_4043_, lean_object* v_cfg_4044_){
_start:
{
lean_object* v_toWorkspaceConfig_4045_; lean_object* v_toLeanConfig_4046_; uint8_t v_bootstrap_4047_; lean_object* v_extraDepTargets_4048_; uint8_t v_precompileModules_4049_; lean_object* v_moreGlobalServerArgs_4050_; lean_object* v_srcDir_4051_; lean_object* v_buildDir_4052_; lean_object* v_leanLibDir_4053_; lean_object* v_nativeLibDir_4054_; lean_object* v_binDir_4055_; lean_object* v_irDir_4056_; lean_object* v_releaseRepo_4057_; lean_object* v_buildArchive_4058_; uint8_t v_preferReleaseBuild_4059_; lean_object* v_testDriver_4060_; lean_object* v_testDriverArgs_4061_; lean_object* v_lintDriver_4062_; lean_object* v_lintDriverArgs_4063_; lean_object* v_version_4064_; lean_object* v_versionTags_4065_; lean_object* v_description_4066_; lean_object* v_keywords_4067_; lean_object* v_homepage_4068_; lean_object* v_license_4069_; lean_object* v_licenseFiles_4070_; lean_object* v_readmeFile_4071_; uint8_t v_reservoir_4072_; lean_object* v_enableArtifactCache_x3f_4073_; lean_object* v_restoreAllArtifacts_x3f_4074_; uint8_t v_libPrefixOnWindows_4075_; uint8_t v_allowImportAll_4076_; lean_object* v_builtinLint_x3f_4077_; lean_object* v_checks_4078_; uint8_t v_fixedToolchain_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4087_; 
v_toWorkspaceConfig_4045_ = lean_ctor_get(v_cfg_4044_, 0);
v_toLeanConfig_4046_ = lean_ctor_get(v_cfg_4044_, 1);
v_bootstrap_4047_ = lean_ctor_get_uint8(v_cfg_4044_, sizeof(void*)*28);
v_extraDepTargets_4048_ = lean_ctor_get(v_cfg_4044_, 2);
v_precompileModules_4049_ = lean_ctor_get_uint8(v_cfg_4044_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4050_ = lean_ctor_get(v_cfg_4044_, 3);
v_srcDir_4051_ = lean_ctor_get(v_cfg_4044_, 4);
v_buildDir_4052_ = lean_ctor_get(v_cfg_4044_, 5);
v_leanLibDir_4053_ = lean_ctor_get(v_cfg_4044_, 6);
v_nativeLibDir_4054_ = lean_ctor_get(v_cfg_4044_, 7);
v_binDir_4055_ = lean_ctor_get(v_cfg_4044_, 8);
v_irDir_4056_ = lean_ctor_get(v_cfg_4044_, 9);
v_releaseRepo_4057_ = lean_ctor_get(v_cfg_4044_, 10);
v_buildArchive_4058_ = lean_ctor_get(v_cfg_4044_, 11);
v_preferReleaseBuild_4059_ = lean_ctor_get_uint8(v_cfg_4044_, sizeof(void*)*28 + 2);
v_testDriver_4060_ = lean_ctor_get(v_cfg_4044_, 12);
v_testDriverArgs_4061_ = lean_ctor_get(v_cfg_4044_, 13);
v_lintDriver_4062_ = lean_ctor_get(v_cfg_4044_, 14);
v_lintDriverArgs_4063_ = lean_ctor_get(v_cfg_4044_, 15);
v_version_4064_ = lean_ctor_get(v_cfg_4044_, 16);
v_versionTags_4065_ = lean_ctor_get(v_cfg_4044_, 17);
v_description_4066_ = lean_ctor_get(v_cfg_4044_, 18);
v_keywords_4067_ = lean_ctor_get(v_cfg_4044_, 19);
v_homepage_4068_ = lean_ctor_get(v_cfg_4044_, 20);
v_license_4069_ = lean_ctor_get(v_cfg_4044_, 21);
v_licenseFiles_4070_ = lean_ctor_get(v_cfg_4044_, 22);
v_readmeFile_4071_ = lean_ctor_get(v_cfg_4044_, 23);
v_reservoir_4072_ = lean_ctor_get_uint8(v_cfg_4044_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4073_ = lean_ctor_get(v_cfg_4044_, 24);
v_restoreAllArtifacts_x3f_4074_ = lean_ctor_get(v_cfg_4044_, 25);
v_libPrefixOnWindows_4075_ = lean_ctor_get_uint8(v_cfg_4044_, sizeof(void*)*28 + 4);
v_allowImportAll_4076_ = lean_ctor_get_uint8(v_cfg_4044_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4077_ = lean_ctor_get(v_cfg_4044_, 26);
v_checks_4078_ = lean_ctor_get(v_cfg_4044_, 27);
v_fixedToolchain_4079_ = lean_ctor_get_uint8(v_cfg_4044_, sizeof(void*)*28 + 6);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_cfg_4044_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4081_ = v_cfg_4044_;
v_isShared_4082_ = v_isSharedCheck_4087_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_checks_4078_);
lean_inc(v_builtinLint_x3f_4077_);
lean_inc(v_restoreAllArtifacts_x3f_4074_);
lean_inc(v_enableArtifactCache_x3f_4073_);
lean_inc(v_readmeFile_4071_);
lean_inc(v_licenseFiles_4070_);
lean_inc(v_license_4069_);
lean_inc(v_homepage_4068_);
lean_inc(v_keywords_4067_);
lean_inc(v_description_4066_);
lean_inc(v_versionTags_4065_);
lean_inc(v_version_4064_);
lean_inc(v_lintDriverArgs_4063_);
lean_inc(v_lintDriver_4062_);
lean_inc(v_testDriverArgs_4061_);
lean_inc(v_testDriver_4060_);
lean_inc(v_buildArchive_4058_);
lean_inc(v_releaseRepo_4057_);
lean_inc(v_irDir_4056_);
lean_inc(v_binDir_4055_);
lean_inc(v_nativeLibDir_4054_);
lean_inc(v_leanLibDir_4053_);
lean_inc(v_buildDir_4052_);
lean_inc(v_srcDir_4051_);
lean_inc(v_moreGlobalServerArgs_4050_);
lean_inc(v_extraDepTargets_4048_);
lean_inc(v_toLeanConfig_4046_);
lean_inc(v_toWorkspaceConfig_4045_);
lean_dec(v_cfg_4044_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4087_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v___x_4085_; 
v___x_4083_ = lean_apply_1(v_f_4043_, v_builtinLint_x3f_4077_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 26, v___x_4083_);
v___x_4085_ = v___x_4081_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_toWorkspaceConfig_4045_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_toLeanConfig_4046_);
lean_ctor_set(v_reuseFailAlloc_4086_, 2, v_extraDepTargets_4048_);
lean_ctor_set(v_reuseFailAlloc_4086_, 3, v_moreGlobalServerArgs_4050_);
lean_ctor_set(v_reuseFailAlloc_4086_, 4, v_srcDir_4051_);
lean_ctor_set(v_reuseFailAlloc_4086_, 5, v_buildDir_4052_);
lean_ctor_set(v_reuseFailAlloc_4086_, 6, v_leanLibDir_4053_);
lean_ctor_set(v_reuseFailAlloc_4086_, 7, v_nativeLibDir_4054_);
lean_ctor_set(v_reuseFailAlloc_4086_, 8, v_binDir_4055_);
lean_ctor_set(v_reuseFailAlloc_4086_, 9, v_irDir_4056_);
lean_ctor_set(v_reuseFailAlloc_4086_, 10, v_releaseRepo_4057_);
lean_ctor_set(v_reuseFailAlloc_4086_, 11, v_buildArchive_4058_);
lean_ctor_set(v_reuseFailAlloc_4086_, 12, v_testDriver_4060_);
lean_ctor_set(v_reuseFailAlloc_4086_, 13, v_testDriverArgs_4061_);
lean_ctor_set(v_reuseFailAlloc_4086_, 14, v_lintDriver_4062_);
lean_ctor_set(v_reuseFailAlloc_4086_, 15, v_lintDriverArgs_4063_);
lean_ctor_set(v_reuseFailAlloc_4086_, 16, v_version_4064_);
lean_ctor_set(v_reuseFailAlloc_4086_, 17, v_versionTags_4065_);
lean_ctor_set(v_reuseFailAlloc_4086_, 18, v_description_4066_);
lean_ctor_set(v_reuseFailAlloc_4086_, 19, v_keywords_4067_);
lean_ctor_set(v_reuseFailAlloc_4086_, 20, v_homepage_4068_);
lean_ctor_set(v_reuseFailAlloc_4086_, 21, v_license_4069_);
lean_ctor_set(v_reuseFailAlloc_4086_, 22, v_licenseFiles_4070_);
lean_ctor_set(v_reuseFailAlloc_4086_, 23, v_readmeFile_4071_);
lean_ctor_set(v_reuseFailAlloc_4086_, 24, v_enableArtifactCache_x3f_4073_);
lean_ctor_set(v_reuseFailAlloc_4086_, 25, v_restoreAllArtifacts_x3f_4074_);
lean_ctor_set(v_reuseFailAlloc_4086_, 26, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4086_, 27, v_checks_4078_);
lean_ctor_set_uint8(v_reuseFailAlloc_4086_, sizeof(void*)*28, v_bootstrap_4047_);
lean_ctor_set_uint8(v_reuseFailAlloc_4086_, sizeof(void*)*28 + 1, v_precompileModules_4049_);
lean_ctor_set_uint8(v_reuseFailAlloc_4086_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4059_);
lean_ctor_set_uint8(v_reuseFailAlloc_4086_, sizeof(void*)*28 + 3, v_reservoir_4072_);
lean_ctor_set_uint8(v_reuseFailAlloc_4086_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4075_);
lean_ctor_set_uint8(v_reuseFailAlloc_4086_, sizeof(void*)*28 + 5, v_allowImportAll_4076_);
lean_ctor_set_uint8(v_reuseFailAlloc_4086_, sizeof(void*)*28 + 6, v_fixedToolchain_4079_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
}
lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg(){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = ((lean_object*)(l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__3));
return v___x_4097_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_builtinLint_x3f___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4098_;
v_res_4098_ = l_Lake_PackageConfig_builtinLint_x3f___proj___redArg();
stack->m_obj
 = v_res_4098_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___boxed(lean_object* v___dummy_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Lake_PackageConfig_builtinLint_x3f___proj___redArg();
return v_res_4100_;
}
}
static lean_object* _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0(void){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l_Lake_PackageConfig_builtinLint_x3f___proj___redArg();
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj(lean_object* v_p_4102_, lean_object* v_n_4103_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___boxed(lean_object* v_p_4105_, lean_object* v_n_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_Lake_PackageConfig_builtinLint_x3f___proj(v_p_4105_, v_n_4106_);
lean_dec(v_n_4106_);
lean_dec(v_p_4105_);
return v_res_4107_;
}
}
lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4109_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4110_;
v_res_4110_ = l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg();
stack->m_obj
 = v_res_4110_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg();
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField(lean_object* v_p_4113_, lean_object* v_n_4114_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___boxed(lean_object* v_p_4116_, lean_object* v_n_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l_Lake_PackageConfig_builtinLint_x3f_instConfigField(v_p_4116_, v_n_4117_);
lean_dec(v_n_4117_);
lean_dec(v_p_4116_);
return v_res_4118_;
}
}
lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___redArg(){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4120_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_builtinLint_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4121_;
v_res_4121_ = l_Lake_PackageConfig_builtinLint_instConfigField___redArg();
stack->m_obj
 = v_res_4121_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___redArg___boxed(lean_object* v___dummy_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_Lake_PackageConfig_builtinLint_instConfigField___redArg();
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField(lean_object* v_p_4124_, lean_object* v_n_4125_){
_start:
{
lean_object* v___x_4126_; 
v___x_4126_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___boxed(lean_object* v_p_4127_, lean_object* v_n_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_Lake_PackageConfig_builtinLint_instConfigField(v_p_4127_, v_n_4128_);
lean_dec(v_n_4128_);
lean_dec(v_p_4127_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__0(lean_object* v_cfg_4130_){
_start:
{
lean_object* v_checks_4131_; 
v_checks_4131_ = lean_ctor_get(v_cfg_4130_, 27);
lean_inc_ref(v_checks_4131_);
return v_checks_4131_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__0___boxed(lean_object* v_cfg_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Lake_PackageConfig_checks___proj___redArg___lam__0(v_cfg_4132_);
lean_dec_ref(v_cfg_4132_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__1(lean_object* v_val_4134_, lean_object* v_cfg_4135_){
_start:
{
lean_object* v_toWorkspaceConfig_4136_; lean_object* v_toLeanConfig_4137_; uint8_t v_bootstrap_4138_; lean_object* v_extraDepTargets_4139_; uint8_t v_precompileModules_4140_; lean_object* v_moreGlobalServerArgs_4141_; lean_object* v_srcDir_4142_; lean_object* v_buildDir_4143_; lean_object* v_leanLibDir_4144_; lean_object* v_nativeLibDir_4145_; lean_object* v_binDir_4146_; lean_object* v_irDir_4147_; lean_object* v_releaseRepo_4148_; lean_object* v_buildArchive_4149_; uint8_t v_preferReleaseBuild_4150_; lean_object* v_testDriver_4151_; lean_object* v_testDriverArgs_4152_; lean_object* v_lintDriver_4153_; lean_object* v_lintDriverArgs_4154_; lean_object* v_version_4155_; lean_object* v_versionTags_4156_; lean_object* v_description_4157_; lean_object* v_keywords_4158_; lean_object* v_homepage_4159_; lean_object* v_license_4160_; lean_object* v_licenseFiles_4161_; lean_object* v_readmeFile_4162_; uint8_t v_reservoir_4163_; lean_object* v_enableArtifactCache_x3f_4164_; lean_object* v_restoreAllArtifacts_x3f_4165_; uint8_t v_libPrefixOnWindows_4166_; uint8_t v_allowImportAll_4167_; lean_object* v_builtinLint_x3f_4168_; uint8_t v_fixedToolchain_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
v_toWorkspaceConfig_4136_ = lean_ctor_get(v_cfg_4135_, 0);
v_toLeanConfig_4137_ = lean_ctor_get(v_cfg_4135_, 1);
v_bootstrap_4138_ = lean_ctor_get_uint8(v_cfg_4135_, sizeof(void*)*28);
v_extraDepTargets_4139_ = lean_ctor_get(v_cfg_4135_, 2);
v_precompileModules_4140_ = lean_ctor_get_uint8(v_cfg_4135_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4141_ = lean_ctor_get(v_cfg_4135_, 3);
v_srcDir_4142_ = lean_ctor_get(v_cfg_4135_, 4);
v_buildDir_4143_ = lean_ctor_get(v_cfg_4135_, 5);
v_leanLibDir_4144_ = lean_ctor_get(v_cfg_4135_, 6);
v_nativeLibDir_4145_ = lean_ctor_get(v_cfg_4135_, 7);
v_binDir_4146_ = lean_ctor_get(v_cfg_4135_, 8);
v_irDir_4147_ = lean_ctor_get(v_cfg_4135_, 9);
v_releaseRepo_4148_ = lean_ctor_get(v_cfg_4135_, 10);
v_buildArchive_4149_ = lean_ctor_get(v_cfg_4135_, 11);
v_preferReleaseBuild_4150_ = lean_ctor_get_uint8(v_cfg_4135_, sizeof(void*)*28 + 2);
v_testDriver_4151_ = lean_ctor_get(v_cfg_4135_, 12);
v_testDriverArgs_4152_ = lean_ctor_get(v_cfg_4135_, 13);
v_lintDriver_4153_ = lean_ctor_get(v_cfg_4135_, 14);
v_lintDriverArgs_4154_ = lean_ctor_get(v_cfg_4135_, 15);
v_version_4155_ = lean_ctor_get(v_cfg_4135_, 16);
v_versionTags_4156_ = lean_ctor_get(v_cfg_4135_, 17);
v_description_4157_ = lean_ctor_get(v_cfg_4135_, 18);
v_keywords_4158_ = lean_ctor_get(v_cfg_4135_, 19);
v_homepage_4159_ = lean_ctor_get(v_cfg_4135_, 20);
v_license_4160_ = lean_ctor_get(v_cfg_4135_, 21);
v_licenseFiles_4161_ = lean_ctor_get(v_cfg_4135_, 22);
v_readmeFile_4162_ = lean_ctor_get(v_cfg_4135_, 23);
v_reservoir_4163_ = lean_ctor_get_uint8(v_cfg_4135_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4164_ = lean_ctor_get(v_cfg_4135_, 24);
v_restoreAllArtifacts_x3f_4165_ = lean_ctor_get(v_cfg_4135_, 25);
v_libPrefixOnWindows_4166_ = lean_ctor_get_uint8(v_cfg_4135_, sizeof(void*)*28 + 4);
v_allowImportAll_4167_ = lean_ctor_get_uint8(v_cfg_4135_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4168_ = lean_ctor_get(v_cfg_4135_, 26);
v_fixedToolchain_4169_ = lean_ctor_get_uint8(v_cfg_4135_, sizeof(void*)*28 + 6);
v_isSharedCheck_4176_ = !lean_is_exclusive(v_cfg_4135_);
if (v_isSharedCheck_4176_ == 0)
{
lean_object* v_unused_4177_; 
v_unused_4177_ = lean_ctor_get(v_cfg_4135_, 27);
lean_dec(v_unused_4177_);
v___x_4171_ = v_cfg_4135_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_builtinLint_x3f_4168_);
lean_inc(v_restoreAllArtifacts_x3f_4165_);
lean_inc(v_enableArtifactCache_x3f_4164_);
lean_inc(v_readmeFile_4162_);
lean_inc(v_licenseFiles_4161_);
lean_inc(v_license_4160_);
lean_inc(v_homepage_4159_);
lean_inc(v_keywords_4158_);
lean_inc(v_description_4157_);
lean_inc(v_versionTags_4156_);
lean_inc(v_version_4155_);
lean_inc(v_lintDriverArgs_4154_);
lean_inc(v_lintDriver_4153_);
lean_inc(v_testDriverArgs_4152_);
lean_inc(v_testDriver_4151_);
lean_inc(v_buildArchive_4149_);
lean_inc(v_releaseRepo_4148_);
lean_inc(v_irDir_4147_);
lean_inc(v_binDir_4146_);
lean_inc(v_nativeLibDir_4145_);
lean_inc(v_leanLibDir_4144_);
lean_inc(v_buildDir_4143_);
lean_inc(v_srcDir_4142_);
lean_inc(v_moreGlobalServerArgs_4141_);
lean_inc(v_extraDepTargets_4139_);
lean_inc(v_toLeanConfig_4137_);
lean_inc(v_toWorkspaceConfig_4136_);
lean_dec(v_cfg_4135_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 27, v_val_4134_);
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_toWorkspaceConfig_4136_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v_toLeanConfig_4137_);
lean_ctor_set(v_reuseFailAlloc_4175_, 2, v_extraDepTargets_4139_);
lean_ctor_set(v_reuseFailAlloc_4175_, 3, v_moreGlobalServerArgs_4141_);
lean_ctor_set(v_reuseFailAlloc_4175_, 4, v_srcDir_4142_);
lean_ctor_set(v_reuseFailAlloc_4175_, 5, v_buildDir_4143_);
lean_ctor_set(v_reuseFailAlloc_4175_, 6, v_leanLibDir_4144_);
lean_ctor_set(v_reuseFailAlloc_4175_, 7, v_nativeLibDir_4145_);
lean_ctor_set(v_reuseFailAlloc_4175_, 8, v_binDir_4146_);
lean_ctor_set(v_reuseFailAlloc_4175_, 9, v_irDir_4147_);
lean_ctor_set(v_reuseFailAlloc_4175_, 10, v_releaseRepo_4148_);
lean_ctor_set(v_reuseFailAlloc_4175_, 11, v_buildArchive_4149_);
lean_ctor_set(v_reuseFailAlloc_4175_, 12, v_testDriver_4151_);
lean_ctor_set(v_reuseFailAlloc_4175_, 13, v_testDriverArgs_4152_);
lean_ctor_set(v_reuseFailAlloc_4175_, 14, v_lintDriver_4153_);
lean_ctor_set(v_reuseFailAlloc_4175_, 15, v_lintDriverArgs_4154_);
lean_ctor_set(v_reuseFailAlloc_4175_, 16, v_version_4155_);
lean_ctor_set(v_reuseFailAlloc_4175_, 17, v_versionTags_4156_);
lean_ctor_set(v_reuseFailAlloc_4175_, 18, v_description_4157_);
lean_ctor_set(v_reuseFailAlloc_4175_, 19, v_keywords_4158_);
lean_ctor_set(v_reuseFailAlloc_4175_, 20, v_homepage_4159_);
lean_ctor_set(v_reuseFailAlloc_4175_, 21, v_license_4160_);
lean_ctor_set(v_reuseFailAlloc_4175_, 22, v_licenseFiles_4161_);
lean_ctor_set(v_reuseFailAlloc_4175_, 23, v_readmeFile_4162_);
lean_ctor_set(v_reuseFailAlloc_4175_, 24, v_enableArtifactCache_x3f_4164_);
lean_ctor_set(v_reuseFailAlloc_4175_, 25, v_restoreAllArtifacts_x3f_4165_);
lean_ctor_set(v_reuseFailAlloc_4175_, 26, v_builtinLint_x3f_4168_);
lean_ctor_set(v_reuseFailAlloc_4175_, 27, v_val_4134_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, sizeof(void*)*28, v_bootstrap_4138_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, sizeof(void*)*28 + 1, v_precompileModules_4140_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4150_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, sizeof(void*)*28 + 3, v_reservoir_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4166_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, sizeof(void*)*28 + 5, v_allowImportAll_4167_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, sizeof(void*)*28 + 6, v_fixedToolchain_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__2(lean_object* v_f_4178_, lean_object* v_cfg_4179_){
_start:
{
lean_object* v_toWorkspaceConfig_4180_; lean_object* v_toLeanConfig_4181_; uint8_t v_bootstrap_4182_; lean_object* v_extraDepTargets_4183_; uint8_t v_precompileModules_4184_; lean_object* v_moreGlobalServerArgs_4185_; lean_object* v_srcDir_4186_; lean_object* v_buildDir_4187_; lean_object* v_leanLibDir_4188_; lean_object* v_nativeLibDir_4189_; lean_object* v_binDir_4190_; lean_object* v_irDir_4191_; lean_object* v_releaseRepo_4192_; lean_object* v_buildArchive_4193_; uint8_t v_preferReleaseBuild_4194_; lean_object* v_testDriver_4195_; lean_object* v_testDriverArgs_4196_; lean_object* v_lintDriver_4197_; lean_object* v_lintDriverArgs_4198_; lean_object* v_version_4199_; lean_object* v_versionTags_4200_; lean_object* v_description_4201_; lean_object* v_keywords_4202_; lean_object* v_homepage_4203_; lean_object* v_license_4204_; lean_object* v_licenseFiles_4205_; lean_object* v_readmeFile_4206_; uint8_t v_reservoir_4207_; lean_object* v_enableArtifactCache_x3f_4208_; lean_object* v_restoreAllArtifacts_x3f_4209_; uint8_t v_libPrefixOnWindows_4210_; uint8_t v_allowImportAll_4211_; lean_object* v_builtinLint_x3f_4212_; lean_object* v_checks_4213_; uint8_t v_fixedToolchain_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4222_; 
v_toWorkspaceConfig_4180_ = lean_ctor_get(v_cfg_4179_, 0);
v_toLeanConfig_4181_ = lean_ctor_get(v_cfg_4179_, 1);
v_bootstrap_4182_ = lean_ctor_get_uint8(v_cfg_4179_, sizeof(void*)*28);
v_extraDepTargets_4183_ = lean_ctor_get(v_cfg_4179_, 2);
v_precompileModules_4184_ = lean_ctor_get_uint8(v_cfg_4179_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4185_ = lean_ctor_get(v_cfg_4179_, 3);
v_srcDir_4186_ = lean_ctor_get(v_cfg_4179_, 4);
v_buildDir_4187_ = lean_ctor_get(v_cfg_4179_, 5);
v_leanLibDir_4188_ = lean_ctor_get(v_cfg_4179_, 6);
v_nativeLibDir_4189_ = lean_ctor_get(v_cfg_4179_, 7);
v_binDir_4190_ = lean_ctor_get(v_cfg_4179_, 8);
v_irDir_4191_ = lean_ctor_get(v_cfg_4179_, 9);
v_releaseRepo_4192_ = lean_ctor_get(v_cfg_4179_, 10);
v_buildArchive_4193_ = lean_ctor_get(v_cfg_4179_, 11);
v_preferReleaseBuild_4194_ = lean_ctor_get_uint8(v_cfg_4179_, sizeof(void*)*28 + 2);
v_testDriver_4195_ = lean_ctor_get(v_cfg_4179_, 12);
v_testDriverArgs_4196_ = lean_ctor_get(v_cfg_4179_, 13);
v_lintDriver_4197_ = lean_ctor_get(v_cfg_4179_, 14);
v_lintDriverArgs_4198_ = lean_ctor_get(v_cfg_4179_, 15);
v_version_4199_ = lean_ctor_get(v_cfg_4179_, 16);
v_versionTags_4200_ = lean_ctor_get(v_cfg_4179_, 17);
v_description_4201_ = lean_ctor_get(v_cfg_4179_, 18);
v_keywords_4202_ = lean_ctor_get(v_cfg_4179_, 19);
v_homepage_4203_ = lean_ctor_get(v_cfg_4179_, 20);
v_license_4204_ = lean_ctor_get(v_cfg_4179_, 21);
v_licenseFiles_4205_ = lean_ctor_get(v_cfg_4179_, 22);
v_readmeFile_4206_ = lean_ctor_get(v_cfg_4179_, 23);
v_reservoir_4207_ = lean_ctor_get_uint8(v_cfg_4179_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4208_ = lean_ctor_get(v_cfg_4179_, 24);
v_restoreAllArtifacts_x3f_4209_ = lean_ctor_get(v_cfg_4179_, 25);
v_libPrefixOnWindows_4210_ = lean_ctor_get_uint8(v_cfg_4179_, sizeof(void*)*28 + 4);
v_allowImportAll_4211_ = lean_ctor_get_uint8(v_cfg_4179_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4212_ = lean_ctor_get(v_cfg_4179_, 26);
v_checks_4213_ = lean_ctor_get(v_cfg_4179_, 27);
v_fixedToolchain_4214_ = lean_ctor_get_uint8(v_cfg_4179_, sizeof(void*)*28 + 6);
v_isSharedCheck_4222_ = !lean_is_exclusive(v_cfg_4179_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4216_ = v_cfg_4179_;
v_isShared_4217_ = v_isSharedCheck_4222_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_checks_4213_);
lean_inc(v_builtinLint_x3f_4212_);
lean_inc(v_restoreAllArtifacts_x3f_4209_);
lean_inc(v_enableArtifactCache_x3f_4208_);
lean_inc(v_readmeFile_4206_);
lean_inc(v_licenseFiles_4205_);
lean_inc(v_license_4204_);
lean_inc(v_homepage_4203_);
lean_inc(v_keywords_4202_);
lean_inc(v_description_4201_);
lean_inc(v_versionTags_4200_);
lean_inc(v_version_4199_);
lean_inc(v_lintDriverArgs_4198_);
lean_inc(v_lintDriver_4197_);
lean_inc(v_testDriverArgs_4196_);
lean_inc(v_testDriver_4195_);
lean_inc(v_buildArchive_4193_);
lean_inc(v_releaseRepo_4192_);
lean_inc(v_irDir_4191_);
lean_inc(v_binDir_4190_);
lean_inc(v_nativeLibDir_4189_);
lean_inc(v_leanLibDir_4188_);
lean_inc(v_buildDir_4187_);
lean_inc(v_srcDir_4186_);
lean_inc(v_moreGlobalServerArgs_4185_);
lean_inc(v_extraDepTargets_4183_);
lean_inc(v_toLeanConfig_4181_);
lean_inc(v_toWorkspaceConfig_4180_);
lean_dec(v_cfg_4179_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4222_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4218_; lean_object* v___x_4220_; 
v___x_4218_ = lean_apply_1(v_f_4178_, v_checks_4213_);
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 27, v___x_4218_);
v___x_4220_ = v___x_4216_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_toWorkspaceConfig_4180_);
lean_ctor_set(v_reuseFailAlloc_4221_, 1, v_toLeanConfig_4181_);
lean_ctor_set(v_reuseFailAlloc_4221_, 2, v_extraDepTargets_4183_);
lean_ctor_set(v_reuseFailAlloc_4221_, 3, v_moreGlobalServerArgs_4185_);
lean_ctor_set(v_reuseFailAlloc_4221_, 4, v_srcDir_4186_);
lean_ctor_set(v_reuseFailAlloc_4221_, 5, v_buildDir_4187_);
lean_ctor_set(v_reuseFailAlloc_4221_, 6, v_leanLibDir_4188_);
lean_ctor_set(v_reuseFailAlloc_4221_, 7, v_nativeLibDir_4189_);
lean_ctor_set(v_reuseFailAlloc_4221_, 8, v_binDir_4190_);
lean_ctor_set(v_reuseFailAlloc_4221_, 9, v_irDir_4191_);
lean_ctor_set(v_reuseFailAlloc_4221_, 10, v_releaseRepo_4192_);
lean_ctor_set(v_reuseFailAlloc_4221_, 11, v_buildArchive_4193_);
lean_ctor_set(v_reuseFailAlloc_4221_, 12, v_testDriver_4195_);
lean_ctor_set(v_reuseFailAlloc_4221_, 13, v_testDriverArgs_4196_);
lean_ctor_set(v_reuseFailAlloc_4221_, 14, v_lintDriver_4197_);
lean_ctor_set(v_reuseFailAlloc_4221_, 15, v_lintDriverArgs_4198_);
lean_ctor_set(v_reuseFailAlloc_4221_, 16, v_version_4199_);
lean_ctor_set(v_reuseFailAlloc_4221_, 17, v_versionTags_4200_);
lean_ctor_set(v_reuseFailAlloc_4221_, 18, v_description_4201_);
lean_ctor_set(v_reuseFailAlloc_4221_, 19, v_keywords_4202_);
lean_ctor_set(v_reuseFailAlloc_4221_, 20, v_homepage_4203_);
lean_ctor_set(v_reuseFailAlloc_4221_, 21, v_license_4204_);
lean_ctor_set(v_reuseFailAlloc_4221_, 22, v_licenseFiles_4205_);
lean_ctor_set(v_reuseFailAlloc_4221_, 23, v_readmeFile_4206_);
lean_ctor_set(v_reuseFailAlloc_4221_, 24, v_enableArtifactCache_x3f_4208_);
lean_ctor_set(v_reuseFailAlloc_4221_, 25, v_restoreAllArtifacts_x3f_4209_);
lean_ctor_set(v_reuseFailAlloc_4221_, 26, v_builtinLint_x3f_4212_);
lean_ctor_set(v_reuseFailAlloc_4221_, 27, v___x_4218_);
lean_ctor_set_uint8(v_reuseFailAlloc_4221_, sizeof(void*)*28, v_bootstrap_4182_);
lean_ctor_set_uint8(v_reuseFailAlloc_4221_, sizeof(void*)*28 + 1, v_precompileModules_4184_);
lean_ctor_set_uint8(v_reuseFailAlloc_4221_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4194_);
lean_ctor_set_uint8(v_reuseFailAlloc_4221_, sizeof(void*)*28 + 3, v_reservoir_4207_);
lean_ctor_set_uint8(v_reuseFailAlloc_4221_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4210_);
lean_ctor_set_uint8(v_reuseFailAlloc_4221_, sizeof(void*)*28 + 5, v_allowImportAll_4211_);
lean_ctor_set_uint8(v_reuseFailAlloc_4221_, sizeof(void*)*28 + 6, v_fixedToolchain_4214_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
lean_object* l_Lake_PackageConfig_checks___proj___redArg(){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = ((lean_object*)(l_Lake_PackageConfig_checks___proj___redArg___closed__3));
return v___x_4232_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_checks___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4233_;
v_res_4233_ = l_Lake_PackageConfig_checks___proj___redArg();
stack->m_obj
 = v_res_4233_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___boxed(lean_object* v___dummy_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lake_PackageConfig_checks___proj___redArg();
return v_res_4235_;
}
}
static lean_object* _init_l_Lake_PackageConfig_checks___proj___closed__0(void){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l_Lake_PackageConfig_checks___proj___redArg();
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj(lean_object* v_p_4237_, lean_object* v_n_4238_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = lean_obj_once(&l_Lake_PackageConfig_checks___proj___closed__0, &l_Lake_PackageConfig_checks___proj___closed__0_once, _init_l_Lake_PackageConfig_checks___proj___closed__0);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___boxed(lean_object* v_p_4240_, lean_object* v_n_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Lake_PackageConfig_checks___proj(v_p_4240_, v_n_4241_);
lean_dec(v_n_4241_);
lean_dec(v_p_4240_);
return v_res_4242_;
}
}
lean_object* l_Lake_PackageConfig_checks_instConfigField___redArg(){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = lean_obj_once(&l_Lake_PackageConfig_checks___proj___closed__0, &l_Lake_PackageConfig_checks___proj___closed__0_once, _init_l_Lake_PackageConfig_checks___proj___closed__0);
return v___x_4244_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_checks_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4245_;
v_res_4245_ = l_Lake_PackageConfig_checks_instConfigField___redArg();
stack->m_obj
 = v_res_4245_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___redArg___boxed(lean_object* v___dummy_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Lake_PackageConfig_checks_instConfigField___redArg();
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField(lean_object* v_p_4248_, lean_object* v_n_4249_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = lean_obj_once(&l_Lake_PackageConfig_checks___proj___closed__0, &l_Lake_PackageConfig_checks___proj___closed__0_once, _init_l_Lake_PackageConfig_checks___proj___closed__0);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___boxed(lean_object* v_p_4251_, lean_object* v_n_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l_Lake_PackageConfig_checks_instConfigField(v_p_4251_, v_n_4252_);
lean_dec(v_n_4252_);
lean_dec(v_p_4251_);
return v_res_4253_;
}
}
uint8_t l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0(lean_object* v_cfg_4254_){
_start:
{
uint8_t v_fixedToolchain_4255_; 
v_fixedToolchain_4255_ = lean_ctor_get_uint8(v_cfg_4254_, sizeof(void*)*28 + 6);
return v_fixedToolchain_4255_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_4254_ = stack[0].m_obj;
uint8_t v_res_4256_;
v_res_4256_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0(v_cfg_4254_);
stack->m_num = v_res_4256_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0___boxed(lean_object* v_cfg_4257_){
_start:
{
uint8_t v_res_4258_; lean_object* v_r_4259_; 
v_res_4258_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0(v_cfg_4257_);
lean_dec_ref(v_cfg_4257_);
v_r_4259_ = lean_box(v_res_4258_);
return v_r_4259_;
}
}
lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1(uint8_t v_val_4260_, lean_object* v_cfg_4261_){
_start:
{
lean_object* v_toWorkspaceConfig_4262_; lean_object* v_toLeanConfig_4263_; uint8_t v_bootstrap_4264_; lean_object* v_extraDepTargets_4265_; uint8_t v_precompileModules_4266_; lean_object* v_moreGlobalServerArgs_4267_; lean_object* v_srcDir_4268_; lean_object* v_buildDir_4269_; lean_object* v_leanLibDir_4270_; lean_object* v_nativeLibDir_4271_; lean_object* v_binDir_4272_; lean_object* v_irDir_4273_; lean_object* v_releaseRepo_4274_; lean_object* v_buildArchive_4275_; uint8_t v_preferReleaseBuild_4276_; lean_object* v_testDriver_4277_; lean_object* v_testDriverArgs_4278_; lean_object* v_lintDriver_4279_; lean_object* v_lintDriverArgs_4280_; lean_object* v_version_4281_; lean_object* v_versionTags_4282_; lean_object* v_description_4283_; lean_object* v_keywords_4284_; lean_object* v_homepage_4285_; lean_object* v_license_4286_; lean_object* v_licenseFiles_4287_; lean_object* v_readmeFile_4288_; uint8_t v_reservoir_4289_; lean_object* v_enableArtifactCache_x3f_4290_; lean_object* v_restoreAllArtifacts_x3f_4291_; uint8_t v_libPrefixOnWindows_4292_; uint8_t v_allowImportAll_4293_; lean_object* v_builtinLint_x3f_4294_; lean_object* v_checks_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
v_toWorkspaceConfig_4262_ = lean_ctor_get(v_cfg_4261_, 0);
v_toLeanConfig_4263_ = lean_ctor_get(v_cfg_4261_, 1);
v_bootstrap_4264_ = lean_ctor_get_uint8(v_cfg_4261_, sizeof(void*)*28);
v_extraDepTargets_4265_ = lean_ctor_get(v_cfg_4261_, 2);
v_precompileModules_4266_ = lean_ctor_get_uint8(v_cfg_4261_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4267_ = lean_ctor_get(v_cfg_4261_, 3);
v_srcDir_4268_ = lean_ctor_get(v_cfg_4261_, 4);
v_buildDir_4269_ = lean_ctor_get(v_cfg_4261_, 5);
v_leanLibDir_4270_ = lean_ctor_get(v_cfg_4261_, 6);
v_nativeLibDir_4271_ = lean_ctor_get(v_cfg_4261_, 7);
v_binDir_4272_ = lean_ctor_get(v_cfg_4261_, 8);
v_irDir_4273_ = lean_ctor_get(v_cfg_4261_, 9);
v_releaseRepo_4274_ = lean_ctor_get(v_cfg_4261_, 10);
v_buildArchive_4275_ = lean_ctor_get(v_cfg_4261_, 11);
v_preferReleaseBuild_4276_ = lean_ctor_get_uint8(v_cfg_4261_, sizeof(void*)*28 + 2);
v_testDriver_4277_ = lean_ctor_get(v_cfg_4261_, 12);
v_testDriverArgs_4278_ = lean_ctor_get(v_cfg_4261_, 13);
v_lintDriver_4279_ = lean_ctor_get(v_cfg_4261_, 14);
v_lintDriverArgs_4280_ = lean_ctor_get(v_cfg_4261_, 15);
v_version_4281_ = lean_ctor_get(v_cfg_4261_, 16);
v_versionTags_4282_ = lean_ctor_get(v_cfg_4261_, 17);
v_description_4283_ = lean_ctor_get(v_cfg_4261_, 18);
v_keywords_4284_ = lean_ctor_get(v_cfg_4261_, 19);
v_homepage_4285_ = lean_ctor_get(v_cfg_4261_, 20);
v_license_4286_ = lean_ctor_get(v_cfg_4261_, 21);
v_licenseFiles_4287_ = lean_ctor_get(v_cfg_4261_, 22);
v_readmeFile_4288_ = lean_ctor_get(v_cfg_4261_, 23);
v_reservoir_4289_ = lean_ctor_get_uint8(v_cfg_4261_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4290_ = lean_ctor_get(v_cfg_4261_, 24);
v_restoreAllArtifacts_x3f_4291_ = lean_ctor_get(v_cfg_4261_, 25);
v_libPrefixOnWindows_4292_ = lean_ctor_get_uint8(v_cfg_4261_, sizeof(void*)*28 + 4);
v_allowImportAll_4293_ = lean_ctor_get_uint8(v_cfg_4261_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4294_ = lean_ctor_get(v_cfg_4261_, 26);
v_checks_4295_ = lean_ctor_get(v_cfg_4261_, 27);
v_isSharedCheck_4302_ = !lean_is_exclusive(v_cfg_4261_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v_cfg_4261_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_checks_4295_);
lean_inc(v_builtinLint_x3f_4294_);
lean_inc(v_restoreAllArtifacts_x3f_4291_);
lean_inc(v_enableArtifactCache_x3f_4290_);
lean_inc(v_readmeFile_4288_);
lean_inc(v_licenseFiles_4287_);
lean_inc(v_license_4286_);
lean_inc(v_homepage_4285_);
lean_inc(v_keywords_4284_);
lean_inc(v_description_4283_);
lean_inc(v_versionTags_4282_);
lean_inc(v_version_4281_);
lean_inc(v_lintDriverArgs_4280_);
lean_inc(v_lintDriver_4279_);
lean_inc(v_testDriverArgs_4278_);
lean_inc(v_testDriver_4277_);
lean_inc(v_buildArchive_4275_);
lean_inc(v_releaseRepo_4274_);
lean_inc(v_irDir_4273_);
lean_inc(v_binDir_4272_);
lean_inc(v_nativeLibDir_4271_);
lean_inc(v_leanLibDir_4270_);
lean_inc(v_buildDir_4269_);
lean_inc(v_srcDir_4268_);
lean_inc(v_moreGlobalServerArgs_4267_);
lean_inc(v_extraDepTargets_4265_);
lean_inc(v_toLeanConfig_4263_);
lean_inc(v_toWorkspaceConfig_4262_);
lean_dec(v_cfg_4261_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_toWorkspaceConfig_4262_);
lean_ctor_set(v_reuseFailAlloc_4301_, 1, v_toLeanConfig_4263_);
lean_ctor_set(v_reuseFailAlloc_4301_, 2, v_extraDepTargets_4265_);
lean_ctor_set(v_reuseFailAlloc_4301_, 3, v_moreGlobalServerArgs_4267_);
lean_ctor_set(v_reuseFailAlloc_4301_, 4, v_srcDir_4268_);
lean_ctor_set(v_reuseFailAlloc_4301_, 5, v_buildDir_4269_);
lean_ctor_set(v_reuseFailAlloc_4301_, 6, v_leanLibDir_4270_);
lean_ctor_set(v_reuseFailAlloc_4301_, 7, v_nativeLibDir_4271_);
lean_ctor_set(v_reuseFailAlloc_4301_, 8, v_binDir_4272_);
lean_ctor_set(v_reuseFailAlloc_4301_, 9, v_irDir_4273_);
lean_ctor_set(v_reuseFailAlloc_4301_, 10, v_releaseRepo_4274_);
lean_ctor_set(v_reuseFailAlloc_4301_, 11, v_buildArchive_4275_);
lean_ctor_set(v_reuseFailAlloc_4301_, 12, v_testDriver_4277_);
lean_ctor_set(v_reuseFailAlloc_4301_, 13, v_testDriverArgs_4278_);
lean_ctor_set(v_reuseFailAlloc_4301_, 14, v_lintDriver_4279_);
lean_ctor_set(v_reuseFailAlloc_4301_, 15, v_lintDriverArgs_4280_);
lean_ctor_set(v_reuseFailAlloc_4301_, 16, v_version_4281_);
lean_ctor_set(v_reuseFailAlloc_4301_, 17, v_versionTags_4282_);
lean_ctor_set(v_reuseFailAlloc_4301_, 18, v_description_4283_);
lean_ctor_set(v_reuseFailAlloc_4301_, 19, v_keywords_4284_);
lean_ctor_set(v_reuseFailAlloc_4301_, 20, v_homepage_4285_);
lean_ctor_set(v_reuseFailAlloc_4301_, 21, v_license_4286_);
lean_ctor_set(v_reuseFailAlloc_4301_, 22, v_licenseFiles_4287_);
lean_ctor_set(v_reuseFailAlloc_4301_, 23, v_readmeFile_4288_);
lean_ctor_set(v_reuseFailAlloc_4301_, 24, v_enableArtifactCache_x3f_4290_);
lean_ctor_set(v_reuseFailAlloc_4301_, 25, v_restoreAllArtifacts_x3f_4291_);
lean_ctor_set(v_reuseFailAlloc_4301_, 26, v_builtinLint_x3f_4294_);
lean_ctor_set(v_reuseFailAlloc_4301_, 27, v_checks_4295_);
lean_ctor_set_uint8(v_reuseFailAlloc_4301_, sizeof(void*)*28, v_bootstrap_4264_);
lean_ctor_set_uint8(v_reuseFailAlloc_4301_, sizeof(void*)*28 + 1, v_precompileModules_4266_);
lean_ctor_set_uint8(v_reuseFailAlloc_4301_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4276_);
lean_ctor_set_uint8(v_reuseFailAlloc_4301_, sizeof(void*)*28 + 3, v_reservoir_4289_);
lean_ctor_set_uint8(v_reuseFailAlloc_4301_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4292_);
lean_ctor_set_uint8(v_reuseFailAlloc_4301_, sizeof(void*)*28 + 5, v_allowImportAll_4293_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
lean_ctor_set_uint8(v___x_4300_, sizeof(void*)*28 + 6, v_val_4260_);
return v___x_4300_;
}
}
}
}
LEAN_EXPORT void l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_4260_ = stack[0].m_num;
lean_object* v_cfg_4261_ = stack[1].m_obj;
lean_object* v_res_4303_;
v_res_4303_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1(v_val_4260_, v_cfg_4261_);
stack->m_obj
 = v_res_4303_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1___boxed(lean_object* v_val_4304_, lean_object* v_cfg_4305_){
_start:
{
uint8_t v_val_143__boxed_4306_; lean_object* v_res_4307_; 
v_val_143__boxed_4306_ = lean_unbox(v_val_4304_);
v_res_4307_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1(v_val_143__boxed_4306_, v_cfg_4305_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__2(lean_object* v_f_4308_, lean_object* v_cfg_4309_){
_start:
{
lean_object* v_toWorkspaceConfig_4310_; lean_object* v_toLeanConfig_4311_; uint8_t v_bootstrap_4312_; lean_object* v_extraDepTargets_4313_; uint8_t v_precompileModules_4314_; lean_object* v_moreGlobalServerArgs_4315_; lean_object* v_srcDir_4316_; lean_object* v_buildDir_4317_; lean_object* v_leanLibDir_4318_; lean_object* v_nativeLibDir_4319_; lean_object* v_binDir_4320_; lean_object* v_irDir_4321_; lean_object* v_releaseRepo_4322_; lean_object* v_buildArchive_4323_; uint8_t v_preferReleaseBuild_4324_; lean_object* v_testDriver_4325_; lean_object* v_testDriverArgs_4326_; lean_object* v_lintDriver_4327_; lean_object* v_lintDriverArgs_4328_; lean_object* v_version_4329_; lean_object* v_versionTags_4330_; lean_object* v_description_4331_; lean_object* v_keywords_4332_; lean_object* v_homepage_4333_; lean_object* v_license_4334_; lean_object* v_licenseFiles_4335_; lean_object* v_readmeFile_4336_; uint8_t v_reservoir_4337_; lean_object* v_enableArtifactCache_x3f_4338_; lean_object* v_restoreAllArtifacts_x3f_4339_; uint8_t v_libPrefixOnWindows_4340_; uint8_t v_allowImportAll_4341_; lean_object* v_builtinLint_x3f_4342_; lean_object* v_checks_4343_; uint8_t v_fixedToolchain_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4354_; 
v_toWorkspaceConfig_4310_ = lean_ctor_get(v_cfg_4309_, 0);
v_toLeanConfig_4311_ = lean_ctor_get(v_cfg_4309_, 1);
v_bootstrap_4312_ = lean_ctor_get_uint8(v_cfg_4309_, sizeof(void*)*28);
v_extraDepTargets_4313_ = lean_ctor_get(v_cfg_4309_, 2);
v_precompileModules_4314_ = lean_ctor_get_uint8(v_cfg_4309_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4315_ = lean_ctor_get(v_cfg_4309_, 3);
v_srcDir_4316_ = lean_ctor_get(v_cfg_4309_, 4);
v_buildDir_4317_ = lean_ctor_get(v_cfg_4309_, 5);
v_leanLibDir_4318_ = lean_ctor_get(v_cfg_4309_, 6);
v_nativeLibDir_4319_ = lean_ctor_get(v_cfg_4309_, 7);
v_binDir_4320_ = lean_ctor_get(v_cfg_4309_, 8);
v_irDir_4321_ = lean_ctor_get(v_cfg_4309_, 9);
v_releaseRepo_4322_ = lean_ctor_get(v_cfg_4309_, 10);
v_buildArchive_4323_ = lean_ctor_get(v_cfg_4309_, 11);
v_preferReleaseBuild_4324_ = lean_ctor_get_uint8(v_cfg_4309_, sizeof(void*)*28 + 2);
v_testDriver_4325_ = lean_ctor_get(v_cfg_4309_, 12);
v_testDriverArgs_4326_ = lean_ctor_get(v_cfg_4309_, 13);
v_lintDriver_4327_ = lean_ctor_get(v_cfg_4309_, 14);
v_lintDriverArgs_4328_ = lean_ctor_get(v_cfg_4309_, 15);
v_version_4329_ = lean_ctor_get(v_cfg_4309_, 16);
v_versionTags_4330_ = lean_ctor_get(v_cfg_4309_, 17);
v_description_4331_ = lean_ctor_get(v_cfg_4309_, 18);
v_keywords_4332_ = lean_ctor_get(v_cfg_4309_, 19);
v_homepage_4333_ = lean_ctor_get(v_cfg_4309_, 20);
v_license_4334_ = lean_ctor_get(v_cfg_4309_, 21);
v_licenseFiles_4335_ = lean_ctor_get(v_cfg_4309_, 22);
v_readmeFile_4336_ = lean_ctor_get(v_cfg_4309_, 23);
v_reservoir_4337_ = lean_ctor_get_uint8(v_cfg_4309_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4338_ = lean_ctor_get(v_cfg_4309_, 24);
v_restoreAllArtifacts_x3f_4339_ = lean_ctor_get(v_cfg_4309_, 25);
v_libPrefixOnWindows_4340_ = lean_ctor_get_uint8(v_cfg_4309_, sizeof(void*)*28 + 4);
v_allowImportAll_4341_ = lean_ctor_get_uint8(v_cfg_4309_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4342_ = lean_ctor_get(v_cfg_4309_, 26);
v_checks_4343_ = lean_ctor_get(v_cfg_4309_, 27);
v_fixedToolchain_4344_ = lean_ctor_get_uint8(v_cfg_4309_, sizeof(void*)*28 + 6);
v_isSharedCheck_4354_ = !lean_is_exclusive(v_cfg_4309_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4346_ = v_cfg_4309_;
v_isShared_4347_ = v_isSharedCheck_4354_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_checks_4343_);
lean_inc(v_builtinLint_x3f_4342_);
lean_inc(v_restoreAllArtifacts_x3f_4339_);
lean_inc(v_enableArtifactCache_x3f_4338_);
lean_inc(v_readmeFile_4336_);
lean_inc(v_licenseFiles_4335_);
lean_inc(v_license_4334_);
lean_inc(v_homepage_4333_);
lean_inc(v_keywords_4332_);
lean_inc(v_description_4331_);
lean_inc(v_versionTags_4330_);
lean_inc(v_version_4329_);
lean_inc(v_lintDriverArgs_4328_);
lean_inc(v_lintDriver_4327_);
lean_inc(v_testDriverArgs_4326_);
lean_inc(v_testDriver_4325_);
lean_inc(v_buildArchive_4323_);
lean_inc(v_releaseRepo_4322_);
lean_inc(v_irDir_4321_);
lean_inc(v_binDir_4320_);
lean_inc(v_nativeLibDir_4319_);
lean_inc(v_leanLibDir_4318_);
lean_inc(v_buildDir_4317_);
lean_inc(v_srcDir_4316_);
lean_inc(v_moreGlobalServerArgs_4315_);
lean_inc(v_extraDepTargets_4313_);
lean_inc(v_toLeanConfig_4311_);
lean_inc(v_toWorkspaceConfig_4310_);
lean_dec(v_cfg_4309_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4354_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4351_; 
v___x_4348_ = lean_box(v_fixedToolchain_4344_);
v___x_4349_ = lean_apply_1(v_f_4308_, v___x_4348_);
if (v_isShared_4347_ == 0)
{
v___x_4351_ = v___x_4346_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_toWorkspaceConfig_4310_);
lean_ctor_set(v_reuseFailAlloc_4353_, 1, v_toLeanConfig_4311_);
lean_ctor_set(v_reuseFailAlloc_4353_, 2, v_extraDepTargets_4313_);
lean_ctor_set(v_reuseFailAlloc_4353_, 3, v_moreGlobalServerArgs_4315_);
lean_ctor_set(v_reuseFailAlloc_4353_, 4, v_srcDir_4316_);
lean_ctor_set(v_reuseFailAlloc_4353_, 5, v_buildDir_4317_);
lean_ctor_set(v_reuseFailAlloc_4353_, 6, v_leanLibDir_4318_);
lean_ctor_set(v_reuseFailAlloc_4353_, 7, v_nativeLibDir_4319_);
lean_ctor_set(v_reuseFailAlloc_4353_, 8, v_binDir_4320_);
lean_ctor_set(v_reuseFailAlloc_4353_, 9, v_irDir_4321_);
lean_ctor_set(v_reuseFailAlloc_4353_, 10, v_releaseRepo_4322_);
lean_ctor_set(v_reuseFailAlloc_4353_, 11, v_buildArchive_4323_);
lean_ctor_set(v_reuseFailAlloc_4353_, 12, v_testDriver_4325_);
lean_ctor_set(v_reuseFailAlloc_4353_, 13, v_testDriverArgs_4326_);
lean_ctor_set(v_reuseFailAlloc_4353_, 14, v_lintDriver_4327_);
lean_ctor_set(v_reuseFailAlloc_4353_, 15, v_lintDriverArgs_4328_);
lean_ctor_set(v_reuseFailAlloc_4353_, 16, v_version_4329_);
lean_ctor_set(v_reuseFailAlloc_4353_, 17, v_versionTags_4330_);
lean_ctor_set(v_reuseFailAlloc_4353_, 18, v_description_4331_);
lean_ctor_set(v_reuseFailAlloc_4353_, 19, v_keywords_4332_);
lean_ctor_set(v_reuseFailAlloc_4353_, 20, v_homepage_4333_);
lean_ctor_set(v_reuseFailAlloc_4353_, 21, v_license_4334_);
lean_ctor_set(v_reuseFailAlloc_4353_, 22, v_licenseFiles_4335_);
lean_ctor_set(v_reuseFailAlloc_4353_, 23, v_readmeFile_4336_);
lean_ctor_set(v_reuseFailAlloc_4353_, 24, v_enableArtifactCache_x3f_4338_);
lean_ctor_set(v_reuseFailAlloc_4353_, 25, v_restoreAllArtifacts_x3f_4339_);
lean_ctor_set(v_reuseFailAlloc_4353_, 26, v_builtinLint_x3f_4342_);
lean_ctor_set(v_reuseFailAlloc_4353_, 27, v_checks_4343_);
lean_ctor_set_uint8(v_reuseFailAlloc_4353_, sizeof(void*)*28, v_bootstrap_4312_);
lean_ctor_set_uint8(v_reuseFailAlloc_4353_, sizeof(void*)*28 + 1, v_precompileModules_4314_);
lean_ctor_set_uint8(v_reuseFailAlloc_4353_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4324_);
lean_ctor_set_uint8(v_reuseFailAlloc_4353_, sizeof(void*)*28 + 3, v_reservoir_4337_);
lean_ctor_set_uint8(v_reuseFailAlloc_4353_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4340_);
lean_ctor_set_uint8(v_reuseFailAlloc_4353_, sizeof(void*)*28 + 5, v_allowImportAll_4341_);
v___x_4351_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
uint8_t v___x_4352_; 
v___x_4352_ = lean_unbox(v___x_4349_);
lean_ctor_set_uint8(v___x_4351_, sizeof(void*)*28 + 6, v___x_4352_);
return v___x_4351_;
}
}
}
}
lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg(){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = ((lean_object*)(l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__3));
return v___x_4364_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_fixedToolchain___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4365_;
v_res_4365_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg();
stack->m_obj
 = v_res_4365_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___boxed(lean_object* v___dummy_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg();
return v_res_4367_;
}
}
static lean_object* _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0(void){
_start:
{
lean_object* v___x_4368_; 
v___x_4368_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg();
return v___x_4368_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj(lean_object* v_p_4369_, lean_object* v_n_4370_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = lean_obj_once(&l_Lake_PackageConfig_fixedToolchain___proj___closed__0, &l_Lake_PackageConfig_fixedToolchain___proj___closed__0_once, _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___boxed(lean_object* v_p_4372_, lean_object* v_n_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_4372_, v_n_4373_);
lean_dec(v_n_4373_);
lean_dec(v_p_4372_);
return v_res_4374_;
}
}
lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg(){
_start:
{
lean_object* v___x_4376_; 
v___x_4376_ = lean_obj_once(&l_Lake_PackageConfig_fixedToolchain___proj___closed__0, &l_Lake_PackageConfig_fixedToolchain___proj___closed__0_once, _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0);
return v___x_4376_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4377_;
v_res_4377_ = l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg();
stack->m_obj
 = v_res_4377_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg___boxed(lean_object* v___dummy_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg();
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField(lean_object* v_p_4380_, lean_object* v_n_4381_){
_start:
{
lean_object* v___x_4382_; 
v___x_4382_ = lean_obj_once(&l_Lake_PackageConfig_fixedToolchain___proj___closed__0, &l_Lake_PackageConfig_fixedToolchain___proj___closed__0_once, _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___boxed(lean_object* v_p_4383_, lean_object* v_n_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l_Lake_PackageConfig_fixedToolchain_instConfigField(v_p_4383_, v_n_4384_);
lean_dec(v_n_4384_);
lean_dec(v_p_4383_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0(lean_object* v_cfg_4386_){
_start:
{
lean_object* v_toWorkspaceConfig_4387_; 
v_toWorkspaceConfig_4387_ = lean_ctor_get(v_cfg_4386_, 0);
lean_inc_ref(v_toWorkspaceConfig_4387_);
return v_toWorkspaceConfig_4387_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0___boxed(lean_object* v_cfg_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0(v_cfg_4388_);
lean_dec_ref(v_cfg_4388_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__1(lean_object* v_val_4390_, lean_object* v_cfg_4391_){
_start:
{
lean_object* v_toLeanConfig_4392_; uint8_t v_bootstrap_4393_; lean_object* v_extraDepTargets_4394_; uint8_t v_precompileModules_4395_; lean_object* v_moreGlobalServerArgs_4396_; lean_object* v_srcDir_4397_; lean_object* v_buildDir_4398_; lean_object* v_leanLibDir_4399_; lean_object* v_nativeLibDir_4400_; lean_object* v_binDir_4401_; lean_object* v_irDir_4402_; lean_object* v_releaseRepo_4403_; lean_object* v_buildArchive_4404_; uint8_t v_preferReleaseBuild_4405_; lean_object* v_testDriver_4406_; lean_object* v_testDriverArgs_4407_; lean_object* v_lintDriver_4408_; lean_object* v_lintDriverArgs_4409_; lean_object* v_version_4410_; lean_object* v_versionTags_4411_; lean_object* v_description_4412_; lean_object* v_keywords_4413_; lean_object* v_homepage_4414_; lean_object* v_license_4415_; lean_object* v_licenseFiles_4416_; lean_object* v_readmeFile_4417_; uint8_t v_reservoir_4418_; lean_object* v_enableArtifactCache_x3f_4419_; lean_object* v_restoreAllArtifacts_x3f_4420_; uint8_t v_libPrefixOnWindows_4421_; uint8_t v_allowImportAll_4422_; lean_object* v_builtinLint_x3f_4423_; lean_object* v_checks_4424_; uint8_t v_fixedToolchain_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
v_toLeanConfig_4392_ = lean_ctor_get(v_cfg_4391_, 1);
v_bootstrap_4393_ = lean_ctor_get_uint8(v_cfg_4391_, sizeof(void*)*28);
v_extraDepTargets_4394_ = lean_ctor_get(v_cfg_4391_, 2);
v_precompileModules_4395_ = lean_ctor_get_uint8(v_cfg_4391_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4396_ = lean_ctor_get(v_cfg_4391_, 3);
v_srcDir_4397_ = lean_ctor_get(v_cfg_4391_, 4);
v_buildDir_4398_ = lean_ctor_get(v_cfg_4391_, 5);
v_leanLibDir_4399_ = lean_ctor_get(v_cfg_4391_, 6);
v_nativeLibDir_4400_ = lean_ctor_get(v_cfg_4391_, 7);
v_binDir_4401_ = lean_ctor_get(v_cfg_4391_, 8);
v_irDir_4402_ = lean_ctor_get(v_cfg_4391_, 9);
v_releaseRepo_4403_ = lean_ctor_get(v_cfg_4391_, 10);
v_buildArchive_4404_ = lean_ctor_get(v_cfg_4391_, 11);
v_preferReleaseBuild_4405_ = lean_ctor_get_uint8(v_cfg_4391_, sizeof(void*)*28 + 2);
v_testDriver_4406_ = lean_ctor_get(v_cfg_4391_, 12);
v_testDriverArgs_4407_ = lean_ctor_get(v_cfg_4391_, 13);
v_lintDriver_4408_ = lean_ctor_get(v_cfg_4391_, 14);
v_lintDriverArgs_4409_ = lean_ctor_get(v_cfg_4391_, 15);
v_version_4410_ = lean_ctor_get(v_cfg_4391_, 16);
v_versionTags_4411_ = lean_ctor_get(v_cfg_4391_, 17);
v_description_4412_ = lean_ctor_get(v_cfg_4391_, 18);
v_keywords_4413_ = lean_ctor_get(v_cfg_4391_, 19);
v_homepage_4414_ = lean_ctor_get(v_cfg_4391_, 20);
v_license_4415_ = lean_ctor_get(v_cfg_4391_, 21);
v_licenseFiles_4416_ = lean_ctor_get(v_cfg_4391_, 22);
v_readmeFile_4417_ = lean_ctor_get(v_cfg_4391_, 23);
v_reservoir_4418_ = lean_ctor_get_uint8(v_cfg_4391_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4419_ = lean_ctor_get(v_cfg_4391_, 24);
v_restoreAllArtifacts_x3f_4420_ = lean_ctor_get(v_cfg_4391_, 25);
v_libPrefixOnWindows_4421_ = lean_ctor_get_uint8(v_cfg_4391_, sizeof(void*)*28 + 4);
v_allowImportAll_4422_ = lean_ctor_get_uint8(v_cfg_4391_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4423_ = lean_ctor_get(v_cfg_4391_, 26);
v_checks_4424_ = lean_ctor_get(v_cfg_4391_, 27);
v_fixedToolchain_4425_ = lean_ctor_get_uint8(v_cfg_4391_, sizeof(void*)*28 + 6);
v_isSharedCheck_4432_ = !lean_is_exclusive(v_cfg_4391_);
if (v_isSharedCheck_4432_ == 0)
{
lean_object* v_unused_4433_; 
v_unused_4433_ = lean_ctor_get(v_cfg_4391_, 0);
lean_dec(v_unused_4433_);
v___x_4427_ = v_cfg_4391_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_checks_4424_);
lean_inc(v_builtinLint_x3f_4423_);
lean_inc(v_restoreAllArtifacts_x3f_4420_);
lean_inc(v_enableArtifactCache_x3f_4419_);
lean_inc(v_readmeFile_4417_);
lean_inc(v_licenseFiles_4416_);
lean_inc(v_license_4415_);
lean_inc(v_homepage_4414_);
lean_inc(v_keywords_4413_);
lean_inc(v_description_4412_);
lean_inc(v_versionTags_4411_);
lean_inc(v_version_4410_);
lean_inc(v_lintDriverArgs_4409_);
lean_inc(v_lintDriver_4408_);
lean_inc(v_testDriverArgs_4407_);
lean_inc(v_testDriver_4406_);
lean_inc(v_buildArchive_4404_);
lean_inc(v_releaseRepo_4403_);
lean_inc(v_irDir_4402_);
lean_inc(v_binDir_4401_);
lean_inc(v_nativeLibDir_4400_);
lean_inc(v_leanLibDir_4399_);
lean_inc(v_buildDir_4398_);
lean_inc(v_srcDir_4397_);
lean_inc(v_moreGlobalServerArgs_4396_);
lean_inc(v_extraDepTargets_4394_);
lean_inc(v_toLeanConfig_4392_);
lean_dec(v_cfg_4391_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v_val_4390_);
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_val_4390_);
lean_ctor_set(v_reuseFailAlloc_4431_, 1, v_toLeanConfig_4392_);
lean_ctor_set(v_reuseFailAlloc_4431_, 2, v_extraDepTargets_4394_);
lean_ctor_set(v_reuseFailAlloc_4431_, 3, v_moreGlobalServerArgs_4396_);
lean_ctor_set(v_reuseFailAlloc_4431_, 4, v_srcDir_4397_);
lean_ctor_set(v_reuseFailAlloc_4431_, 5, v_buildDir_4398_);
lean_ctor_set(v_reuseFailAlloc_4431_, 6, v_leanLibDir_4399_);
lean_ctor_set(v_reuseFailAlloc_4431_, 7, v_nativeLibDir_4400_);
lean_ctor_set(v_reuseFailAlloc_4431_, 8, v_binDir_4401_);
lean_ctor_set(v_reuseFailAlloc_4431_, 9, v_irDir_4402_);
lean_ctor_set(v_reuseFailAlloc_4431_, 10, v_releaseRepo_4403_);
lean_ctor_set(v_reuseFailAlloc_4431_, 11, v_buildArchive_4404_);
lean_ctor_set(v_reuseFailAlloc_4431_, 12, v_testDriver_4406_);
lean_ctor_set(v_reuseFailAlloc_4431_, 13, v_testDriverArgs_4407_);
lean_ctor_set(v_reuseFailAlloc_4431_, 14, v_lintDriver_4408_);
lean_ctor_set(v_reuseFailAlloc_4431_, 15, v_lintDriverArgs_4409_);
lean_ctor_set(v_reuseFailAlloc_4431_, 16, v_version_4410_);
lean_ctor_set(v_reuseFailAlloc_4431_, 17, v_versionTags_4411_);
lean_ctor_set(v_reuseFailAlloc_4431_, 18, v_description_4412_);
lean_ctor_set(v_reuseFailAlloc_4431_, 19, v_keywords_4413_);
lean_ctor_set(v_reuseFailAlloc_4431_, 20, v_homepage_4414_);
lean_ctor_set(v_reuseFailAlloc_4431_, 21, v_license_4415_);
lean_ctor_set(v_reuseFailAlloc_4431_, 22, v_licenseFiles_4416_);
lean_ctor_set(v_reuseFailAlloc_4431_, 23, v_readmeFile_4417_);
lean_ctor_set(v_reuseFailAlloc_4431_, 24, v_enableArtifactCache_x3f_4419_);
lean_ctor_set(v_reuseFailAlloc_4431_, 25, v_restoreAllArtifacts_x3f_4420_);
lean_ctor_set(v_reuseFailAlloc_4431_, 26, v_builtinLint_x3f_4423_);
lean_ctor_set(v_reuseFailAlloc_4431_, 27, v_checks_4424_);
lean_ctor_set_uint8(v_reuseFailAlloc_4431_, sizeof(void*)*28, v_bootstrap_4393_);
lean_ctor_set_uint8(v_reuseFailAlloc_4431_, sizeof(void*)*28 + 1, v_precompileModules_4395_);
lean_ctor_set_uint8(v_reuseFailAlloc_4431_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4405_);
lean_ctor_set_uint8(v_reuseFailAlloc_4431_, sizeof(void*)*28 + 3, v_reservoir_4418_);
lean_ctor_set_uint8(v_reuseFailAlloc_4431_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4421_);
lean_ctor_set_uint8(v_reuseFailAlloc_4431_, sizeof(void*)*28 + 5, v_allowImportAll_4422_);
lean_ctor_set_uint8(v_reuseFailAlloc_4431_, sizeof(void*)*28 + 6, v_fixedToolchain_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__2(lean_object* v_f_4434_, lean_object* v_cfg_4435_){
_start:
{
lean_object* v_toWorkspaceConfig_4436_; lean_object* v_toLeanConfig_4437_; uint8_t v_bootstrap_4438_; lean_object* v_extraDepTargets_4439_; uint8_t v_precompileModules_4440_; lean_object* v_moreGlobalServerArgs_4441_; lean_object* v_srcDir_4442_; lean_object* v_buildDir_4443_; lean_object* v_leanLibDir_4444_; lean_object* v_nativeLibDir_4445_; lean_object* v_binDir_4446_; lean_object* v_irDir_4447_; lean_object* v_releaseRepo_4448_; lean_object* v_buildArchive_4449_; uint8_t v_preferReleaseBuild_4450_; lean_object* v_testDriver_4451_; lean_object* v_testDriverArgs_4452_; lean_object* v_lintDriver_4453_; lean_object* v_lintDriverArgs_4454_; lean_object* v_version_4455_; lean_object* v_versionTags_4456_; lean_object* v_description_4457_; lean_object* v_keywords_4458_; lean_object* v_homepage_4459_; lean_object* v_license_4460_; lean_object* v_licenseFiles_4461_; lean_object* v_readmeFile_4462_; uint8_t v_reservoir_4463_; lean_object* v_enableArtifactCache_x3f_4464_; lean_object* v_restoreAllArtifacts_x3f_4465_; uint8_t v_libPrefixOnWindows_4466_; uint8_t v_allowImportAll_4467_; lean_object* v_builtinLint_x3f_4468_; lean_object* v_checks_4469_; uint8_t v_fixedToolchain_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4478_; 
v_toWorkspaceConfig_4436_ = lean_ctor_get(v_cfg_4435_, 0);
v_toLeanConfig_4437_ = lean_ctor_get(v_cfg_4435_, 1);
v_bootstrap_4438_ = lean_ctor_get_uint8(v_cfg_4435_, sizeof(void*)*28);
v_extraDepTargets_4439_ = lean_ctor_get(v_cfg_4435_, 2);
v_precompileModules_4440_ = lean_ctor_get_uint8(v_cfg_4435_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4441_ = lean_ctor_get(v_cfg_4435_, 3);
v_srcDir_4442_ = lean_ctor_get(v_cfg_4435_, 4);
v_buildDir_4443_ = lean_ctor_get(v_cfg_4435_, 5);
v_leanLibDir_4444_ = lean_ctor_get(v_cfg_4435_, 6);
v_nativeLibDir_4445_ = lean_ctor_get(v_cfg_4435_, 7);
v_binDir_4446_ = lean_ctor_get(v_cfg_4435_, 8);
v_irDir_4447_ = lean_ctor_get(v_cfg_4435_, 9);
v_releaseRepo_4448_ = lean_ctor_get(v_cfg_4435_, 10);
v_buildArchive_4449_ = lean_ctor_get(v_cfg_4435_, 11);
v_preferReleaseBuild_4450_ = lean_ctor_get_uint8(v_cfg_4435_, sizeof(void*)*28 + 2);
v_testDriver_4451_ = lean_ctor_get(v_cfg_4435_, 12);
v_testDriverArgs_4452_ = lean_ctor_get(v_cfg_4435_, 13);
v_lintDriver_4453_ = lean_ctor_get(v_cfg_4435_, 14);
v_lintDriverArgs_4454_ = lean_ctor_get(v_cfg_4435_, 15);
v_version_4455_ = lean_ctor_get(v_cfg_4435_, 16);
v_versionTags_4456_ = lean_ctor_get(v_cfg_4435_, 17);
v_description_4457_ = lean_ctor_get(v_cfg_4435_, 18);
v_keywords_4458_ = lean_ctor_get(v_cfg_4435_, 19);
v_homepage_4459_ = lean_ctor_get(v_cfg_4435_, 20);
v_license_4460_ = lean_ctor_get(v_cfg_4435_, 21);
v_licenseFiles_4461_ = lean_ctor_get(v_cfg_4435_, 22);
v_readmeFile_4462_ = lean_ctor_get(v_cfg_4435_, 23);
v_reservoir_4463_ = lean_ctor_get_uint8(v_cfg_4435_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4464_ = lean_ctor_get(v_cfg_4435_, 24);
v_restoreAllArtifacts_x3f_4465_ = lean_ctor_get(v_cfg_4435_, 25);
v_libPrefixOnWindows_4466_ = lean_ctor_get_uint8(v_cfg_4435_, sizeof(void*)*28 + 4);
v_allowImportAll_4467_ = lean_ctor_get_uint8(v_cfg_4435_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4468_ = lean_ctor_get(v_cfg_4435_, 26);
v_checks_4469_ = lean_ctor_get(v_cfg_4435_, 27);
v_fixedToolchain_4470_ = lean_ctor_get_uint8(v_cfg_4435_, sizeof(void*)*28 + 6);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_cfg_4435_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4472_ = v_cfg_4435_;
v_isShared_4473_ = v_isSharedCheck_4478_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_checks_4469_);
lean_inc(v_builtinLint_x3f_4468_);
lean_inc(v_restoreAllArtifacts_x3f_4465_);
lean_inc(v_enableArtifactCache_x3f_4464_);
lean_inc(v_readmeFile_4462_);
lean_inc(v_licenseFiles_4461_);
lean_inc(v_license_4460_);
lean_inc(v_homepage_4459_);
lean_inc(v_keywords_4458_);
lean_inc(v_description_4457_);
lean_inc(v_versionTags_4456_);
lean_inc(v_version_4455_);
lean_inc(v_lintDriverArgs_4454_);
lean_inc(v_lintDriver_4453_);
lean_inc(v_testDriverArgs_4452_);
lean_inc(v_testDriver_4451_);
lean_inc(v_buildArchive_4449_);
lean_inc(v_releaseRepo_4448_);
lean_inc(v_irDir_4447_);
lean_inc(v_binDir_4446_);
lean_inc(v_nativeLibDir_4445_);
lean_inc(v_leanLibDir_4444_);
lean_inc(v_buildDir_4443_);
lean_inc(v_srcDir_4442_);
lean_inc(v_moreGlobalServerArgs_4441_);
lean_inc(v_extraDepTargets_4439_);
lean_inc(v_toLeanConfig_4437_);
lean_inc(v_toWorkspaceConfig_4436_);
lean_dec(v_cfg_4435_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4478_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4474_; lean_object* v___x_4476_; 
v___x_4474_ = lean_apply_1(v_f_4434_, v_toWorkspaceConfig_4436_);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 0, v___x_4474_);
v___x_4476_ = v___x_4472_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4474_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_toLeanConfig_4437_);
lean_ctor_set(v_reuseFailAlloc_4477_, 2, v_extraDepTargets_4439_);
lean_ctor_set(v_reuseFailAlloc_4477_, 3, v_moreGlobalServerArgs_4441_);
lean_ctor_set(v_reuseFailAlloc_4477_, 4, v_srcDir_4442_);
lean_ctor_set(v_reuseFailAlloc_4477_, 5, v_buildDir_4443_);
lean_ctor_set(v_reuseFailAlloc_4477_, 6, v_leanLibDir_4444_);
lean_ctor_set(v_reuseFailAlloc_4477_, 7, v_nativeLibDir_4445_);
lean_ctor_set(v_reuseFailAlloc_4477_, 8, v_binDir_4446_);
lean_ctor_set(v_reuseFailAlloc_4477_, 9, v_irDir_4447_);
lean_ctor_set(v_reuseFailAlloc_4477_, 10, v_releaseRepo_4448_);
lean_ctor_set(v_reuseFailAlloc_4477_, 11, v_buildArchive_4449_);
lean_ctor_set(v_reuseFailAlloc_4477_, 12, v_testDriver_4451_);
lean_ctor_set(v_reuseFailAlloc_4477_, 13, v_testDriverArgs_4452_);
lean_ctor_set(v_reuseFailAlloc_4477_, 14, v_lintDriver_4453_);
lean_ctor_set(v_reuseFailAlloc_4477_, 15, v_lintDriverArgs_4454_);
lean_ctor_set(v_reuseFailAlloc_4477_, 16, v_version_4455_);
lean_ctor_set(v_reuseFailAlloc_4477_, 17, v_versionTags_4456_);
lean_ctor_set(v_reuseFailAlloc_4477_, 18, v_description_4457_);
lean_ctor_set(v_reuseFailAlloc_4477_, 19, v_keywords_4458_);
lean_ctor_set(v_reuseFailAlloc_4477_, 20, v_homepage_4459_);
lean_ctor_set(v_reuseFailAlloc_4477_, 21, v_license_4460_);
lean_ctor_set(v_reuseFailAlloc_4477_, 22, v_licenseFiles_4461_);
lean_ctor_set(v_reuseFailAlloc_4477_, 23, v_readmeFile_4462_);
lean_ctor_set(v_reuseFailAlloc_4477_, 24, v_enableArtifactCache_x3f_4464_);
lean_ctor_set(v_reuseFailAlloc_4477_, 25, v_restoreAllArtifacts_x3f_4465_);
lean_ctor_set(v_reuseFailAlloc_4477_, 26, v_builtinLint_x3f_4468_);
lean_ctor_set(v_reuseFailAlloc_4477_, 27, v_checks_4469_);
lean_ctor_set_uint8(v_reuseFailAlloc_4477_, sizeof(void*)*28, v_bootstrap_4438_);
lean_ctor_set_uint8(v_reuseFailAlloc_4477_, sizeof(void*)*28 + 1, v_precompileModules_4440_);
lean_ctor_set_uint8(v_reuseFailAlloc_4477_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4450_);
lean_ctor_set_uint8(v_reuseFailAlloc_4477_, sizeof(void*)*28 + 3, v_reservoir_4463_);
lean_ctor_set_uint8(v_reuseFailAlloc_4477_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4466_);
lean_ctor_set_uint8(v_reuseFailAlloc_4477_, sizeof(void*)*28 + 5, v_allowImportAll_4467_);
lean_ctor_set_uint8(v_reuseFailAlloc_4477_, sizeof(void*)*28 + 6, v_fixedToolchain_4470_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3(lean_object* v_x_4479_){
_start:
{
lean_object* v___x_4480_; 
v___x_4480_ = l_Lake_defaultPackagesDir;
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3___boxed(lean_object* v_x_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3(v_x_4481_);
lean_dec_ref(v_x_4481_);
return v_res_4482_;
}
}
lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg(){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = ((lean_object*)(l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__4));
return v___x_4493_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4494_;
v_res_4494_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg();
stack->m_obj
 = v_res_4494_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___boxed(lean_object* v___dummy_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg();
return v_res_4496_;
}
}
static lean_object* _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0(void){
_start:
{
lean_object* v___x_4497_; 
v___x_4497_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg();
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object* v_p_4498_, lean_object* v_n_4499_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = lean_obj_once(&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0, &l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object* v_p_4501_, lean_object* v_n_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_4501_, v_n_4502_);
lean_dec(v_n_4502_);
lean_dec(v_p_4501_);
return v_res_4503_;
}
}
lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg(){
_start:
{
lean_object* v___x_4505_; 
v___x_4505_ = lean_obj_once(&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0, &l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0);
return v___x_4505_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4506_;
v_res_4506_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg();
stack->m_obj
 = v_res_4506_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg___boxed(lean_object* v___dummy_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg();
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object* v_p_4509_, lean_object* v_n_4510_){
_start:
{
lean_object* v___x_4511_; 
v___x_4511_ = lean_obj_once(&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0, &l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object* v_p_4512_, lean_object* v_n_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(v_p_4512_, v_n_4513_);
lean_dec(v_n_4513_);
lean_dec(v_p_4512_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0(lean_object* v_cfg_4515_){
_start:
{
lean_object* v_toLeanConfig_4516_; 
v_toLeanConfig_4516_ = lean_ctor_get(v_cfg_4515_, 1);
lean_inc_ref(v_toLeanConfig_4516_);
return v_toLeanConfig_4516_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0___boxed(lean_object* v_cfg_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0(v_cfg_4517_);
lean_dec_ref(v_cfg_4517_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__1(lean_object* v_val_4519_, lean_object* v_cfg_4520_){
_start:
{
lean_object* v_toWorkspaceConfig_4521_; uint8_t v_bootstrap_4522_; lean_object* v_extraDepTargets_4523_; uint8_t v_precompileModules_4524_; lean_object* v_moreGlobalServerArgs_4525_; lean_object* v_srcDir_4526_; lean_object* v_buildDir_4527_; lean_object* v_leanLibDir_4528_; lean_object* v_nativeLibDir_4529_; lean_object* v_binDir_4530_; lean_object* v_irDir_4531_; lean_object* v_releaseRepo_4532_; lean_object* v_buildArchive_4533_; uint8_t v_preferReleaseBuild_4534_; lean_object* v_testDriver_4535_; lean_object* v_testDriverArgs_4536_; lean_object* v_lintDriver_4537_; lean_object* v_lintDriverArgs_4538_; lean_object* v_version_4539_; lean_object* v_versionTags_4540_; lean_object* v_description_4541_; lean_object* v_keywords_4542_; lean_object* v_homepage_4543_; lean_object* v_license_4544_; lean_object* v_licenseFiles_4545_; lean_object* v_readmeFile_4546_; uint8_t v_reservoir_4547_; lean_object* v_enableArtifactCache_x3f_4548_; lean_object* v_restoreAllArtifacts_x3f_4549_; uint8_t v_libPrefixOnWindows_4550_; uint8_t v_allowImportAll_4551_; lean_object* v_builtinLint_x3f_4552_; lean_object* v_checks_4553_; uint8_t v_fixedToolchain_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
v_toWorkspaceConfig_4521_ = lean_ctor_get(v_cfg_4520_, 0);
v_bootstrap_4522_ = lean_ctor_get_uint8(v_cfg_4520_, sizeof(void*)*28);
v_extraDepTargets_4523_ = lean_ctor_get(v_cfg_4520_, 2);
v_precompileModules_4524_ = lean_ctor_get_uint8(v_cfg_4520_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4525_ = lean_ctor_get(v_cfg_4520_, 3);
v_srcDir_4526_ = lean_ctor_get(v_cfg_4520_, 4);
v_buildDir_4527_ = lean_ctor_get(v_cfg_4520_, 5);
v_leanLibDir_4528_ = lean_ctor_get(v_cfg_4520_, 6);
v_nativeLibDir_4529_ = lean_ctor_get(v_cfg_4520_, 7);
v_binDir_4530_ = lean_ctor_get(v_cfg_4520_, 8);
v_irDir_4531_ = lean_ctor_get(v_cfg_4520_, 9);
v_releaseRepo_4532_ = lean_ctor_get(v_cfg_4520_, 10);
v_buildArchive_4533_ = lean_ctor_get(v_cfg_4520_, 11);
v_preferReleaseBuild_4534_ = lean_ctor_get_uint8(v_cfg_4520_, sizeof(void*)*28 + 2);
v_testDriver_4535_ = lean_ctor_get(v_cfg_4520_, 12);
v_testDriverArgs_4536_ = lean_ctor_get(v_cfg_4520_, 13);
v_lintDriver_4537_ = lean_ctor_get(v_cfg_4520_, 14);
v_lintDriverArgs_4538_ = lean_ctor_get(v_cfg_4520_, 15);
v_version_4539_ = lean_ctor_get(v_cfg_4520_, 16);
v_versionTags_4540_ = lean_ctor_get(v_cfg_4520_, 17);
v_description_4541_ = lean_ctor_get(v_cfg_4520_, 18);
v_keywords_4542_ = lean_ctor_get(v_cfg_4520_, 19);
v_homepage_4543_ = lean_ctor_get(v_cfg_4520_, 20);
v_license_4544_ = lean_ctor_get(v_cfg_4520_, 21);
v_licenseFiles_4545_ = lean_ctor_get(v_cfg_4520_, 22);
v_readmeFile_4546_ = lean_ctor_get(v_cfg_4520_, 23);
v_reservoir_4547_ = lean_ctor_get_uint8(v_cfg_4520_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4548_ = lean_ctor_get(v_cfg_4520_, 24);
v_restoreAllArtifacts_x3f_4549_ = lean_ctor_get(v_cfg_4520_, 25);
v_libPrefixOnWindows_4550_ = lean_ctor_get_uint8(v_cfg_4520_, sizeof(void*)*28 + 4);
v_allowImportAll_4551_ = lean_ctor_get_uint8(v_cfg_4520_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4552_ = lean_ctor_get(v_cfg_4520_, 26);
v_checks_4553_ = lean_ctor_get(v_cfg_4520_, 27);
v_fixedToolchain_4554_ = lean_ctor_get_uint8(v_cfg_4520_, sizeof(void*)*28 + 6);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_cfg_4520_);
if (v_isSharedCheck_4561_ == 0)
{
lean_object* v_unused_4562_; 
v_unused_4562_ = lean_ctor_get(v_cfg_4520_, 1);
lean_dec(v_unused_4562_);
v___x_4556_ = v_cfg_4520_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_checks_4553_);
lean_inc(v_builtinLint_x3f_4552_);
lean_inc(v_restoreAllArtifacts_x3f_4549_);
lean_inc(v_enableArtifactCache_x3f_4548_);
lean_inc(v_readmeFile_4546_);
lean_inc(v_licenseFiles_4545_);
lean_inc(v_license_4544_);
lean_inc(v_homepage_4543_);
lean_inc(v_keywords_4542_);
lean_inc(v_description_4541_);
lean_inc(v_versionTags_4540_);
lean_inc(v_version_4539_);
lean_inc(v_lintDriverArgs_4538_);
lean_inc(v_lintDriver_4537_);
lean_inc(v_testDriverArgs_4536_);
lean_inc(v_testDriver_4535_);
lean_inc(v_buildArchive_4533_);
lean_inc(v_releaseRepo_4532_);
lean_inc(v_irDir_4531_);
lean_inc(v_binDir_4530_);
lean_inc(v_nativeLibDir_4529_);
lean_inc(v_leanLibDir_4528_);
lean_inc(v_buildDir_4527_);
lean_inc(v_srcDir_4526_);
lean_inc(v_moreGlobalServerArgs_4525_);
lean_inc(v_extraDepTargets_4523_);
lean_inc(v_toWorkspaceConfig_4521_);
lean_dec(v_cfg_4520_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 1, v_val_4519_);
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_toWorkspaceConfig_4521_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v_val_4519_);
lean_ctor_set(v_reuseFailAlloc_4560_, 2, v_extraDepTargets_4523_);
lean_ctor_set(v_reuseFailAlloc_4560_, 3, v_moreGlobalServerArgs_4525_);
lean_ctor_set(v_reuseFailAlloc_4560_, 4, v_srcDir_4526_);
lean_ctor_set(v_reuseFailAlloc_4560_, 5, v_buildDir_4527_);
lean_ctor_set(v_reuseFailAlloc_4560_, 6, v_leanLibDir_4528_);
lean_ctor_set(v_reuseFailAlloc_4560_, 7, v_nativeLibDir_4529_);
lean_ctor_set(v_reuseFailAlloc_4560_, 8, v_binDir_4530_);
lean_ctor_set(v_reuseFailAlloc_4560_, 9, v_irDir_4531_);
lean_ctor_set(v_reuseFailAlloc_4560_, 10, v_releaseRepo_4532_);
lean_ctor_set(v_reuseFailAlloc_4560_, 11, v_buildArchive_4533_);
lean_ctor_set(v_reuseFailAlloc_4560_, 12, v_testDriver_4535_);
lean_ctor_set(v_reuseFailAlloc_4560_, 13, v_testDriverArgs_4536_);
lean_ctor_set(v_reuseFailAlloc_4560_, 14, v_lintDriver_4537_);
lean_ctor_set(v_reuseFailAlloc_4560_, 15, v_lintDriverArgs_4538_);
lean_ctor_set(v_reuseFailAlloc_4560_, 16, v_version_4539_);
lean_ctor_set(v_reuseFailAlloc_4560_, 17, v_versionTags_4540_);
lean_ctor_set(v_reuseFailAlloc_4560_, 18, v_description_4541_);
lean_ctor_set(v_reuseFailAlloc_4560_, 19, v_keywords_4542_);
lean_ctor_set(v_reuseFailAlloc_4560_, 20, v_homepage_4543_);
lean_ctor_set(v_reuseFailAlloc_4560_, 21, v_license_4544_);
lean_ctor_set(v_reuseFailAlloc_4560_, 22, v_licenseFiles_4545_);
lean_ctor_set(v_reuseFailAlloc_4560_, 23, v_readmeFile_4546_);
lean_ctor_set(v_reuseFailAlloc_4560_, 24, v_enableArtifactCache_x3f_4548_);
lean_ctor_set(v_reuseFailAlloc_4560_, 25, v_restoreAllArtifacts_x3f_4549_);
lean_ctor_set(v_reuseFailAlloc_4560_, 26, v_builtinLint_x3f_4552_);
lean_ctor_set(v_reuseFailAlloc_4560_, 27, v_checks_4553_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*28, v_bootstrap_4522_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*28 + 1, v_precompileModules_4524_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4534_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*28 + 3, v_reservoir_4547_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4550_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*28 + 5, v_allowImportAll_4551_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*28 + 6, v_fixedToolchain_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__2(lean_object* v_f_4563_, lean_object* v_cfg_4564_){
_start:
{
lean_object* v_toWorkspaceConfig_4565_; lean_object* v_toLeanConfig_4566_; uint8_t v_bootstrap_4567_; lean_object* v_extraDepTargets_4568_; uint8_t v_precompileModules_4569_; lean_object* v_moreGlobalServerArgs_4570_; lean_object* v_srcDir_4571_; lean_object* v_buildDir_4572_; lean_object* v_leanLibDir_4573_; lean_object* v_nativeLibDir_4574_; lean_object* v_binDir_4575_; lean_object* v_irDir_4576_; lean_object* v_releaseRepo_4577_; lean_object* v_buildArchive_4578_; uint8_t v_preferReleaseBuild_4579_; lean_object* v_testDriver_4580_; lean_object* v_testDriverArgs_4581_; lean_object* v_lintDriver_4582_; lean_object* v_lintDriverArgs_4583_; lean_object* v_version_4584_; lean_object* v_versionTags_4585_; lean_object* v_description_4586_; lean_object* v_keywords_4587_; lean_object* v_homepage_4588_; lean_object* v_license_4589_; lean_object* v_licenseFiles_4590_; lean_object* v_readmeFile_4591_; uint8_t v_reservoir_4592_; lean_object* v_enableArtifactCache_x3f_4593_; lean_object* v_restoreAllArtifacts_x3f_4594_; uint8_t v_libPrefixOnWindows_4595_; uint8_t v_allowImportAll_4596_; lean_object* v_builtinLint_x3f_4597_; lean_object* v_checks_4598_; uint8_t v_fixedToolchain_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4607_; 
v_toWorkspaceConfig_4565_ = lean_ctor_get(v_cfg_4564_, 0);
v_toLeanConfig_4566_ = lean_ctor_get(v_cfg_4564_, 1);
v_bootstrap_4567_ = lean_ctor_get_uint8(v_cfg_4564_, sizeof(void*)*28);
v_extraDepTargets_4568_ = lean_ctor_get(v_cfg_4564_, 2);
v_precompileModules_4569_ = lean_ctor_get_uint8(v_cfg_4564_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4570_ = lean_ctor_get(v_cfg_4564_, 3);
v_srcDir_4571_ = lean_ctor_get(v_cfg_4564_, 4);
v_buildDir_4572_ = lean_ctor_get(v_cfg_4564_, 5);
v_leanLibDir_4573_ = lean_ctor_get(v_cfg_4564_, 6);
v_nativeLibDir_4574_ = lean_ctor_get(v_cfg_4564_, 7);
v_binDir_4575_ = lean_ctor_get(v_cfg_4564_, 8);
v_irDir_4576_ = lean_ctor_get(v_cfg_4564_, 9);
v_releaseRepo_4577_ = lean_ctor_get(v_cfg_4564_, 10);
v_buildArchive_4578_ = lean_ctor_get(v_cfg_4564_, 11);
v_preferReleaseBuild_4579_ = lean_ctor_get_uint8(v_cfg_4564_, sizeof(void*)*28 + 2);
v_testDriver_4580_ = lean_ctor_get(v_cfg_4564_, 12);
v_testDriverArgs_4581_ = lean_ctor_get(v_cfg_4564_, 13);
v_lintDriver_4582_ = lean_ctor_get(v_cfg_4564_, 14);
v_lintDriverArgs_4583_ = lean_ctor_get(v_cfg_4564_, 15);
v_version_4584_ = lean_ctor_get(v_cfg_4564_, 16);
v_versionTags_4585_ = lean_ctor_get(v_cfg_4564_, 17);
v_description_4586_ = lean_ctor_get(v_cfg_4564_, 18);
v_keywords_4587_ = lean_ctor_get(v_cfg_4564_, 19);
v_homepage_4588_ = lean_ctor_get(v_cfg_4564_, 20);
v_license_4589_ = lean_ctor_get(v_cfg_4564_, 21);
v_licenseFiles_4590_ = lean_ctor_get(v_cfg_4564_, 22);
v_readmeFile_4591_ = lean_ctor_get(v_cfg_4564_, 23);
v_reservoir_4592_ = lean_ctor_get_uint8(v_cfg_4564_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4593_ = lean_ctor_get(v_cfg_4564_, 24);
v_restoreAllArtifacts_x3f_4594_ = lean_ctor_get(v_cfg_4564_, 25);
v_libPrefixOnWindows_4595_ = lean_ctor_get_uint8(v_cfg_4564_, sizeof(void*)*28 + 4);
v_allowImportAll_4596_ = lean_ctor_get_uint8(v_cfg_4564_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4597_ = lean_ctor_get(v_cfg_4564_, 26);
v_checks_4598_ = lean_ctor_get(v_cfg_4564_, 27);
v_fixedToolchain_4599_ = lean_ctor_get_uint8(v_cfg_4564_, sizeof(void*)*28 + 6);
v_isSharedCheck_4607_ = !lean_is_exclusive(v_cfg_4564_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4601_ = v_cfg_4564_;
v_isShared_4602_ = v_isSharedCheck_4607_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_checks_4598_);
lean_inc(v_builtinLint_x3f_4597_);
lean_inc(v_restoreAllArtifacts_x3f_4594_);
lean_inc(v_enableArtifactCache_x3f_4593_);
lean_inc(v_readmeFile_4591_);
lean_inc(v_licenseFiles_4590_);
lean_inc(v_license_4589_);
lean_inc(v_homepage_4588_);
lean_inc(v_keywords_4587_);
lean_inc(v_description_4586_);
lean_inc(v_versionTags_4585_);
lean_inc(v_version_4584_);
lean_inc(v_lintDriverArgs_4583_);
lean_inc(v_lintDriver_4582_);
lean_inc(v_testDriverArgs_4581_);
lean_inc(v_testDriver_4580_);
lean_inc(v_buildArchive_4578_);
lean_inc(v_releaseRepo_4577_);
lean_inc(v_irDir_4576_);
lean_inc(v_binDir_4575_);
lean_inc(v_nativeLibDir_4574_);
lean_inc(v_leanLibDir_4573_);
lean_inc(v_buildDir_4572_);
lean_inc(v_srcDir_4571_);
lean_inc(v_moreGlobalServerArgs_4570_);
lean_inc(v_extraDepTargets_4568_);
lean_inc(v_toLeanConfig_4566_);
lean_inc(v_toWorkspaceConfig_4565_);
lean_dec(v_cfg_4564_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4607_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4603_ = lean_apply_1(v_f_4563_, v_toLeanConfig_4566_);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 1, v___x_4603_);
v___x_4605_ = v___x_4601_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_toWorkspaceConfig_4565_);
lean_ctor_set(v_reuseFailAlloc_4606_, 1, v___x_4603_);
lean_ctor_set(v_reuseFailAlloc_4606_, 2, v_extraDepTargets_4568_);
lean_ctor_set(v_reuseFailAlloc_4606_, 3, v_moreGlobalServerArgs_4570_);
lean_ctor_set(v_reuseFailAlloc_4606_, 4, v_srcDir_4571_);
lean_ctor_set(v_reuseFailAlloc_4606_, 5, v_buildDir_4572_);
lean_ctor_set(v_reuseFailAlloc_4606_, 6, v_leanLibDir_4573_);
lean_ctor_set(v_reuseFailAlloc_4606_, 7, v_nativeLibDir_4574_);
lean_ctor_set(v_reuseFailAlloc_4606_, 8, v_binDir_4575_);
lean_ctor_set(v_reuseFailAlloc_4606_, 9, v_irDir_4576_);
lean_ctor_set(v_reuseFailAlloc_4606_, 10, v_releaseRepo_4577_);
lean_ctor_set(v_reuseFailAlloc_4606_, 11, v_buildArchive_4578_);
lean_ctor_set(v_reuseFailAlloc_4606_, 12, v_testDriver_4580_);
lean_ctor_set(v_reuseFailAlloc_4606_, 13, v_testDriverArgs_4581_);
lean_ctor_set(v_reuseFailAlloc_4606_, 14, v_lintDriver_4582_);
lean_ctor_set(v_reuseFailAlloc_4606_, 15, v_lintDriverArgs_4583_);
lean_ctor_set(v_reuseFailAlloc_4606_, 16, v_version_4584_);
lean_ctor_set(v_reuseFailAlloc_4606_, 17, v_versionTags_4585_);
lean_ctor_set(v_reuseFailAlloc_4606_, 18, v_description_4586_);
lean_ctor_set(v_reuseFailAlloc_4606_, 19, v_keywords_4587_);
lean_ctor_set(v_reuseFailAlloc_4606_, 20, v_homepage_4588_);
lean_ctor_set(v_reuseFailAlloc_4606_, 21, v_license_4589_);
lean_ctor_set(v_reuseFailAlloc_4606_, 22, v_licenseFiles_4590_);
lean_ctor_set(v_reuseFailAlloc_4606_, 23, v_readmeFile_4591_);
lean_ctor_set(v_reuseFailAlloc_4606_, 24, v_enableArtifactCache_x3f_4593_);
lean_ctor_set(v_reuseFailAlloc_4606_, 25, v_restoreAllArtifacts_x3f_4594_);
lean_ctor_set(v_reuseFailAlloc_4606_, 26, v_builtinLint_x3f_4597_);
lean_ctor_set(v_reuseFailAlloc_4606_, 27, v_checks_4598_);
lean_ctor_set_uint8(v_reuseFailAlloc_4606_, sizeof(void*)*28, v_bootstrap_4567_);
lean_ctor_set_uint8(v_reuseFailAlloc_4606_, sizeof(void*)*28 + 1, v_precompileModules_4569_);
lean_ctor_set_uint8(v_reuseFailAlloc_4606_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4579_);
lean_ctor_set_uint8(v_reuseFailAlloc_4606_, sizeof(void*)*28 + 3, v_reservoir_4592_);
lean_ctor_set_uint8(v_reuseFailAlloc_4606_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4595_);
lean_ctor_set_uint8(v_reuseFailAlloc_4606_, sizeof(void*)*28 + 5, v_allowImportAll_4596_);
lean_ctor_set_uint8(v_reuseFailAlloc_4606_, sizeof(void*)*28 + 6, v_fixedToolchain_4599_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3(lean_object* v_x_4616_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__1));
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___boxed(lean_object* v_x_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3(v_x_4618_);
lean_dec_ref(v_x_4618_);
return v_res_4619_;
}
}
lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg(){
_start:
{
lean_object* v___x_4630_; 
v___x_4630_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__4));
return v___x_4630_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_toLeanConfig___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4631_;
v_res_4631_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg();
stack->m_obj
 = v_res_4631_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___boxed(lean_object* v___dummy_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg();
return v_res_4633_;
}
}
static lean_object* _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0(void){
_start:
{
lean_object* v___x_4634_; 
v___x_4634_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg();
return v___x_4634_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object* v_p_4635_, lean_object* v_n_4636_){
_start:
{
lean_object* v___x_4637_; 
v___x_4637_ = lean_obj_once(&l_Lake_PackageConfig_toLeanConfig___proj___closed__0, &l_Lake_PackageConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___boxed(lean_object* v_p_4638_, lean_object* v_n_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_4638_, v_n_4639_);
lean_dec(v_n_4639_);
lean_dec(v_p_4638_);
return v_res_4640_;
}
}
lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg(){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = lean_obj_once(&l_Lake_PackageConfig_toLeanConfig___proj___closed__0, &l_Lake_PackageConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0);
return v___x_4642_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4643_;
v_res_4643_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg();
stack->m_obj
 = v_res_4643_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg___boxed(lean_object* v___dummy_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg();
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent(lean_object* v_p_4646_, lean_object* v_n_4647_){
_start:
{
lean_object* v___x_4648_; 
v___x_4648_ = lean_obj_once(&l_Lake_PackageConfig_toLeanConfig___proj___closed__0, &l_Lake_PackageConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_p_4649_, lean_object* v_n_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent(v_p_4649_, v_n_4650_);
lean_dec(v_n_4650_);
lean_dec(v_p_4649_);
return v_res_4651_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4661_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__3));
v___x_4662_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__0));
v___x_4663_ = lean_array_push(v___x_4662_, v___x_4661_);
return v___x_4663_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4671_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__7));
v___x_4672_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__4, &l_Lake_PackageConfig___fields___closed__4_once, _init_l_Lake_PackageConfig___fields___closed__4);
v___x_4673_ = lean_array_push(v___x_4672_, v___x_4671_);
return v___x_4673_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4681_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__11));
v___x_4682_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__8, &l_Lake_PackageConfig___fields___closed__8_once, _init_l_Lake_PackageConfig___fields___closed__8);
v___x_4683_ = lean_array_push(v___x_4682_, v___x_4681_);
return v___x_4683_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4691_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__15));
v___x_4692_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__12, &l_Lake_PackageConfig___fields___closed__12_once, _init_l_Lake_PackageConfig___fields___closed__12);
v___x_4693_ = lean_array_push(v___x_4692_, v___x_4691_);
return v___x_4693_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; 
v___x_4701_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__19));
v___x_4702_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__16, &l_Lake_PackageConfig___fields___closed__16_once, _init_l_Lake_PackageConfig___fields___closed__16);
v___x_4703_ = lean_array_push(v___x_4702_, v___x_4701_);
return v___x_4703_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4711_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__23));
v___x_4712_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__20, &l_Lake_PackageConfig___fields___closed__20_once, _init_l_Lake_PackageConfig___fields___closed__20);
v___x_4713_ = lean_array_push(v___x_4712_, v___x_4711_);
return v___x_4713_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4721_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__27));
v___x_4722_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__24, &l_Lake_PackageConfig___fields___closed__24_once, _init_l_Lake_PackageConfig___fields___closed__24);
v___x_4723_ = lean_array_push(v___x_4722_, v___x_4721_);
return v___x_4723_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4731_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__31));
v___x_4732_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__28, &l_Lake_PackageConfig___fields___closed__28_once, _init_l_Lake_PackageConfig___fields___closed__28);
v___x_4733_ = lean_array_push(v___x_4732_, v___x_4731_);
return v___x_4733_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4741_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__35));
v___x_4742_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__32, &l_Lake_PackageConfig___fields___closed__32_once, _init_l_Lake_PackageConfig___fields___closed__32);
v___x_4743_ = lean_array_push(v___x_4742_, v___x_4741_);
return v___x_4743_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4751_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__39));
v___x_4752_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__36, &l_Lake_PackageConfig___fields___closed__36_once, _init_l_Lake_PackageConfig___fields___closed__36);
v___x_4753_ = lean_array_push(v___x_4752_, v___x_4751_);
return v___x_4753_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4761_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__43));
v___x_4762_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__40, &l_Lake_PackageConfig___fields___closed__40_once, _init_l_Lake_PackageConfig___fields___closed__40);
v___x_4763_ = lean_array_push(v___x_4762_, v___x_4761_);
return v___x_4763_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4771_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__47));
v___x_4772_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__44, &l_Lake_PackageConfig___fields___closed__44_once, _init_l_Lake_PackageConfig___fields___closed__44);
v___x_4773_ = lean_array_push(v___x_4772_, v___x_4771_);
return v___x_4773_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__52(void){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4781_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__51));
v___x_4782_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__48, &l_Lake_PackageConfig___fields___closed__48_once, _init_l_Lake_PackageConfig___fields___closed__48);
v___x_4783_ = lean_array_push(v___x_4782_, v___x_4781_);
return v___x_4783_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__56(void){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4791_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__55));
v___x_4792_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__52, &l_Lake_PackageConfig___fields___closed__52_once, _init_l_Lake_PackageConfig___fields___closed__52);
v___x_4793_ = lean_array_push(v___x_4792_, v___x_4791_);
return v___x_4793_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__60(void){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4801_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__59));
v___x_4802_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__56, &l_Lake_PackageConfig___fields___closed__56_once, _init_l_Lake_PackageConfig___fields___closed__56);
v___x_4803_ = lean_array_push(v___x_4802_, v___x_4801_);
return v___x_4803_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__64(void){
_start:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4811_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__63));
v___x_4812_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__60, &l_Lake_PackageConfig___fields___closed__60_once, _init_l_Lake_PackageConfig___fields___closed__60);
v___x_4813_ = lean_array_push(v___x_4812_, v___x_4811_);
return v___x_4813_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__68(void){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4821_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__67));
v___x_4822_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__64, &l_Lake_PackageConfig___fields___closed__64_once, _init_l_Lake_PackageConfig___fields___closed__64);
v___x_4823_ = lean_array_push(v___x_4822_, v___x_4821_);
return v___x_4823_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__72(void){
_start:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4831_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__71));
v___x_4832_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__68, &l_Lake_PackageConfig___fields___closed__68_once, _init_l_Lake_PackageConfig___fields___closed__68);
v___x_4833_ = lean_array_push(v___x_4832_, v___x_4831_);
return v___x_4833_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__76(void){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4841_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__75));
v___x_4842_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__72, &l_Lake_PackageConfig___fields___closed__72_once, _init_l_Lake_PackageConfig___fields___closed__72);
v___x_4843_ = lean_array_push(v___x_4842_, v___x_4841_);
return v___x_4843_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__80(void){
_start:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4851_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__79));
v___x_4852_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__76, &l_Lake_PackageConfig___fields___closed__76_once, _init_l_Lake_PackageConfig___fields___closed__76);
v___x_4853_ = lean_array_push(v___x_4852_, v___x_4851_);
return v___x_4853_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__84(void){
_start:
{
lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4861_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__83));
v___x_4862_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__80, &l_Lake_PackageConfig___fields___closed__80_once, _init_l_Lake_PackageConfig___fields___closed__80);
v___x_4863_ = lean_array_push(v___x_4862_, v___x_4861_);
return v___x_4863_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__88(void){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4871_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__87));
v___x_4872_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__84, &l_Lake_PackageConfig___fields___closed__84_once, _init_l_Lake_PackageConfig___fields___closed__84);
v___x_4873_ = lean_array_push(v___x_4872_, v___x_4871_);
return v___x_4873_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__92(void){
_start:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4881_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__91));
v___x_4882_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__88, &l_Lake_PackageConfig___fields___closed__88_once, _init_l_Lake_PackageConfig___fields___closed__88);
v___x_4883_ = lean_array_push(v___x_4882_, v___x_4881_);
return v___x_4883_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__96(void){
_start:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___x_4891_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__95));
v___x_4892_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__92, &l_Lake_PackageConfig___fields___closed__92_once, _init_l_Lake_PackageConfig___fields___closed__92);
v___x_4893_ = lean_array_push(v___x_4892_, v___x_4891_);
return v___x_4893_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__100(void){
_start:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4901_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__99));
v___x_4902_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__96, &l_Lake_PackageConfig___fields___closed__96_once, _init_l_Lake_PackageConfig___fields___closed__96);
v___x_4903_ = lean_array_push(v___x_4902_, v___x_4901_);
return v___x_4903_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__104(void){
_start:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4911_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__103));
v___x_4912_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__100, &l_Lake_PackageConfig___fields___closed__100_once, _init_l_Lake_PackageConfig___fields___closed__100);
v___x_4913_ = lean_array_push(v___x_4912_, v___x_4911_);
return v___x_4913_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__108(void){
_start:
{
lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v___x_4921_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__107));
v___x_4922_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__104, &l_Lake_PackageConfig___fields___closed__104_once, _init_l_Lake_PackageConfig___fields___closed__104);
v___x_4923_ = lean_array_push(v___x_4922_, v___x_4921_);
return v___x_4923_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__112(void){
_start:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4931_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__111));
v___x_4932_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__108, &l_Lake_PackageConfig___fields___closed__108_once, _init_l_Lake_PackageConfig___fields___closed__108);
v___x_4933_ = lean_array_push(v___x_4932_, v___x_4931_);
return v___x_4933_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__116(void){
_start:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4941_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__115));
v___x_4942_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__112, &l_Lake_PackageConfig___fields___closed__112_once, _init_l_Lake_PackageConfig___fields___closed__112);
v___x_4943_ = lean_array_push(v___x_4942_, v___x_4941_);
return v___x_4943_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__120(void){
_start:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4951_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__119));
v___x_4952_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__116, &l_Lake_PackageConfig___fields___closed__116_once, _init_l_Lake_PackageConfig___fields___closed__116);
v___x_4953_ = lean_array_push(v___x_4952_, v___x_4951_);
return v___x_4953_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__124(void){
_start:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4961_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__123));
v___x_4962_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__120, &l_Lake_PackageConfig___fields___closed__120_once, _init_l_Lake_PackageConfig___fields___closed__120);
v___x_4963_ = lean_array_push(v___x_4962_, v___x_4961_);
return v___x_4963_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__128(void){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4971_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__127));
v___x_4972_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__124, &l_Lake_PackageConfig___fields___closed__124_once, _init_l_Lake_PackageConfig___fields___closed__124);
v___x_4973_ = lean_array_push(v___x_4972_, v___x_4971_);
return v___x_4973_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__132(void){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4981_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__131));
v___x_4982_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__128, &l_Lake_PackageConfig___fields___closed__128_once, _init_l_Lake_PackageConfig___fields___closed__128);
v___x_4983_ = lean_array_push(v___x_4982_, v___x_4981_);
return v___x_4983_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__136(void){
_start:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4991_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__135));
v___x_4992_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__132, &l_Lake_PackageConfig___fields___closed__132_once, _init_l_Lake_PackageConfig___fields___closed__132);
v___x_4993_ = lean_array_push(v___x_4992_, v___x_4991_);
return v___x_4993_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__140(void){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5001_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__139));
v___x_5002_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__136, &l_Lake_PackageConfig___fields___closed__136_once, _init_l_Lake_PackageConfig___fields___closed__136);
v___x_5003_ = lean_array_push(v___x_5002_, v___x_5001_);
return v___x_5003_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__144(void){
_start:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5011_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__143));
v___x_5012_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__140, &l_Lake_PackageConfig___fields___closed__140_once, _init_l_Lake_PackageConfig___fields___closed__140);
v___x_5013_ = lean_array_push(v___x_5012_, v___x_5011_);
return v___x_5013_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__148(void){
_start:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___x_5021_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__147));
v___x_5022_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__144, &l_Lake_PackageConfig___fields___closed__144_once, _init_l_Lake_PackageConfig___fields___closed__144);
v___x_5023_ = lean_array_push(v___x_5022_, v___x_5021_);
return v___x_5023_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__152(void){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5031_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__151));
v___x_5032_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__148, &l_Lake_PackageConfig___fields___closed__148_once, _init_l_Lake_PackageConfig___fields___closed__148);
v___x_5033_ = lean_array_push(v___x_5032_, v___x_5031_);
return v___x_5033_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__156(void){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5041_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__155));
v___x_5042_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__152, &l_Lake_PackageConfig___fields___closed__152_once, _init_l_Lake_PackageConfig___fields___closed__152);
v___x_5043_ = lean_array_push(v___x_5042_, v___x_5041_);
return v___x_5043_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__160(void){
_start:
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5051_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__159));
v___x_5052_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__156, &l_Lake_PackageConfig___fields___closed__156_once, _init_l_Lake_PackageConfig___fields___closed__156);
v___x_5053_ = lean_array_push(v___x_5052_, v___x_5051_);
return v___x_5053_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__161(void){
_start:
{
lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5054_ = l_Lake_WorkspaceConfig___fields;
v___x_5055_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__160, &l_Lake_PackageConfig___fields___closed__160_once, _init_l_Lake_PackageConfig___fields___closed__160);
v___x_5056_ = l_Array_append___redArg(v___x_5055_, v___x_5054_);
return v___x_5056_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__165(void){
_start:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5064_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__164));
v___x_5065_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__161, &l_Lake_PackageConfig___fields___closed__161_once, _init_l_Lake_PackageConfig___fields___closed__161);
v___x_5066_ = lean_array_push(v___x_5065_, v___x_5064_);
return v___x_5066_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__166(void){
_start:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___x_5067_ = l_Lake_LeanConfig___fields;
v___x_5068_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__165, &l_Lake_PackageConfig___fields___closed__165_once, _init_l_Lake_PackageConfig___fields___closed__165);
v___x_5069_ = l_Array_append___redArg(v___x_5068_, v___x_5067_);
return v___x_5069_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__170(void){
_start:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; 
v___x_5077_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__169));
v___x_5078_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__166, &l_Lake_PackageConfig___fields___closed__166_once, _init_l_Lake_PackageConfig___fields___closed__166);
v___x_5079_ = lean_array_push(v___x_5078_, v___x_5077_);
return v___x_5079_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields(void){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__170, &l_Lake_PackageConfig___fields___closed__170_once, _init_l_Lake_PackageConfig___fields___closed__170);
return v___x_5080_;
}
}
lean_object* l_Lake_PackageConfig_instConfigFields___redArg(){
_start:
{
lean_object* v___x_5082_; 
v___x_5082_ = l_Lake_PackageConfig___fields;
return v___x_5082_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_instConfigFields___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5083_;
v_res_5083_ = l_Lake_PackageConfig_instConfigFields___redArg();
stack->m_obj
 = v_res_5083_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___redArg___boxed(lean_object* v___dummy_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lake_PackageConfig_instConfigFields___redArg();
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields(lean_object* v_p_5086_, lean_object* v_n_5087_){
_start:
{
lean_object* v___x_5088_; 
v___x_5088_ = l_Lake_PackageConfig___fields;
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___boxed(lean_object* v_p_5089_, lean_object* v_n_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l_Lake_PackageConfig_instConfigFields(v_p_5089_, v_n_5090_);
lean_dec(v_n_5090_);
lean_dec(v_p_5089_);
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo___lam__0(lean_object* v_x1_5092_, lean_object* v_x2_5093_){
_start:
{
lean_object* v_name_5094_; lean_object* v___x_5095_; 
v_name_5094_ = lean_ctor_get(v_x2_5093_, 0);
lean_inc(v_name_5094_);
v___x_5095_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5094_, v_x2_5093_, v_x1_5092_);
return v___x_5095_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5096_ = l_Lake_PackageConfig___fields;
v___x_5097_ = lean_array_get_size(v___x_5096_);
return v___x_5097_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_5117_; lean_object* v___x_5118_; uint8_t v___x_5119_; 
v___x_5117_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_5118_ = lean_unsigned_to_nat(0u);
v___x_5119_ = lean_nat_dec_lt(v___x_5118_, v___x_5117_);
return v___x_5119_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_5121_; uint8_t v___x_5122_; 
v___x_5121_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_5122_ = lean_nat_dec_le(v___x_5121_, v___x_5121_);
return v___x_5122_;
}
}
static size_t _init_l_Lake_PackageConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_5123_; size_t v___x_5124_; 
v___x_5123_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_5124_ = lean_usize_of_nat(v___x_5123_);
return v___x_5124_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_5125_; size_t v___x_5126_; size_t v___x_5127_; lean_object* v___x_5128_; lean_object* v___f_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; 
v___x_5125_ = lean_box(1);
v___x_5126_ = lean_usize_once(&l_Lake_PackageConfig_instConfigInfo___closed__14, &l_Lake_PackageConfig_instConfigInfo___closed__14_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__14);
v___x_5127_ = ((size_t)0ULL);
v___x_5128_ = l_Lake_PackageConfig___fields;
v___f_5129_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__12));
v___x_5130_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__10));
v___x_5131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5130_, v___f_5129_, v___x_5128_, v___x_5127_, v___x_5126_, v___x_5125_);
return v___x_5131_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_5132_; lean_object* v___y_5134_; lean_object* v___x_5137_; uint8_t v___x_5138_; 
v___x_5132_ = l_Lake_PackageConfig___fields;
v___x_5137_ = lean_box(1);
v___x_5138_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__11, &l_Lake_PackageConfig_instConfigInfo___closed__11_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__11);
if (v___x_5138_ == 0)
{
v___y_5134_ = v___x_5137_;
goto v___jp_5133_;
}
else
{
uint8_t v___x_5139_; 
v___x_5139_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__13, &l_Lake_PackageConfig_instConfigInfo___closed__13_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__13);
if (v___x_5139_ == 0)
{
if (v___x_5138_ == 0)
{
v___y_5134_ = v___x_5137_;
goto v___jp_5133_;
}
else
{
lean_object* v___x_5140_; 
v___x_5140_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_5134_ = v___x_5140_;
goto v___jp_5133_;
}
}
else
{
lean_object* v___x_5141_; 
v___x_5141_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_5134_ = v___x_5141_;
goto v___jp_5133_;
}
}
v___jp_5133_:
{
lean_object* v___x_5135_; lean_object* v___x_5136_; 
v___x_5135_ = lean_unsigned_to_nat(2u);
lean_inc(v___y_5134_);
v___x_5136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5136_, 0, v___x_5132_);
lean_ctor_set(v___x_5136_, 1, v___y_5134_);
lean_ctor_set(v___x_5136_, 2, v___x_5135_);
return v___x_5136_;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0(void){
_start:
{
uint8_t v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; uint8_t v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; 
v___x_5142_ = 1;
v___x_5143_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__7));
v___x_5144_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__6));
v___x_5145_ = l_Lake_defaultVersionTags;
v___x_5146_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__4));
v___x_5147_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__2));
v___x_5148_ = lean_box(0);
v___x_5149_ = l_Lake_defaultIrDir;
v___x_5150_ = l_Lake_defaultBinDir;
v___x_5151_ = l_Lake_defaultNativeLibDir;
v___x_5152_ = l_Lake_defaultLeanLibDir;
v___x_5153_ = l_Lake_defaultBuildDir;
v___x_5154_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__1));
v___x_5155_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0));
v___x_5156_ = 0;
v___x_5157_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__1));
v___x_5158_ = l_Lake_defaultPackagesDir;
v___x_5159_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v___x_5159_, 0, v___x_5158_);
lean_ctor_set(v___x_5159_, 1, v___x_5157_);
lean_ctor_set(v___x_5159_, 2, v___x_5155_);
lean_ctor_set(v___x_5159_, 3, v___x_5155_);
lean_ctor_set(v___x_5159_, 4, v___x_5154_);
lean_ctor_set(v___x_5159_, 5, v___x_5153_);
lean_ctor_set(v___x_5159_, 6, v___x_5152_);
lean_ctor_set(v___x_5159_, 7, v___x_5151_);
lean_ctor_set(v___x_5159_, 8, v___x_5150_);
lean_ctor_set(v___x_5159_, 9, v___x_5149_);
lean_ctor_set(v___x_5159_, 10, v___x_5148_);
lean_ctor_set(v___x_5159_, 11, v___x_5148_);
lean_ctor_set(v___x_5159_, 12, v___x_5147_);
lean_ctor_set(v___x_5159_, 13, v___x_5155_);
lean_ctor_set(v___x_5159_, 14, v___x_5147_);
lean_ctor_set(v___x_5159_, 15, v___x_5155_);
lean_ctor_set(v___x_5159_, 16, v___x_5146_);
lean_ctor_set(v___x_5159_, 17, v___x_5145_);
lean_ctor_set(v___x_5159_, 18, v___x_5147_);
lean_ctor_set(v___x_5159_, 19, v___x_5155_);
lean_ctor_set(v___x_5159_, 20, v___x_5147_);
lean_ctor_set(v___x_5159_, 21, v___x_5147_);
lean_ctor_set(v___x_5159_, 22, v___x_5144_);
lean_ctor_set(v___x_5159_, 23, v___x_5143_);
lean_ctor_set(v___x_5159_, 24, v___x_5148_);
lean_ctor_set(v___x_5159_, 25, v___x_5148_);
lean_ctor_set(v___x_5159_, 26, v___x_5148_);
lean_ctor_set(v___x_5159_, 27, v___x_5155_);
lean_ctor_set_uint8(v___x_5159_, sizeof(void*)*28, v___x_5156_);
lean_ctor_set_uint8(v___x_5159_, sizeof(void*)*28 + 1, v___x_5156_);
lean_ctor_set_uint8(v___x_5159_, sizeof(void*)*28 + 2, v___x_5156_);
lean_ctor_set_uint8(v___x_5159_, sizeof(void*)*28 + 3, v___x_5142_);
lean_ctor_set_uint8(v___x_5159_, sizeof(void*)*28 + 4, v___x_5156_);
lean_ctor_set_uint8(v___x_5159_, sizeof(void*)*28 + 5, v___x_5156_);
lean_ctor_set_uint8(v___x_5159_, sizeof(void*)*28 + 6, v___x_5156_);
return v___x_5159_;
}
}
lean_object* l_Lake_PackageConfig_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_5161_; 
v___x_5161_ = lean_obj_once(&l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0, &l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0_once, _init_l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0);
return v___x_5161_;
}
}
LEAN_EXPORT void l_Lake_PackageConfig_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5162_;
v_res_5162_ = l_Lake_PackageConfig_instEmptyCollection___redArg();
stack->m_obj
 = v_res_5162_;
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___redArg___boxed(lean_object* v___dummy_5163_){
_start:
{
lean_object* v_res_5164_; 
v_res_5164_ = l_Lake_PackageConfig_instEmptyCollection___redArg();
return v_res_5164_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_5165_; 
v___x_5165_ = l_Lake_PackageConfig_instEmptyCollection___redArg();
return v___x_5165_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection(lean_object* v_p_5166_, lean_object* v_n_5167_){
_start:
{
lean_object* v___x_5168_; 
v___x_5168_ = lean_obj_once(&l_Lake_PackageConfig_instEmptyCollection___closed__0, &l_Lake_PackageConfig_instEmptyCollection___closed__0_once, _init_l_Lake_PackageConfig_instEmptyCollection___closed__0);
return v___x_5168_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___boxed(lean_object* v_p_5169_, lean_object* v_n_5170_){
_start:
{
lean_object* v_res_5171_; 
v_res_5171_ = l_Lake_PackageConfig_instEmptyCollection(v_p_5169_, v_n_5170_);
lean_dec(v_n_5170_);
lean_dec(v_p_5169_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg(lean_object* v_n_5172_){
_start:
{
lean_inc(v_n_5172_);
return v_n_5172_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg___boxed(lean_object* v_n_5173_){
_start:
{
lean_object* v_res_5174_; 
v_res_5174_ = l_Lake_PackageConfig_origName___redArg(v_n_5173_);
lean_dec(v_n_5173_);
return v_res_5174_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName(lean_object* v_p_5175_, lean_object* v_n_5176_, lean_object* v_x_5177_){
_start:
{
lean_inc(v_n_5176_);
return v_n_5176_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___boxed(lean_object* v_p_5178_, lean_object* v_n_5179_, lean_object* v_x_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l_Lake_PackageConfig_origName(v_p_5178_, v_n_5179_, v_x_5180_);
lean_dec_ref(v_x_5180_);
lean_dec(v_n_5179_);
lean_dec(v_p_5178_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name(lean_object* v_self_5189_){
_start:
{
lean_object* v_keyName_5190_; 
v_keyName_5190_ = lean_ctor_get(v_self_5189_, 1);
lean_inc(v_keyName_5190_);
return v_keyName_5190_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name___boxed(lean_object* v_self_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Lake_PackageDecl_name(v_self_5191_);
lean_dec_ref(v_self_5191_);
return v_res_5192_;
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
