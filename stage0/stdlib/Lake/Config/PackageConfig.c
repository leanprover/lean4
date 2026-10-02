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
v_bootstrap_67_ = lean_ctor_get_uint8(v_cfg_66_, sizeof(void*)*28);
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
lean_object* v_toWorkspaceConfig_73_; lean_object* v_toLeanConfig_74_; lean_object* v_extraDepTargets_75_; uint8_t v_precompileModules_76_; lean_object* v_moreGlobalServerArgs_77_; lean_object* v_srcDir_78_; lean_object* v_buildDir_79_; lean_object* v_leanLibDir_80_; lean_object* v_nativeLibDir_81_; lean_object* v_binDir_82_; lean_object* v_irDir_83_; lean_object* v_releaseRepo_84_; lean_object* v_buildArchive_85_; uint8_t v_preferReleaseBuild_86_; lean_object* v_testDriver_87_; lean_object* v_testDriverArgs_88_; lean_object* v_lintDriver_89_; lean_object* v_lintDriverArgs_90_; lean_object* v_version_91_; lean_object* v_versionTags_92_; lean_object* v_description_93_; lean_object* v_keywords_94_; lean_object* v_homepage_95_; lean_object* v_license_96_; lean_object* v_licenseFiles_97_; lean_object* v_readmeFile_98_; uint8_t v_reservoir_99_; lean_object* v_enableArtifactCache_x3f_100_; lean_object* v_restoreAllArtifacts_x3f_101_; uint8_t v_libPrefixOnWindows_102_; uint8_t v_allowImportAll_103_; lean_object* v_builtinLint_x3f_104_; lean_object* v_checks_105_; uint8_t v_fixedToolchain_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
v_toWorkspaceConfig_73_ = lean_ctor_get(v_cfg_72_, 0);
v_toLeanConfig_74_ = lean_ctor_get(v_cfg_72_, 1);
v_extraDepTargets_75_ = lean_ctor_get(v_cfg_72_, 2);
v_precompileModules_76_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_77_ = lean_ctor_get(v_cfg_72_, 3);
v_srcDir_78_ = lean_ctor_get(v_cfg_72_, 4);
v_buildDir_79_ = lean_ctor_get(v_cfg_72_, 5);
v_leanLibDir_80_ = lean_ctor_get(v_cfg_72_, 6);
v_nativeLibDir_81_ = lean_ctor_get(v_cfg_72_, 7);
v_binDir_82_ = lean_ctor_get(v_cfg_72_, 8);
v_irDir_83_ = lean_ctor_get(v_cfg_72_, 9);
v_releaseRepo_84_ = lean_ctor_get(v_cfg_72_, 10);
v_buildArchive_85_ = lean_ctor_get(v_cfg_72_, 11);
v_preferReleaseBuild_86_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*28 + 2);
v_testDriver_87_ = lean_ctor_get(v_cfg_72_, 12);
v_testDriverArgs_88_ = lean_ctor_get(v_cfg_72_, 13);
v_lintDriver_89_ = lean_ctor_get(v_cfg_72_, 14);
v_lintDriverArgs_90_ = lean_ctor_get(v_cfg_72_, 15);
v_version_91_ = lean_ctor_get(v_cfg_72_, 16);
v_versionTags_92_ = lean_ctor_get(v_cfg_72_, 17);
v_description_93_ = lean_ctor_get(v_cfg_72_, 18);
v_keywords_94_ = lean_ctor_get(v_cfg_72_, 19);
v_homepage_95_ = lean_ctor_get(v_cfg_72_, 20);
v_license_96_ = lean_ctor_get(v_cfg_72_, 21);
v_licenseFiles_97_ = lean_ctor_get(v_cfg_72_, 22);
v_readmeFile_98_ = lean_ctor_get(v_cfg_72_, 23);
v_reservoir_99_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_100_ = lean_ctor_get(v_cfg_72_, 24);
v_restoreAllArtifacts_x3f_101_ = lean_ctor_get(v_cfg_72_, 25);
v_libPrefixOnWindows_102_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*28 + 4);
v_allowImportAll_103_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_104_ = lean_ctor_get(v_cfg_72_, 26);
v_checks_105_ = lean_ctor_get(v_cfg_72_, 27);
v_fixedToolchain_106_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*28 + 6);
v_isSharedCheck_113_ = !lean_is_exclusive(v_cfg_72_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v_cfg_72_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_checks_105_);
lean_inc(v_builtinLint_x3f_104_);
lean_inc(v_restoreAllArtifacts_x3f_101_);
lean_inc(v_enableArtifactCache_x3f_100_);
lean_inc(v_readmeFile_98_);
lean_inc(v_licenseFiles_97_);
lean_inc(v_license_96_);
lean_inc(v_homepage_95_);
lean_inc(v_keywords_94_);
lean_inc(v_description_93_);
lean_inc(v_versionTags_92_);
lean_inc(v_version_91_);
lean_inc(v_lintDriverArgs_90_);
lean_inc(v_lintDriver_89_);
lean_inc(v_testDriverArgs_88_);
lean_inc(v_testDriver_87_);
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
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_toWorkspaceConfig_73_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_toLeanConfig_74_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_extraDepTargets_75_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v_moreGlobalServerArgs_77_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v_srcDir_78_);
lean_ctor_set(v_reuseFailAlloc_112_, 5, v_buildDir_79_);
lean_ctor_set(v_reuseFailAlloc_112_, 6, v_leanLibDir_80_);
lean_ctor_set(v_reuseFailAlloc_112_, 7, v_nativeLibDir_81_);
lean_ctor_set(v_reuseFailAlloc_112_, 8, v_binDir_82_);
lean_ctor_set(v_reuseFailAlloc_112_, 9, v_irDir_83_);
lean_ctor_set(v_reuseFailAlloc_112_, 10, v_releaseRepo_84_);
lean_ctor_set(v_reuseFailAlloc_112_, 11, v_buildArchive_85_);
lean_ctor_set(v_reuseFailAlloc_112_, 12, v_testDriver_87_);
lean_ctor_set(v_reuseFailAlloc_112_, 13, v_testDriverArgs_88_);
lean_ctor_set(v_reuseFailAlloc_112_, 14, v_lintDriver_89_);
lean_ctor_set(v_reuseFailAlloc_112_, 15, v_lintDriverArgs_90_);
lean_ctor_set(v_reuseFailAlloc_112_, 16, v_version_91_);
lean_ctor_set(v_reuseFailAlloc_112_, 17, v_versionTags_92_);
lean_ctor_set(v_reuseFailAlloc_112_, 18, v_description_93_);
lean_ctor_set(v_reuseFailAlloc_112_, 19, v_keywords_94_);
lean_ctor_set(v_reuseFailAlloc_112_, 20, v_homepage_95_);
lean_ctor_set(v_reuseFailAlloc_112_, 21, v_license_96_);
lean_ctor_set(v_reuseFailAlloc_112_, 22, v_licenseFiles_97_);
lean_ctor_set(v_reuseFailAlloc_112_, 23, v_readmeFile_98_);
lean_ctor_set(v_reuseFailAlloc_112_, 24, v_enableArtifactCache_x3f_100_);
lean_ctor_set(v_reuseFailAlloc_112_, 25, v_restoreAllArtifacts_x3f_101_);
lean_ctor_set(v_reuseFailAlloc_112_, 26, v_builtinLint_x3f_104_);
lean_ctor_set(v_reuseFailAlloc_112_, 27, v_checks_105_);
lean_ctor_set_uint8(v_reuseFailAlloc_112_, sizeof(void*)*28 + 1, v_precompileModules_76_);
lean_ctor_set_uint8(v_reuseFailAlloc_112_, sizeof(void*)*28 + 2, v_preferReleaseBuild_86_);
lean_ctor_set_uint8(v_reuseFailAlloc_112_, sizeof(void*)*28 + 3, v_reservoir_99_);
lean_ctor_set_uint8(v_reuseFailAlloc_112_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_102_);
lean_ctor_set_uint8(v_reuseFailAlloc_112_, sizeof(void*)*28 + 5, v_allowImportAll_103_);
lean_ctor_set_uint8(v_reuseFailAlloc_112_, sizeof(void*)*28 + 6, v_fixedToolchain_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*28, v_val_71_);
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1___boxed(lean_object* v_val_114_, lean_object* v_cfg_115_){
_start:
{
uint8_t v_val_141__boxed_116_; lean_object* v_res_117_; 
v_val_141__boxed_116_ = lean_unbox(v_val_114_);
v_res_117_ = l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1(v_val_141__boxed_116_, v_cfg_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__2(lean_object* v_f_118_, lean_object* v_cfg_119_){
_start:
{
lean_object* v_toWorkspaceConfig_120_; lean_object* v_toLeanConfig_121_; uint8_t v_bootstrap_122_; lean_object* v_extraDepTargets_123_; uint8_t v_precompileModules_124_; lean_object* v_moreGlobalServerArgs_125_; lean_object* v_srcDir_126_; lean_object* v_buildDir_127_; lean_object* v_leanLibDir_128_; lean_object* v_nativeLibDir_129_; lean_object* v_binDir_130_; lean_object* v_irDir_131_; lean_object* v_releaseRepo_132_; lean_object* v_buildArchive_133_; uint8_t v_preferReleaseBuild_134_; lean_object* v_testDriver_135_; lean_object* v_testDriverArgs_136_; lean_object* v_lintDriver_137_; lean_object* v_lintDriverArgs_138_; lean_object* v_version_139_; lean_object* v_versionTags_140_; lean_object* v_description_141_; lean_object* v_keywords_142_; lean_object* v_homepage_143_; lean_object* v_license_144_; lean_object* v_licenseFiles_145_; lean_object* v_readmeFile_146_; uint8_t v_reservoir_147_; lean_object* v_enableArtifactCache_x3f_148_; lean_object* v_restoreAllArtifacts_x3f_149_; uint8_t v_libPrefixOnWindows_150_; uint8_t v_allowImportAll_151_; lean_object* v_builtinLint_x3f_152_; lean_object* v_checks_153_; uint8_t v_fixedToolchain_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_164_; 
v_toWorkspaceConfig_120_ = lean_ctor_get(v_cfg_119_, 0);
v_toLeanConfig_121_ = lean_ctor_get(v_cfg_119_, 1);
v_bootstrap_122_ = lean_ctor_get_uint8(v_cfg_119_, sizeof(void*)*28);
v_extraDepTargets_123_ = lean_ctor_get(v_cfg_119_, 2);
v_precompileModules_124_ = lean_ctor_get_uint8(v_cfg_119_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_125_ = lean_ctor_get(v_cfg_119_, 3);
v_srcDir_126_ = lean_ctor_get(v_cfg_119_, 4);
v_buildDir_127_ = lean_ctor_get(v_cfg_119_, 5);
v_leanLibDir_128_ = lean_ctor_get(v_cfg_119_, 6);
v_nativeLibDir_129_ = lean_ctor_get(v_cfg_119_, 7);
v_binDir_130_ = lean_ctor_get(v_cfg_119_, 8);
v_irDir_131_ = lean_ctor_get(v_cfg_119_, 9);
v_releaseRepo_132_ = lean_ctor_get(v_cfg_119_, 10);
v_buildArchive_133_ = lean_ctor_get(v_cfg_119_, 11);
v_preferReleaseBuild_134_ = lean_ctor_get_uint8(v_cfg_119_, sizeof(void*)*28 + 2);
v_testDriver_135_ = lean_ctor_get(v_cfg_119_, 12);
v_testDriverArgs_136_ = lean_ctor_get(v_cfg_119_, 13);
v_lintDriver_137_ = lean_ctor_get(v_cfg_119_, 14);
v_lintDriverArgs_138_ = lean_ctor_get(v_cfg_119_, 15);
v_version_139_ = lean_ctor_get(v_cfg_119_, 16);
v_versionTags_140_ = lean_ctor_get(v_cfg_119_, 17);
v_description_141_ = lean_ctor_get(v_cfg_119_, 18);
v_keywords_142_ = lean_ctor_get(v_cfg_119_, 19);
v_homepage_143_ = lean_ctor_get(v_cfg_119_, 20);
v_license_144_ = lean_ctor_get(v_cfg_119_, 21);
v_licenseFiles_145_ = lean_ctor_get(v_cfg_119_, 22);
v_readmeFile_146_ = lean_ctor_get(v_cfg_119_, 23);
v_reservoir_147_ = lean_ctor_get_uint8(v_cfg_119_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_148_ = lean_ctor_get(v_cfg_119_, 24);
v_restoreAllArtifacts_x3f_149_ = lean_ctor_get(v_cfg_119_, 25);
v_libPrefixOnWindows_150_ = lean_ctor_get_uint8(v_cfg_119_, sizeof(void*)*28 + 4);
v_allowImportAll_151_ = lean_ctor_get_uint8(v_cfg_119_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_152_ = lean_ctor_get(v_cfg_119_, 26);
v_checks_153_ = lean_ctor_get(v_cfg_119_, 27);
v_fixedToolchain_154_ = lean_ctor_get_uint8(v_cfg_119_, sizeof(void*)*28 + 6);
v_isSharedCheck_164_ = !lean_is_exclusive(v_cfg_119_);
if (v_isSharedCheck_164_ == 0)
{
v___x_156_ = v_cfg_119_;
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_checks_153_);
lean_inc(v_builtinLint_x3f_152_);
lean_inc(v_restoreAllArtifacts_x3f_149_);
lean_inc(v_enableArtifactCache_x3f_148_);
lean_inc(v_readmeFile_146_);
lean_inc(v_licenseFiles_145_);
lean_inc(v_license_144_);
lean_inc(v_homepage_143_);
lean_inc(v_keywords_142_);
lean_inc(v_description_141_);
lean_inc(v_versionTags_140_);
lean_inc(v_version_139_);
lean_inc(v_lintDriverArgs_138_);
lean_inc(v_lintDriver_137_);
lean_inc(v_testDriverArgs_136_);
lean_inc(v_testDriver_135_);
lean_inc(v_buildArchive_133_);
lean_inc(v_releaseRepo_132_);
lean_inc(v_irDir_131_);
lean_inc(v_binDir_130_);
lean_inc(v_nativeLibDir_129_);
lean_inc(v_leanLibDir_128_);
lean_inc(v_buildDir_127_);
lean_inc(v_srcDir_126_);
lean_inc(v_moreGlobalServerArgs_125_);
lean_inc(v_extraDepTargets_123_);
lean_inc(v_toLeanConfig_121_);
lean_inc(v_toWorkspaceConfig_120_);
lean_dec(v_cfg_119_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_158_ = lean_box(v_bootstrap_122_);
v___x_159_ = lean_apply_1(v_f_118_, v___x_158_);
if (v_isShared_157_ == 0)
{
v___x_161_ = v___x_156_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_toWorkspaceConfig_120_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_toLeanConfig_121_);
lean_ctor_set(v_reuseFailAlloc_163_, 2, v_extraDepTargets_123_);
lean_ctor_set(v_reuseFailAlloc_163_, 3, v_moreGlobalServerArgs_125_);
lean_ctor_set(v_reuseFailAlloc_163_, 4, v_srcDir_126_);
lean_ctor_set(v_reuseFailAlloc_163_, 5, v_buildDir_127_);
lean_ctor_set(v_reuseFailAlloc_163_, 6, v_leanLibDir_128_);
lean_ctor_set(v_reuseFailAlloc_163_, 7, v_nativeLibDir_129_);
lean_ctor_set(v_reuseFailAlloc_163_, 8, v_binDir_130_);
lean_ctor_set(v_reuseFailAlloc_163_, 9, v_irDir_131_);
lean_ctor_set(v_reuseFailAlloc_163_, 10, v_releaseRepo_132_);
lean_ctor_set(v_reuseFailAlloc_163_, 11, v_buildArchive_133_);
lean_ctor_set(v_reuseFailAlloc_163_, 12, v_testDriver_135_);
lean_ctor_set(v_reuseFailAlloc_163_, 13, v_testDriverArgs_136_);
lean_ctor_set(v_reuseFailAlloc_163_, 14, v_lintDriver_137_);
lean_ctor_set(v_reuseFailAlloc_163_, 15, v_lintDriverArgs_138_);
lean_ctor_set(v_reuseFailAlloc_163_, 16, v_version_139_);
lean_ctor_set(v_reuseFailAlloc_163_, 17, v_versionTags_140_);
lean_ctor_set(v_reuseFailAlloc_163_, 18, v_description_141_);
lean_ctor_set(v_reuseFailAlloc_163_, 19, v_keywords_142_);
lean_ctor_set(v_reuseFailAlloc_163_, 20, v_homepage_143_);
lean_ctor_set(v_reuseFailAlloc_163_, 21, v_license_144_);
lean_ctor_set(v_reuseFailAlloc_163_, 22, v_licenseFiles_145_);
lean_ctor_set(v_reuseFailAlloc_163_, 23, v_readmeFile_146_);
lean_ctor_set(v_reuseFailAlloc_163_, 24, v_enableArtifactCache_x3f_148_);
lean_ctor_set(v_reuseFailAlloc_163_, 25, v_restoreAllArtifacts_x3f_149_);
lean_ctor_set(v_reuseFailAlloc_163_, 26, v_builtinLint_x3f_152_);
lean_ctor_set(v_reuseFailAlloc_163_, 27, v_checks_153_);
v___x_161_ = v_reuseFailAlloc_163_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
uint8_t v___x_162_; 
v___x_162_ = lean_unbox(v___x_159_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*28, v___x_162_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*28 + 1, v_precompileModules_124_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*28 + 2, v_preferReleaseBuild_134_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*28 + 3, v_reservoir_147_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_150_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*28 + 5, v_allowImportAll_151_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*28 + 6, v_fixedToolchain_154_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3(lean_object* v_x_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = 0;
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3___boxed(lean_object* v_x_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3(v_x_167_);
lean_dec_ref(v_x_167_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg(){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = ((lean_object*)(l_Lake_PackageConfig_bootstrap___proj___redArg___closed__4));
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___boxed(lean_object* v___dummy_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lake_PackageConfig_bootstrap___proj___redArg();
return v_res_182_;
}
}
static lean_object* _init_l_Lake_PackageConfig_bootstrap___proj___closed__0(void){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lake_PackageConfig_bootstrap___proj___redArg();
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object* v_p_184_, lean_object* v_n_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lake_PackageConfig_bootstrap___proj___closed__0, &l_Lake_PackageConfig_bootstrap___proj___closed__0_once, _init_l_Lake_PackageConfig_bootstrap___proj___closed__0);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___boxed(lean_object* v_p_187_, lean_object* v_n_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lake_PackageConfig_bootstrap___proj(v_p_187_, v_n_188_);
lean_dec(v_n_188_);
lean_dec(v_p_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___redArg(){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lake_PackageConfig_bootstrap___proj___closed__0, &l_Lake_PackageConfig_bootstrap___proj___closed__0_once, _init_l_Lake_PackageConfig_bootstrap___proj___closed__0);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___redArg___boxed(lean_object* v___dummy_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lake_PackageConfig_bootstrap_instConfigField___redArg();
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField(lean_object* v_p_194_, lean_object* v_n_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&l_Lake_PackageConfig_bootstrap___proj___closed__0, &l_Lake_PackageConfig_bootstrap___proj___closed__0_once, _init_l_Lake_PackageConfig_bootstrap___proj___closed__0);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___boxed(lean_object* v_p_197_, lean_object* v_n_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lake_PackageConfig_bootstrap_instConfigField(v_p_197_, v_n_198_);
lean_dec(v_n_198_);
lean_dec(v_p_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0(lean_object* v_cfg_200_){
_start:
{
lean_object* v_extraDepTargets_201_; 
v_extraDepTargets_201_ = lean_ctor_get(v_cfg_200_, 2);
lean_inc_ref(v_extraDepTargets_201_);
return v_extraDepTargets_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0___boxed(lean_object* v_cfg_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0(v_cfg_202_);
lean_dec_ref(v_cfg_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__1(lean_object* v_val_204_, lean_object* v_cfg_205_){
_start:
{
lean_object* v_toWorkspaceConfig_206_; lean_object* v_toLeanConfig_207_; uint8_t v_bootstrap_208_; uint8_t v_precompileModules_209_; lean_object* v_moreGlobalServerArgs_210_; lean_object* v_srcDir_211_; lean_object* v_buildDir_212_; lean_object* v_leanLibDir_213_; lean_object* v_nativeLibDir_214_; lean_object* v_binDir_215_; lean_object* v_irDir_216_; lean_object* v_releaseRepo_217_; lean_object* v_buildArchive_218_; uint8_t v_preferReleaseBuild_219_; lean_object* v_testDriver_220_; lean_object* v_testDriverArgs_221_; lean_object* v_lintDriver_222_; lean_object* v_lintDriverArgs_223_; lean_object* v_version_224_; lean_object* v_versionTags_225_; lean_object* v_description_226_; lean_object* v_keywords_227_; lean_object* v_homepage_228_; lean_object* v_license_229_; lean_object* v_licenseFiles_230_; lean_object* v_readmeFile_231_; uint8_t v_reservoir_232_; lean_object* v_enableArtifactCache_x3f_233_; lean_object* v_restoreAllArtifacts_x3f_234_; uint8_t v_libPrefixOnWindows_235_; uint8_t v_allowImportAll_236_; lean_object* v_builtinLint_x3f_237_; lean_object* v_checks_238_; uint8_t v_fixedToolchain_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
v_toWorkspaceConfig_206_ = lean_ctor_get(v_cfg_205_, 0);
v_toLeanConfig_207_ = lean_ctor_get(v_cfg_205_, 1);
v_bootstrap_208_ = lean_ctor_get_uint8(v_cfg_205_, sizeof(void*)*28);
v_precompileModules_209_ = lean_ctor_get_uint8(v_cfg_205_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_210_ = lean_ctor_get(v_cfg_205_, 3);
v_srcDir_211_ = lean_ctor_get(v_cfg_205_, 4);
v_buildDir_212_ = lean_ctor_get(v_cfg_205_, 5);
v_leanLibDir_213_ = lean_ctor_get(v_cfg_205_, 6);
v_nativeLibDir_214_ = lean_ctor_get(v_cfg_205_, 7);
v_binDir_215_ = lean_ctor_get(v_cfg_205_, 8);
v_irDir_216_ = lean_ctor_get(v_cfg_205_, 9);
v_releaseRepo_217_ = lean_ctor_get(v_cfg_205_, 10);
v_buildArchive_218_ = lean_ctor_get(v_cfg_205_, 11);
v_preferReleaseBuild_219_ = lean_ctor_get_uint8(v_cfg_205_, sizeof(void*)*28 + 2);
v_testDriver_220_ = lean_ctor_get(v_cfg_205_, 12);
v_testDriverArgs_221_ = lean_ctor_get(v_cfg_205_, 13);
v_lintDriver_222_ = lean_ctor_get(v_cfg_205_, 14);
v_lintDriverArgs_223_ = lean_ctor_get(v_cfg_205_, 15);
v_version_224_ = lean_ctor_get(v_cfg_205_, 16);
v_versionTags_225_ = lean_ctor_get(v_cfg_205_, 17);
v_description_226_ = lean_ctor_get(v_cfg_205_, 18);
v_keywords_227_ = lean_ctor_get(v_cfg_205_, 19);
v_homepage_228_ = lean_ctor_get(v_cfg_205_, 20);
v_license_229_ = lean_ctor_get(v_cfg_205_, 21);
v_licenseFiles_230_ = lean_ctor_get(v_cfg_205_, 22);
v_readmeFile_231_ = lean_ctor_get(v_cfg_205_, 23);
v_reservoir_232_ = lean_ctor_get_uint8(v_cfg_205_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_233_ = lean_ctor_get(v_cfg_205_, 24);
v_restoreAllArtifacts_x3f_234_ = lean_ctor_get(v_cfg_205_, 25);
v_libPrefixOnWindows_235_ = lean_ctor_get_uint8(v_cfg_205_, sizeof(void*)*28 + 4);
v_allowImportAll_236_ = lean_ctor_get_uint8(v_cfg_205_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_237_ = lean_ctor_get(v_cfg_205_, 26);
v_checks_238_ = lean_ctor_get(v_cfg_205_, 27);
v_fixedToolchain_239_ = lean_ctor_get_uint8(v_cfg_205_, sizeof(void*)*28 + 6);
v_isSharedCheck_246_ = !lean_is_exclusive(v_cfg_205_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v_cfg_205_, 2);
lean_dec(v_unused_247_);
v___x_241_ = v_cfg_205_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_checks_238_);
lean_inc(v_builtinLint_x3f_237_);
lean_inc(v_restoreAllArtifacts_x3f_234_);
lean_inc(v_enableArtifactCache_x3f_233_);
lean_inc(v_readmeFile_231_);
lean_inc(v_licenseFiles_230_);
lean_inc(v_license_229_);
lean_inc(v_homepage_228_);
lean_inc(v_keywords_227_);
lean_inc(v_description_226_);
lean_inc(v_versionTags_225_);
lean_inc(v_version_224_);
lean_inc(v_lintDriverArgs_223_);
lean_inc(v_lintDriver_222_);
lean_inc(v_testDriverArgs_221_);
lean_inc(v_testDriver_220_);
lean_inc(v_buildArchive_218_);
lean_inc(v_releaseRepo_217_);
lean_inc(v_irDir_216_);
lean_inc(v_binDir_215_);
lean_inc(v_nativeLibDir_214_);
lean_inc(v_leanLibDir_213_);
lean_inc(v_buildDir_212_);
lean_inc(v_srcDir_211_);
lean_inc(v_moreGlobalServerArgs_210_);
lean_inc(v_toLeanConfig_207_);
lean_inc(v_toWorkspaceConfig_206_);
lean_dec(v_cfg_205_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 2, v_val_204_);
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_toWorkspaceConfig_206_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_toLeanConfig_207_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_val_204_);
lean_ctor_set(v_reuseFailAlloc_245_, 3, v_moreGlobalServerArgs_210_);
lean_ctor_set(v_reuseFailAlloc_245_, 4, v_srcDir_211_);
lean_ctor_set(v_reuseFailAlloc_245_, 5, v_buildDir_212_);
lean_ctor_set(v_reuseFailAlloc_245_, 6, v_leanLibDir_213_);
lean_ctor_set(v_reuseFailAlloc_245_, 7, v_nativeLibDir_214_);
lean_ctor_set(v_reuseFailAlloc_245_, 8, v_binDir_215_);
lean_ctor_set(v_reuseFailAlloc_245_, 9, v_irDir_216_);
lean_ctor_set(v_reuseFailAlloc_245_, 10, v_releaseRepo_217_);
lean_ctor_set(v_reuseFailAlloc_245_, 11, v_buildArchive_218_);
lean_ctor_set(v_reuseFailAlloc_245_, 12, v_testDriver_220_);
lean_ctor_set(v_reuseFailAlloc_245_, 13, v_testDriverArgs_221_);
lean_ctor_set(v_reuseFailAlloc_245_, 14, v_lintDriver_222_);
lean_ctor_set(v_reuseFailAlloc_245_, 15, v_lintDriverArgs_223_);
lean_ctor_set(v_reuseFailAlloc_245_, 16, v_version_224_);
lean_ctor_set(v_reuseFailAlloc_245_, 17, v_versionTags_225_);
lean_ctor_set(v_reuseFailAlloc_245_, 18, v_description_226_);
lean_ctor_set(v_reuseFailAlloc_245_, 19, v_keywords_227_);
lean_ctor_set(v_reuseFailAlloc_245_, 20, v_homepage_228_);
lean_ctor_set(v_reuseFailAlloc_245_, 21, v_license_229_);
lean_ctor_set(v_reuseFailAlloc_245_, 22, v_licenseFiles_230_);
lean_ctor_set(v_reuseFailAlloc_245_, 23, v_readmeFile_231_);
lean_ctor_set(v_reuseFailAlloc_245_, 24, v_enableArtifactCache_x3f_233_);
lean_ctor_set(v_reuseFailAlloc_245_, 25, v_restoreAllArtifacts_x3f_234_);
lean_ctor_set(v_reuseFailAlloc_245_, 26, v_builtinLint_x3f_237_);
lean_ctor_set(v_reuseFailAlloc_245_, 27, v_checks_238_);
lean_ctor_set_uint8(v_reuseFailAlloc_245_, sizeof(void*)*28, v_bootstrap_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_245_, sizeof(void*)*28 + 1, v_precompileModules_209_);
lean_ctor_set_uint8(v_reuseFailAlloc_245_, sizeof(void*)*28 + 2, v_preferReleaseBuild_219_);
lean_ctor_set_uint8(v_reuseFailAlloc_245_, sizeof(void*)*28 + 3, v_reservoir_232_);
lean_ctor_set_uint8(v_reuseFailAlloc_245_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_235_);
lean_ctor_set_uint8(v_reuseFailAlloc_245_, sizeof(void*)*28 + 5, v_allowImportAll_236_);
lean_ctor_set_uint8(v_reuseFailAlloc_245_, sizeof(void*)*28 + 6, v_fixedToolchain_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__2(lean_object* v_f_248_, lean_object* v_cfg_249_){
_start:
{
lean_object* v_toWorkspaceConfig_250_; lean_object* v_toLeanConfig_251_; uint8_t v_bootstrap_252_; lean_object* v_extraDepTargets_253_; uint8_t v_precompileModules_254_; lean_object* v_moreGlobalServerArgs_255_; lean_object* v_srcDir_256_; lean_object* v_buildDir_257_; lean_object* v_leanLibDir_258_; lean_object* v_nativeLibDir_259_; lean_object* v_binDir_260_; lean_object* v_irDir_261_; lean_object* v_releaseRepo_262_; lean_object* v_buildArchive_263_; uint8_t v_preferReleaseBuild_264_; lean_object* v_testDriver_265_; lean_object* v_testDriverArgs_266_; lean_object* v_lintDriver_267_; lean_object* v_lintDriverArgs_268_; lean_object* v_version_269_; lean_object* v_versionTags_270_; lean_object* v_description_271_; lean_object* v_keywords_272_; lean_object* v_homepage_273_; lean_object* v_license_274_; lean_object* v_licenseFiles_275_; lean_object* v_readmeFile_276_; uint8_t v_reservoir_277_; lean_object* v_enableArtifactCache_x3f_278_; lean_object* v_restoreAllArtifacts_x3f_279_; uint8_t v_libPrefixOnWindows_280_; uint8_t v_allowImportAll_281_; lean_object* v_builtinLint_x3f_282_; lean_object* v_checks_283_; uint8_t v_fixedToolchain_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_292_; 
v_toWorkspaceConfig_250_ = lean_ctor_get(v_cfg_249_, 0);
v_toLeanConfig_251_ = lean_ctor_get(v_cfg_249_, 1);
v_bootstrap_252_ = lean_ctor_get_uint8(v_cfg_249_, sizeof(void*)*28);
v_extraDepTargets_253_ = lean_ctor_get(v_cfg_249_, 2);
v_precompileModules_254_ = lean_ctor_get_uint8(v_cfg_249_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_255_ = lean_ctor_get(v_cfg_249_, 3);
v_srcDir_256_ = lean_ctor_get(v_cfg_249_, 4);
v_buildDir_257_ = lean_ctor_get(v_cfg_249_, 5);
v_leanLibDir_258_ = lean_ctor_get(v_cfg_249_, 6);
v_nativeLibDir_259_ = lean_ctor_get(v_cfg_249_, 7);
v_binDir_260_ = lean_ctor_get(v_cfg_249_, 8);
v_irDir_261_ = lean_ctor_get(v_cfg_249_, 9);
v_releaseRepo_262_ = lean_ctor_get(v_cfg_249_, 10);
v_buildArchive_263_ = lean_ctor_get(v_cfg_249_, 11);
v_preferReleaseBuild_264_ = lean_ctor_get_uint8(v_cfg_249_, sizeof(void*)*28 + 2);
v_testDriver_265_ = lean_ctor_get(v_cfg_249_, 12);
v_testDriverArgs_266_ = lean_ctor_get(v_cfg_249_, 13);
v_lintDriver_267_ = lean_ctor_get(v_cfg_249_, 14);
v_lintDriverArgs_268_ = lean_ctor_get(v_cfg_249_, 15);
v_version_269_ = lean_ctor_get(v_cfg_249_, 16);
v_versionTags_270_ = lean_ctor_get(v_cfg_249_, 17);
v_description_271_ = lean_ctor_get(v_cfg_249_, 18);
v_keywords_272_ = lean_ctor_get(v_cfg_249_, 19);
v_homepage_273_ = lean_ctor_get(v_cfg_249_, 20);
v_license_274_ = lean_ctor_get(v_cfg_249_, 21);
v_licenseFiles_275_ = lean_ctor_get(v_cfg_249_, 22);
v_readmeFile_276_ = lean_ctor_get(v_cfg_249_, 23);
v_reservoir_277_ = lean_ctor_get_uint8(v_cfg_249_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_278_ = lean_ctor_get(v_cfg_249_, 24);
v_restoreAllArtifacts_x3f_279_ = lean_ctor_get(v_cfg_249_, 25);
v_libPrefixOnWindows_280_ = lean_ctor_get_uint8(v_cfg_249_, sizeof(void*)*28 + 4);
v_allowImportAll_281_ = lean_ctor_get_uint8(v_cfg_249_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_282_ = lean_ctor_get(v_cfg_249_, 26);
v_checks_283_ = lean_ctor_get(v_cfg_249_, 27);
v_fixedToolchain_284_ = lean_ctor_get_uint8(v_cfg_249_, sizeof(void*)*28 + 6);
v_isSharedCheck_292_ = !lean_is_exclusive(v_cfg_249_);
if (v_isSharedCheck_292_ == 0)
{
v___x_286_ = v_cfg_249_;
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_checks_283_);
lean_inc(v_builtinLint_x3f_282_);
lean_inc(v_restoreAllArtifacts_x3f_279_);
lean_inc(v_enableArtifactCache_x3f_278_);
lean_inc(v_readmeFile_276_);
lean_inc(v_licenseFiles_275_);
lean_inc(v_license_274_);
lean_inc(v_homepage_273_);
lean_inc(v_keywords_272_);
lean_inc(v_description_271_);
lean_inc(v_versionTags_270_);
lean_inc(v_version_269_);
lean_inc(v_lintDriverArgs_268_);
lean_inc(v_lintDriver_267_);
lean_inc(v_testDriverArgs_266_);
lean_inc(v_testDriver_265_);
lean_inc(v_buildArchive_263_);
lean_inc(v_releaseRepo_262_);
lean_inc(v_irDir_261_);
lean_inc(v_binDir_260_);
lean_inc(v_nativeLibDir_259_);
lean_inc(v_leanLibDir_258_);
lean_inc(v_buildDir_257_);
lean_inc(v_srcDir_256_);
lean_inc(v_moreGlobalServerArgs_255_);
lean_inc(v_extraDepTargets_253_);
lean_inc(v_toLeanConfig_251_);
lean_inc(v_toWorkspaceConfig_250_);
lean_dec(v_cfg_249_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_apply_1(v_f_248_, v_extraDepTargets_253_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 2, v___x_288_);
v___x_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_toWorkspaceConfig_250_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_toLeanConfig_251_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_moreGlobalServerArgs_255_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_srcDir_256_);
lean_ctor_set(v_reuseFailAlloc_291_, 5, v_buildDir_257_);
lean_ctor_set(v_reuseFailAlloc_291_, 6, v_leanLibDir_258_);
lean_ctor_set(v_reuseFailAlloc_291_, 7, v_nativeLibDir_259_);
lean_ctor_set(v_reuseFailAlloc_291_, 8, v_binDir_260_);
lean_ctor_set(v_reuseFailAlloc_291_, 9, v_irDir_261_);
lean_ctor_set(v_reuseFailAlloc_291_, 10, v_releaseRepo_262_);
lean_ctor_set(v_reuseFailAlloc_291_, 11, v_buildArchive_263_);
lean_ctor_set(v_reuseFailAlloc_291_, 12, v_testDriver_265_);
lean_ctor_set(v_reuseFailAlloc_291_, 13, v_testDriverArgs_266_);
lean_ctor_set(v_reuseFailAlloc_291_, 14, v_lintDriver_267_);
lean_ctor_set(v_reuseFailAlloc_291_, 15, v_lintDriverArgs_268_);
lean_ctor_set(v_reuseFailAlloc_291_, 16, v_version_269_);
lean_ctor_set(v_reuseFailAlloc_291_, 17, v_versionTags_270_);
lean_ctor_set(v_reuseFailAlloc_291_, 18, v_description_271_);
lean_ctor_set(v_reuseFailAlloc_291_, 19, v_keywords_272_);
lean_ctor_set(v_reuseFailAlloc_291_, 20, v_homepage_273_);
lean_ctor_set(v_reuseFailAlloc_291_, 21, v_license_274_);
lean_ctor_set(v_reuseFailAlloc_291_, 22, v_licenseFiles_275_);
lean_ctor_set(v_reuseFailAlloc_291_, 23, v_readmeFile_276_);
lean_ctor_set(v_reuseFailAlloc_291_, 24, v_enableArtifactCache_x3f_278_);
lean_ctor_set(v_reuseFailAlloc_291_, 25, v_restoreAllArtifacts_x3f_279_);
lean_ctor_set(v_reuseFailAlloc_291_, 26, v_builtinLint_x3f_282_);
lean_ctor_set(v_reuseFailAlloc_291_, 27, v_checks_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*28, v_bootstrap_252_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*28 + 1, v_precompileModules_254_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*28 + 2, v_preferReleaseBuild_264_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*28 + 3, v_reservoir_277_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_280_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*28 + 5, v_allowImportAll_281_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*28 + 6, v_fixedToolchain_284_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3(lean_object* v_x_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__0));
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3___boxed(lean_object* v_x_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3(v_x_295_);
lean_dec_ref(v_x_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg(){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__4));
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___boxed(lean_object* v___dummy_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg();
return v_res_309_;
}
}
static lean_object* _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0(void){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg();
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object* v_p_311_, lean_object* v_n_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&l_Lake_PackageConfig_extraDepTargets___proj___closed__0, &l_Lake_PackageConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object* v_p_314_, lean_object* v_n_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_314_, v_n_315_);
lean_dec(v_n_315_);
lean_dec(v_p_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg(){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&l_Lake_PackageConfig_extraDepTargets___proj___closed__0, &l_Lake_PackageConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg___boxed(lean_object* v___dummy_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg();
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object* v_p_321_, lean_object* v_n_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_obj_once(&l_Lake_PackageConfig_extraDepTargets___proj___closed__0, &l_Lake_PackageConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object* v_p_324_, lean_object* v_n_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lake_PackageConfig_extraDepTargets_instConfigField(v_p_324_, v_n_325_);
lean_dec(v_n_325_);
lean_dec(v_p_324_);
return v_res_326_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0(lean_object* v_cfg_327_){
_start:
{
uint8_t v_precompileModules_328_; 
v_precompileModules_328_ = lean_ctor_get_uint8(v_cfg_327_, sizeof(void*)*28 + 1);
return v_precompileModules_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0___boxed(lean_object* v_cfg_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0(v_cfg_329_);
lean_dec_ref(v_cfg_329_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1(uint8_t v_val_332_, lean_object* v_cfg_333_){
_start:
{
lean_object* v_toWorkspaceConfig_334_; lean_object* v_toLeanConfig_335_; uint8_t v_bootstrap_336_; lean_object* v_extraDepTargets_337_; lean_object* v_moreGlobalServerArgs_338_; lean_object* v_srcDir_339_; lean_object* v_buildDir_340_; lean_object* v_leanLibDir_341_; lean_object* v_nativeLibDir_342_; lean_object* v_binDir_343_; lean_object* v_irDir_344_; lean_object* v_releaseRepo_345_; lean_object* v_buildArchive_346_; uint8_t v_preferReleaseBuild_347_; lean_object* v_testDriver_348_; lean_object* v_testDriverArgs_349_; lean_object* v_lintDriver_350_; lean_object* v_lintDriverArgs_351_; lean_object* v_version_352_; lean_object* v_versionTags_353_; lean_object* v_description_354_; lean_object* v_keywords_355_; lean_object* v_homepage_356_; lean_object* v_license_357_; lean_object* v_licenseFiles_358_; lean_object* v_readmeFile_359_; uint8_t v_reservoir_360_; lean_object* v_enableArtifactCache_x3f_361_; lean_object* v_restoreAllArtifacts_x3f_362_; uint8_t v_libPrefixOnWindows_363_; uint8_t v_allowImportAll_364_; lean_object* v_builtinLint_x3f_365_; lean_object* v_checks_366_; uint8_t v_fixedToolchain_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
v_toWorkspaceConfig_334_ = lean_ctor_get(v_cfg_333_, 0);
v_toLeanConfig_335_ = lean_ctor_get(v_cfg_333_, 1);
v_bootstrap_336_ = lean_ctor_get_uint8(v_cfg_333_, sizeof(void*)*28);
v_extraDepTargets_337_ = lean_ctor_get(v_cfg_333_, 2);
v_moreGlobalServerArgs_338_ = lean_ctor_get(v_cfg_333_, 3);
v_srcDir_339_ = lean_ctor_get(v_cfg_333_, 4);
v_buildDir_340_ = lean_ctor_get(v_cfg_333_, 5);
v_leanLibDir_341_ = lean_ctor_get(v_cfg_333_, 6);
v_nativeLibDir_342_ = lean_ctor_get(v_cfg_333_, 7);
v_binDir_343_ = lean_ctor_get(v_cfg_333_, 8);
v_irDir_344_ = lean_ctor_get(v_cfg_333_, 9);
v_releaseRepo_345_ = lean_ctor_get(v_cfg_333_, 10);
v_buildArchive_346_ = lean_ctor_get(v_cfg_333_, 11);
v_preferReleaseBuild_347_ = lean_ctor_get_uint8(v_cfg_333_, sizeof(void*)*28 + 2);
v_testDriver_348_ = lean_ctor_get(v_cfg_333_, 12);
v_testDriverArgs_349_ = lean_ctor_get(v_cfg_333_, 13);
v_lintDriver_350_ = lean_ctor_get(v_cfg_333_, 14);
v_lintDriverArgs_351_ = lean_ctor_get(v_cfg_333_, 15);
v_version_352_ = lean_ctor_get(v_cfg_333_, 16);
v_versionTags_353_ = lean_ctor_get(v_cfg_333_, 17);
v_description_354_ = lean_ctor_get(v_cfg_333_, 18);
v_keywords_355_ = lean_ctor_get(v_cfg_333_, 19);
v_homepage_356_ = lean_ctor_get(v_cfg_333_, 20);
v_license_357_ = lean_ctor_get(v_cfg_333_, 21);
v_licenseFiles_358_ = lean_ctor_get(v_cfg_333_, 22);
v_readmeFile_359_ = lean_ctor_get(v_cfg_333_, 23);
v_reservoir_360_ = lean_ctor_get_uint8(v_cfg_333_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_361_ = lean_ctor_get(v_cfg_333_, 24);
v_restoreAllArtifacts_x3f_362_ = lean_ctor_get(v_cfg_333_, 25);
v_libPrefixOnWindows_363_ = lean_ctor_get_uint8(v_cfg_333_, sizeof(void*)*28 + 4);
v_allowImportAll_364_ = lean_ctor_get_uint8(v_cfg_333_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_365_ = lean_ctor_get(v_cfg_333_, 26);
v_checks_366_ = lean_ctor_get(v_cfg_333_, 27);
v_fixedToolchain_367_ = lean_ctor_get_uint8(v_cfg_333_, sizeof(void*)*28 + 6);
v_isSharedCheck_374_ = !lean_is_exclusive(v_cfg_333_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v_cfg_333_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_checks_366_);
lean_inc(v_builtinLint_x3f_365_);
lean_inc(v_restoreAllArtifacts_x3f_362_);
lean_inc(v_enableArtifactCache_x3f_361_);
lean_inc(v_readmeFile_359_);
lean_inc(v_licenseFiles_358_);
lean_inc(v_license_357_);
lean_inc(v_homepage_356_);
lean_inc(v_keywords_355_);
lean_inc(v_description_354_);
lean_inc(v_versionTags_353_);
lean_inc(v_version_352_);
lean_inc(v_lintDriverArgs_351_);
lean_inc(v_lintDriver_350_);
lean_inc(v_testDriverArgs_349_);
lean_inc(v_testDriver_348_);
lean_inc(v_buildArchive_346_);
lean_inc(v_releaseRepo_345_);
lean_inc(v_irDir_344_);
lean_inc(v_binDir_343_);
lean_inc(v_nativeLibDir_342_);
lean_inc(v_leanLibDir_341_);
lean_inc(v_buildDir_340_);
lean_inc(v_srcDir_339_);
lean_inc(v_moreGlobalServerArgs_338_);
lean_inc(v_extraDepTargets_337_);
lean_inc(v_toLeanConfig_335_);
lean_inc(v_toWorkspaceConfig_334_);
lean_dec(v_cfg_333_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_toWorkspaceConfig_334_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_toLeanConfig_335_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_extraDepTargets_337_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_moreGlobalServerArgs_338_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_srcDir_339_);
lean_ctor_set(v_reuseFailAlloc_373_, 5, v_buildDir_340_);
lean_ctor_set(v_reuseFailAlloc_373_, 6, v_leanLibDir_341_);
lean_ctor_set(v_reuseFailAlloc_373_, 7, v_nativeLibDir_342_);
lean_ctor_set(v_reuseFailAlloc_373_, 8, v_binDir_343_);
lean_ctor_set(v_reuseFailAlloc_373_, 9, v_irDir_344_);
lean_ctor_set(v_reuseFailAlloc_373_, 10, v_releaseRepo_345_);
lean_ctor_set(v_reuseFailAlloc_373_, 11, v_buildArchive_346_);
lean_ctor_set(v_reuseFailAlloc_373_, 12, v_testDriver_348_);
lean_ctor_set(v_reuseFailAlloc_373_, 13, v_testDriverArgs_349_);
lean_ctor_set(v_reuseFailAlloc_373_, 14, v_lintDriver_350_);
lean_ctor_set(v_reuseFailAlloc_373_, 15, v_lintDriverArgs_351_);
lean_ctor_set(v_reuseFailAlloc_373_, 16, v_version_352_);
lean_ctor_set(v_reuseFailAlloc_373_, 17, v_versionTags_353_);
lean_ctor_set(v_reuseFailAlloc_373_, 18, v_description_354_);
lean_ctor_set(v_reuseFailAlloc_373_, 19, v_keywords_355_);
lean_ctor_set(v_reuseFailAlloc_373_, 20, v_homepage_356_);
lean_ctor_set(v_reuseFailAlloc_373_, 21, v_license_357_);
lean_ctor_set(v_reuseFailAlloc_373_, 22, v_licenseFiles_358_);
lean_ctor_set(v_reuseFailAlloc_373_, 23, v_readmeFile_359_);
lean_ctor_set(v_reuseFailAlloc_373_, 24, v_enableArtifactCache_x3f_361_);
lean_ctor_set(v_reuseFailAlloc_373_, 25, v_restoreAllArtifacts_x3f_362_);
lean_ctor_set(v_reuseFailAlloc_373_, 26, v_builtinLint_x3f_365_);
lean_ctor_set(v_reuseFailAlloc_373_, 27, v_checks_366_);
lean_ctor_set_uint8(v_reuseFailAlloc_373_, sizeof(void*)*28, v_bootstrap_336_);
lean_ctor_set_uint8(v_reuseFailAlloc_373_, sizeof(void*)*28 + 2, v_preferReleaseBuild_347_);
lean_ctor_set_uint8(v_reuseFailAlloc_373_, sizeof(void*)*28 + 3, v_reservoir_360_);
lean_ctor_set_uint8(v_reuseFailAlloc_373_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_363_);
lean_ctor_set_uint8(v_reuseFailAlloc_373_, sizeof(void*)*28 + 5, v_allowImportAll_364_);
lean_ctor_set_uint8(v_reuseFailAlloc_373_, sizeof(void*)*28 + 6, v_fixedToolchain_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*28 + 1, v_val_332_);
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1___boxed(lean_object* v_val_375_, lean_object* v_cfg_376_){
_start:
{
uint8_t v_val_141__boxed_377_; lean_object* v_res_378_; 
v_val_141__boxed_377_ = lean_unbox(v_val_375_);
v_res_378_ = l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1(v_val_141__boxed_377_, v_cfg_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__2(lean_object* v_f_379_, lean_object* v_cfg_380_){
_start:
{
lean_object* v_toWorkspaceConfig_381_; lean_object* v_toLeanConfig_382_; uint8_t v_bootstrap_383_; lean_object* v_extraDepTargets_384_; uint8_t v_precompileModules_385_; lean_object* v_moreGlobalServerArgs_386_; lean_object* v_srcDir_387_; lean_object* v_buildDir_388_; lean_object* v_leanLibDir_389_; lean_object* v_nativeLibDir_390_; lean_object* v_binDir_391_; lean_object* v_irDir_392_; lean_object* v_releaseRepo_393_; lean_object* v_buildArchive_394_; uint8_t v_preferReleaseBuild_395_; lean_object* v_testDriver_396_; lean_object* v_testDriverArgs_397_; lean_object* v_lintDriver_398_; lean_object* v_lintDriverArgs_399_; lean_object* v_version_400_; lean_object* v_versionTags_401_; lean_object* v_description_402_; lean_object* v_keywords_403_; lean_object* v_homepage_404_; lean_object* v_license_405_; lean_object* v_licenseFiles_406_; lean_object* v_readmeFile_407_; uint8_t v_reservoir_408_; lean_object* v_enableArtifactCache_x3f_409_; lean_object* v_restoreAllArtifacts_x3f_410_; uint8_t v_libPrefixOnWindows_411_; uint8_t v_allowImportAll_412_; lean_object* v_builtinLint_x3f_413_; lean_object* v_checks_414_; uint8_t v_fixedToolchain_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_425_; 
v_toWorkspaceConfig_381_ = lean_ctor_get(v_cfg_380_, 0);
v_toLeanConfig_382_ = lean_ctor_get(v_cfg_380_, 1);
v_bootstrap_383_ = lean_ctor_get_uint8(v_cfg_380_, sizeof(void*)*28);
v_extraDepTargets_384_ = lean_ctor_get(v_cfg_380_, 2);
v_precompileModules_385_ = lean_ctor_get_uint8(v_cfg_380_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_386_ = lean_ctor_get(v_cfg_380_, 3);
v_srcDir_387_ = lean_ctor_get(v_cfg_380_, 4);
v_buildDir_388_ = lean_ctor_get(v_cfg_380_, 5);
v_leanLibDir_389_ = lean_ctor_get(v_cfg_380_, 6);
v_nativeLibDir_390_ = lean_ctor_get(v_cfg_380_, 7);
v_binDir_391_ = lean_ctor_get(v_cfg_380_, 8);
v_irDir_392_ = lean_ctor_get(v_cfg_380_, 9);
v_releaseRepo_393_ = lean_ctor_get(v_cfg_380_, 10);
v_buildArchive_394_ = lean_ctor_get(v_cfg_380_, 11);
v_preferReleaseBuild_395_ = lean_ctor_get_uint8(v_cfg_380_, sizeof(void*)*28 + 2);
v_testDriver_396_ = lean_ctor_get(v_cfg_380_, 12);
v_testDriverArgs_397_ = lean_ctor_get(v_cfg_380_, 13);
v_lintDriver_398_ = lean_ctor_get(v_cfg_380_, 14);
v_lintDriverArgs_399_ = lean_ctor_get(v_cfg_380_, 15);
v_version_400_ = lean_ctor_get(v_cfg_380_, 16);
v_versionTags_401_ = lean_ctor_get(v_cfg_380_, 17);
v_description_402_ = lean_ctor_get(v_cfg_380_, 18);
v_keywords_403_ = lean_ctor_get(v_cfg_380_, 19);
v_homepage_404_ = lean_ctor_get(v_cfg_380_, 20);
v_license_405_ = lean_ctor_get(v_cfg_380_, 21);
v_licenseFiles_406_ = lean_ctor_get(v_cfg_380_, 22);
v_readmeFile_407_ = lean_ctor_get(v_cfg_380_, 23);
v_reservoir_408_ = lean_ctor_get_uint8(v_cfg_380_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_409_ = lean_ctor_get(v_cfg_380_, 24);
v_restoreAllArtifacts_x3f_410_ = lean_ctor_get(v_cfg_380_, 25);
v_libPrefixOnWindows_411_ = lean_ctor_get_uint8(v_cfg_380_, sizeof(void*)*28 + 4);
v_allowImportAll_412_ = lean_ctor_get_uint8(v_cfg_380_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_413_ = lean_ctor_get(v_cfg_380_, 26);
v_checks_414_ = lean_ctor_get(v_cfg_380_, 27);
v_fixedToolchain_415_ = lean_ctor_get_uint8(v_cfg_380_, sizeof(void*)*28 + 6);
v_isSharedCheck_425_ = !lean_is_exclusive(v_cfg_380_);
if (v_isSharedCheck_425_ == 0)
{
v___x_417_ = v_cfg_380_;
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_checks_414_);
lean_inc(v_builtinLint_x3f_413_);
lean_inc(v_restoreAllArtifacts_x3f_410_);
lean_inc(v_enableArtifactCache_x3f_409_);
lean_inc(v_readmeFile_407_);
lean_inc(v_licenseFiles_406_);
lean_inc(v_license_405_);
lean_inc(v_homepage_404_);
lean_inc(v_keywords_403_);
lean_inc(v_description_402_);
lean_inc(v_versionTags_401_);
lean_inc(v_version_400_);
lean_inc(v_lintDriverArgs_399_);
lean_inc(v_lintDriver_398_);
lean_inc(v_testDriverArgs_397_);
lean_inc(v_testDriver_396_);
lean_inc(v_buildArchive_394_);
lean_inc(v_releaseRepo_393_);
lean_inc(v_irDir_392_);
lean_inc(v_binDir_391_);
lean_inc(v_nativeLibDir_390_);
lean_inc(v_leanLibDir_389_);
lean_inc(v_buildDir_388_);
lean_inc(v_srcDir_387_);
lean_inc(v_moreGlobalServerArgs_386_);
lean_inc(v_extraDepTargets_384_);
lean_inc(v_toLeanConfig_382_);
lean_inc(v_toWorkspaceConfig_381_);
lean_dec(v_cfg_380_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_419_ = lean_box(v_precompileModules_385_);
v___x_420_ = lean_apply_1(v_f_379_, v___x_419_);
if (v_isShared_418_ == 0)
{
v___x_422_ = v___x_417_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_toWorkspaceConfig_381_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_toLeanConfig_382_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_extraDepTargets_384_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_moreGlobalServerArgs_386_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_srcDir_387_);
lean_ctor_set(v_reuseFailAlloc_424_, 5, v_buildDir_388_);
lean_ctor_set(v_reuseFailAlloc_424_, 6, v_leanLibDir_389_);
lean_ctor_set(v_reuseFailAlloc_424_, 7, v_nativeLibDir_390_);
lean_ctor_set(v_reuseFailAlloc_424_, 8, v_binDir_391_);
lean_ctor_set(v_reuseFailAlloc_424_, 9, v_irDir_392_);
lean_ctor_set(v_reuseFailAlloc_424_, 10, v_releaseRepo_393_);
lean_ctor_set(v_reuseFailAlloc_424_, 11, v_buildArchive_394_);
lean_ctor_set(v_reuseFailAlloc_424_, 12, v_testDriver_396_);
lean_ctor_set(v_reuseFailAlloc_424_, 13, v_testDriverArgs_397_);
lean_ctor_set(v_reuseFailAlloc_424_, 14, v_lintDriver_398_);
lean_ctor_set(v_reuseFailAlloc_424_, 15, v_lintDriverArgs_399_);
lean_ctor_set(v_reuseFailAlloc_424_, 16, v_version_400_);
lean_ctor_set(v_reuseFailAlloc_424_, 17, v_versionTags_401_);
lean_ctor_set(v_reuseFailAlloc_424_, 18, v_description_402_);
lean_ctor_set(v_reuseFailAlloc_424_, 19, v_keywords_403_);
lean_ctor_set(v_reuseFailAlloc_424_, 20, v_homepage_404_);
lean_ctor_set(v_reuseFailAlloc_424_, 21, v_license_405_);
lean_ctor_set(v_reuseFailAlloc_424_, 22, v_licenseFiles_406_);
lean_ctor_set(v_reuseFailAlloc_424_, 23, v_readmeFile_407_);
lean_ctor_set(v_reuseFailAlloc_424_, 24, v_enableArtifactCache_x3f_409_);
lean_ctor_set(v_reuseFailAlloc_424_, 25, v_restoreAllArtifacts_x3f_410_);
lean_ctor_set(v_reuseFailAlloc_424_, 26, v_builtinLint_x3f_413_);
lean_ctor_set(v_reuseFailAlloc_424_, 27, v_checks_414_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*28, v_bootstrap_383_);
v___x_422_ = v_reuseFailAlloc_424_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
uint8_t v___x_423_; 
v___x_423_ = lean_unbox(v___x_420_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*28 + 1, v___x_423_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*28 + 2, v_preferReleaseBuild_395_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*28 + 3, v_reservoir_408_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_411_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*28 + 5, v_allowImportAll_412_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*28 + 6, v_fixedToolchain_415_);
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg(){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = ((lean_object*)(l_Lake_PackageConfig_precompileModules___proj___redArg___closed__3));
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___boxed(lean_object* v___dummy_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lake_PackageConfig_precompileModules___proj___redArg();
return v_res_437_;
}
}
static lean_object* _init_l_Lake_PackageConfig_precompileModules___proj___closed__0(void){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lake_PackageConfig_precompileModules___proj___redArg();
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object* v_p_439_, lean_object* v_n_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_obj_once(&l_Lake_PackageConfig_precompileModules___proj___closed__0, &l_Lake_PackageConfig_precompileModules___proj___closed__0_once, _init_l_Lake_PackageConfig_precompileModules___proj___closed__0);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object* v_p_442_, lean_object* v_n_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lake_PackageConfig_precompileModules___proj(v_p_442_, v_n_443_);
lean_dec(v_n_443_);
lean_dec(v_p_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___redArg(){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = lean_obj_once(&l_Lake_PackageConfig_precompileModules___proj___closed__0, &l_Lake_PackageConfig_precompileModules___proj___closed__0_once, _init_l_Lake_PackageConfig_precompileModules___proj___closed__0);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___redArg___boxed(lean_object* v___dummy_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lake_PackageConfig_precompileModules_instConfigField___redArg();
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object* v_p_449_, lean_object* v_n_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = lean_obj_once(&l_Lake_PackageConfig_precompileModules___proj___closed__0, &l_Lake_PackageConfig_precompileModules___proj___closed__0_once, _init_l_Lake_PackageConfig_precompileModules___proj___closed__0);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object* v_p_452_, lean_object* v_n_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lake_PackageConfig_precompileModules_instConfigField(v_p_452_, v_n_453_);
lean_dec(v_n_453_);
lean_dec(v_p_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0(lean_object* v_cfg_455_){
_start:
{
lean_object* v_moreGlobalServerArgs_456_; 
v_moreGlobalServerArgs_456_ = lean_ctor_get(v_cfg_455_, 3);
lean_inc_ref(v_moreGlobalServerArgs_456_);
return v_moreGlobalServerArgs_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0___boxed(lean_object* v_cfg_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0(v_cfg_457_);
lean_dec_ref(v_cfg_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__1(lean_object* v_val_459_, lean_object* v_cfg_460_){
_start:
{
lean_object* v_toWorkspaceConfig_461_; lean_object* v_toLeanConfig_462_; uint8_t v_bootstrap_463_; lean_object* v_extraDepTargets_464_; uint8_t v_precompileModules_465_; lean_object* v_srcDir_466_; lean_object* v_buildDir_467_; lean_object* v_leanLibDir_468_; lean_object* v_nativeLibDir_469_; lean_object* v_binDir_470_; lean_object* v_irDir_471_; lean_object* v_releaseRepo_472_; lean_object* v_buildArchive_473_; uint8_t v_preferReleaseBuild_474_; lean_object* v_testDriver_475_; lean_object* v_testDriverArgs_476_; lean_object* v_lintDriver_477_; lean_object* v_lintDriverArgs_478_; lean_object* v_version_479_; lean_object* v_versionTags_480_; lean_object* v_description_481_; lean_object* v_keywords_482_; lean_object* v_homepage_483_; lean_object* v_license_484_; lean_object* v_licenseFiles_485_; lean_object* v_readmeFile_486_; uint8_t v_reservoir_487_; lean_object* v_enableArtifactCache_x3f_488_; lean_object* v_restoreAllArtifacts_x3f_489_; uint8_t v_libPrefixOnWindows_490_; uint8_t v_allowImportAll_491_; lean_object* v_builtinLint_x3f_492_; lean_object* v_checks_493_; uint8_t v_fixedToolchain_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_toWorkspaceConfig_461_ = lean_ctor_get(v_cfg_460_, 0);
v_toLeanConfig_462_ = lean_ctor_get(v_cfg_460_, 1);
v_bootstrap_463_ = lean_ctor_get_uint8(v_cfg_460_, sizeof(void*)*28);
v_extraDepTargets_464_ = lean_ctor_get(v_cfg_460_, 2);
v_precompileModules_465_ = lean_ctor_get_uint8(v_cfg_460_, sizeof(void*)*28 + 1);
v_srcDir_466_ = lean_ctor_get(v_cfg_460_, 4);
v_buildDir_467_ = lean_ctor_get(v_cfg_460_, 5);
v_leanLibDir_468_ = lean_ctor_get(v_cfg_460_, 6);
v_nativeLibDir_469_ = lean_ctor_get(v_cfg_460_, 7);
v_binDir_470_ = lean_ctor_get(v_cfg_460_, 8);
v_irDir_471_ = lean_ctor_get(v_cfg_460_, 9);
v_releaseRepo_472_ = lean_ctor_get(v_cfg_460_, 10);
v_buildArchive_473_ = lean_ctor_get(v_cfg_460_, 11);
v_preferReleaseBuild_474_ = lean_ctor_get_uint8(v_cfg_460_, sizeof(void*)*28 + 2);
v_testDriver_475_ = lean_ctor_get(v_cfg_460_, 12);
v_testDriverArgs_476_ = lean_ctor_get(v_cfg_460_, 13);
v_lintDriver_477_ = lean_ctor_get(v_cfg_460_, 14);
v_lintDriverArgs_478_ = lean_ctor_get(v_cfg_460_, 15);
v_version_479_ = lean_ctor_get(v_cfg_460_, 16);
v_versionTags_480_ = lean_ctor_get(v_cfg_460_, 17);
v_description_481_ = lean_ctor_get(v_cfg_460_, 18);
v_keywords_482_ = lean_ctor_get(v_cfg_460_, 19);
v_homepage_483_ = lean_ctor_get(v_cfg_460_, 20);
v_license_484_ = lean_ctor_get(v_cfg_460_, 21);
v_licenseFiles_485_ = lean_ctor_get(v_cfg_460_, 22);
v_readmeFile_486_ = lean_ctor_get(v_cfg_460_, 23);
v_reservoir_487_ = lean_ctor_get_uint8(v_cfg_460_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_488_ = lean_ctor_get(v_cfg_460_, 24);
v_restoreAllArtifacts_x3f_489_ = lean_ctor_get(v_cfg_460_, 25);
v_libPrefixOnWindows_490_ = lean_ctor_get_uint8(v_cfg_460_, sizeof(void*)*28 + 4);
v_allowImportAll_491_ = lean_ctor_get_uint8(v_cfg_460_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_492_ = lean_ctor_get(v_cfg_460_, 26);
v_checks_493_ = lean_ctor_get(v_cfg_460_, 27);
v_fixedToolchain_494_ = lean_ctor_get_uint8(v_cfg_460_, sizeof(void*)*28 + 6);
v_isSharedCheck_501_ = !lean_is_exclusive(v_cfg_460_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v_cfg_460_, 3);
lean_dec(v_unused_502_);
v___x_496_ = v_cfg_460_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_checks_493_);
lean_inc(v_builtinLint_x3f_492_);
lean_inc(v_restoreAllArtifacts_x3f_489_);
lean_inc(v_enableArtifactCache_x3f_488_);
lean_inc(v_readmeFile_486_);
lean_inc(v_licenseFiles_485_);
lean_inc(v_license_484_);
lean_inc(v_homepage_483_);
lean_inc(v_keywords_482_);
lean_inc(v_description_481_);
lean_inc(v_versionTags_480_);
lean_inc(v_version_479_);
lean_inc(v_lintDriverArgs_478_);
lean_inc(v_lintDriver_477_);
lean_inc(v_testDriverArgs_476_);
lean_inc(v_testDriver_475_);
lean_inc(v_buildArchive_473_);
lean_inc(v_releaseRepo_472_);
lean_inc(v_irDir_471_);
lean_inc(v_binDir_470_);
lean_inc(v_nativeLibDir_469_);
lean_inc(v_leanLibDir_468_);
lean_inc(v_buildDir_467_);
lean_inc(v_srcDir_466_);
lean_inc(v_extraDepTargets_464_);
lean_inc(v_toLeanConfig_462_);
lean_inc(v_toWorkspaceConfig_461_);
lean_dec(v_cfg_460_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 3, v_val_459_);
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_toWorkspaceConfig_461_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_toLeanConfig_462_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_extraDepTargets_464_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_val_459_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_srcDir_466_);
lean_ctor_set(v_reuseFailAlloc_500_, 5, v_buildDir_467_);
lean_ctor_set(v_reuseFailAlloc_500_, 6, v_leanLibDir_468_);
lean_ctor_set(v_reuseFailAlloc_500_, 7, v_nativeLibDir_469_);
lean_ctor_set(v_reuseFailAlloc_500_, 8, v_binDir_470_);
lean_ctor_set(v_reuseFailAlloc_500_, 9, v_irDir_471_);
lean_ctor_set(v_reuseFailAlloc_500_, 10, v_releaseRepo_472_);
lean_ctor_set(v_reuseFailAlloc_500_, 11, v_buildArchive_473_);
lean_ctor_set(v_reuseFailAlloc_500_, 12, v_testDriver_475_);
lean_ctor_set(v_reuseFailAlloc_500_, 13, v_testDriverArgs_476_);
lean_ctor_set(v_reuseFailAlloc_500_, 14, v_lintDriver_477_);
lean_ctor_set(v_reuseFailAlloc_500_, 15, v_lintDriverArgs_478_);
lean_ctor_set(v_reuseFailAlloc_500_, 16, v_version_479_);
lean_ctor_set(v_reuseFailAlloc_500_, 17, v_versionTags_480_);
lean_ctor_set(v_reuseFailAlloc_500_, 18, v_description_481_);
lean_ctor_set(v_reuseFailAlloc_500_, 19, v_keywords_482_);
lean_ctor_set(v_reuseFailAlloc_500_, 20, v_homepage_483_);
lean_ctor_set(v_reuseFailAlloc_500_, 21, v_license_484_);
lean_ctor_set(v_reuseFailAlloc_500_, 22, v_licenseFiles_485_);
lean_ctor_set(v_reuseFailAlloc_500_, 23, v_readmeFile_486_);
lean_ctor_set(v_reuseFailAlloc_500_, 24, v_enableArtifactCache_x3f_488_);
lean_ctor_set(v_reuseFailAlloc_500_, 25, v_restoreAllArtifacts_x3f_489_);
lean_ctor_set(v_reuseFailAlloc_500_, 26, v_builtinLint_x3f_492_);
lean_ctor_set(v_reuseFailAlloc_500_, 27, v_checks_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, sizeof(void*)*28, v_bootstrap_463_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, sizeof(void*)*28 + 1, v_precompileModules_465_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, sizeof(void*)*28 + 2, v_preferReleaseBuild_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, sizeof(void*)*28 + 3, v_reservoir_487_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, sizeof(void*)*28 + 5, v_allowImportAll_491_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, sizeof(void*)*28 + 6, v_fixedToolchain_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__2(lean_object* v_f_503_, lean_object* v_cfg_504_){
_start:
{
lean_object* v_toWorkspaceConfig_505_; lean_object* v_toLeanConfig_506_; uint8_t v_bootstrap_507_; lean_object* v_extraDepTargets_508_; uint8_t v_precompileModules_509_; lean_object* v_moreGlobalServerArgs_510_; lean_object* v_srcDir_511_; lean_object* v_buildDir_512_; lean_object* v_leanLibDir_513_; lean_object* v_nativeLibDir_514_; lean_object* v_binDir_515_; lean_object* v_irDir_516_; lean_object* v_releaseRepo_517_; lean_object* v_buildArchive_518_; uint8_t v_preferReleaseBuild_519_; lean_object* v_testDriver_520_; lean_object* v_testDriverArgs_521_; lean_object* v_lintDriver_522_; lean_object* v_lintDriverArgs_523_; lean_object* v_version_524_; lean_object* v_versionTags_525_; lean_object* v_description_526_; lean_object* v_keywords_527_; lean_object* v_homepage_528_; lean_object* v_license_529_; lean_object* v_licenseFiles_530_; lean_object* v_readmeFile_531_; uint8_t v_reservoir_532_; lean_object* v_enableArtifactCache_x3f_533_; lean_object* v_restoreAllArtifacts_x3f_534_; uint8_t v_libPrefixOnWindows_535_; uint8_t v_allowImportAll_536_; lean_object* v_builtinLint_x3f_537_; lean_object* v_checks_538_; uint8_t v_fixedToolchain_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_547_; 
v_toWorkspaceConfig_505_ = lean_ctor_get(v_cfg_504_, 0);
v_toLeanConfig_506_ = lean_ctor_get(v_cfg_504_, 1);
v_bootstrap_507_ = lean_ctor_get_uint8(v_cfg_504_, sizeof(void*)*28);
v_extraDepTargets_508_ = lean_ctor_get(v_cfg_504_, 2);
v_precompileModules_509_ = lean_ctor_get_uint8(v_cfg_504_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_510_ = lean_ctor_get(v_cfg_504_, 3);
v_srcDir_511_ = lean_ctor_get(v_cfg_504_, 4);
v_buildDir_512_ = lean_ctor_get(v_cfg_504_, 5);
v_leanLibDir_513_ = lean_ctor_get(v_cfg_504_, 6);
v_nativeLibDir_514_ = lean_ctor_get(v_cfg_504_, 7);
v_binDir_515_ = lean_ctor_get(v_cfg_504_, 8);
v_irDir_516_ = lean_ctor_get(v_cfg_504_, 9);
v_releaseRepo_517_ = lean_ctor_get(v_cfg_504_, 10);
v_buildArchive_518_ = lean_ctor_get(v_cfg_504_, 11);
v_preferReleaseBuild_519_ = lean_ctor_get_uint8(v_cfg_504_, sizeof(void*)*28 + 2);
v_testDriver_520_ = lean_ctor_get(v_cfg_504_, 12);
v_testDriverArgs_521_ = lean_ctor_get(v_cfg_504_, 13);
v_lintDriver_522_ = lean_ctor_get(v_cfg_504_, 14);
v_lintDriverArgs_523_ = lean_ctor_get(v_cfg_504_, 15);
v_version_524_ = lean_ctor_get(v_cfg_504_, 16);
v_versionTags_525_ = lean_ctor_get(v_cfg_504_, 17);
v_description_526_ = lean_ctor_get(v_cfg_504_, 18);
v_keywords_527_ = lean_ctor_get(v_cfg_504_, 19);
v_homepage_528_ = lean_ctor_get(v_cfg_504_, 20);
v_license_529_ = lean_ctor_get(v_cfg_504_, 21);
v_licenseFiles_530_ = lean_ctor_get(v_cfg_504_, 22);
v_readmeFile_531_ = lean_ctor_get(v_cfg_504_, 23);
v_reservoir_532_ = lean_ctor_get_uint8(v_cfg_504_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_533_ = lean_ctor_get(v_cfg_504_, 24);
v_restoreAllArtifacts_x3f_534_ = lean_ctor_get(v_cfg_504_, 25);
v_libPrefixOnWindows_535_ = lean_ctor_get_uint8(v_cfg_504_, sizeof(void*)*28 + 4);
v_allowImportAll_536_ = lean_ctor_get_uint8(v_cfg_504_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_537_ = lean_ctor_get(v_cfg_504_, 26);
v_checks_538_ = lean_ctor_get(v_cfg_504_, 27);
v_fixedToolchain_539_ = lean_ctor_get_uint8(v_cfg_504_, sizeof(void*)*28 + 6);
v_isSharedCheck_547_ = !lean_is_exclusive(v_cfg_504_);
if (v_isSharedCheck_547_ == 0)
{
v___x_541_ = v_cfg_504_;
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_checks_538_);
lean_inc(v_builtinLint_x3f_537_);
lean_inc(v_restoreAllArtifacts_x3f_534_);
lean_inc(v_enableArtifactCache_x3f_533_);
lean_inc(v_readmeFile_531_);
lean_inc(v_licenseFiles_530_);
lean_inc(v_license_529_);
lean_inc(v_homepage_528_);
lean_inc(v_keywords_527_);
lean_inc(v_description_526_);
lean_inc(v_versionTags_525_);
lean_inc(v_version_524_);
lean_inc(v_lintDriverArgs_523_);
lean_inc(v_lintDriver_522_);
lean_inc(v_testDriverArgs_521_);
lean_inc(v_testDriver_520_);
lean_inc(v_buildArchive_518_);
lean_inc(v_releaseRepo_517_);
lean_inc(v_irDir_516_);
lean_inc(v_binDir_515_);
lean_inc(v_nativeLibDir_514_);
lean_inc(v_leanLibDir_513_);
lean_inc(v_buildDir_512_);
lean_inc(v_srcDir_511_);
lean_inc(v_moreGlobalServerArgs_510_);
lean_inc(v_extraDepTargets_508_);
lean_inc(v_toLeanConfig_506_);
lean_inc(v_toWorkspaceConfig_505_);
lean_dec(v_cfg_504_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = lean_apply_1(v_f_503_, v_moreGlobalServerArgs_510_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 3, v___x_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_toWorkspaceConfig_505_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_toLeanConfig_506_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_extraDepTargets_508_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_srcDir_511_);
lean_ctor_set(v_reuseFailAlloc_546_, 5, v_buildDir_512_);
lean_ctor_set(v_reuseFailAlloc_546_, 6, v_leanLibDir_513_);
lean_ctor_set(v_reuseFailAlloc_546_, 7, v_nativeLibDir_514_);
lean_ctor_set(v_reuseFailAlloc_546_, 8, v_binDir_515_);
lean_ctor_set(v_reuseFailAlloc_546_, 9, v_irDir_516_);
lean_ctor_set(v_reuseFailAlloc_546_, 10, v_releaseRepo_517_);
lean_ctor_set(v_reuseFailAlloc_546_, 11, v_buildArchive_518_);
lean_ctor_set(v_reuseFailAlloc_546_, 12, v_testDriver_520_);
lean_ctor_set(v_reuseFailAlloc_546_, 13, v_testDriverArgs_521_);
lean_ctor_set(v_reuseFailAlloc_546_, 14, v_lintDriver_522_);
lean_ctor_set(v_reuseFailAlloc_546_, 15, v_lintDriverArgs_523_);
lean_ctor_set(v_reuseFailAlloc_546_, 16, v_version_524_);
lean_ctor_set(v_reuseFailAlloc_546_, 17, v_versionTags_525_);
lean_ctor_set(v_reuseFailAlloc_546_, 18, v_description_526_);
lean_ctor_set(v_reuseFailAlloc_546_, 19, v_keywords_527_);
lean_ctor_set(v_reuseFailAlloc_546_, 20, v_homepage_528_);
lean_ctor_set(v_reuseFailAlloc_546_, 21, v_license_529_);
lean_ctor_set(v_reuseFailAlloc_546_, 22, v_licenseFiles_530_);
lean_ctor_set(v_reuseFailAlloc_546_, 23, v_readmeFile_531_);
lean_ctor_set(v_reuseFailAlloc_546_, 24, v_enableArtifactCache_x3f_533_);
lean_ctor_set(v_reuseFailAlloc_546_, 25, v_restoreAllArtifacts_x3f_534_);
lean_ctor_set(v_reuseFailAlloc_546_, 26, v_builtinLint_x3f_537_);
lean_ctor_set(v_reuseFailAlloc_546_, 27, v_checks_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*28, v_bootstrap_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*28 + 1, v_precompileModules_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*28 + 2, v_preferReleaseBuild_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*28 + 3, v_reservoir_532_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*28 + 5, v_allowImportAll_536_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*28 + 6, v_fixedToolchain_539_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3(lean_object* v_x_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3___closed__0));
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3___boxed(lean_object* v_x_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3(v_x_552_);
lean_dec_ref(v_x_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg(){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__4));
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___boxed(lean_object* v___dummy_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg();
return v_res_566_;
}
}
static lean_object* _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0(void){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg();
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object* v_p_568_, lean_object* v_n_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object* v_p_571_, lean_object* v_n_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_571_, v_n_572_);
lean_dec(v_n_572_);
lean_dec(v_p_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg___boxed(lean_object* v___dummy_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg();
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object* v_p_578_, lean_object* v_n_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object* v_p_581_, lean_object* v_n_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(v_p_581_, v_n_582_);
lean_dec(v_n_582_);
lean_dec(v_p_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg___boxed(lean_object* v___dummy_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg();
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object* v_p_588_, lean_object* v_n_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object* v_p_591_, lean_object* v_n_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lake_PackageConfig_moreServerArgs_instConfigField(v_p_591_, v_n_592_);
lean_dec(v_n_592_);
lean_dec(v_p_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__0(lean_object* v_cfg_594_){
_start:
{
lean_object* v_srcDir_595_; 
v_srcDir_595_ = lean_ctor_get(v_cfg_594_, 4);
lean_inc_ref(v_srcDir_595_);
return v_srcDir_595_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lake_PackageConfig_srcDir___proj___redArg___lam__0(v_cfg_596_);
lean_dec_ref(v_cfg_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__1(lean_object* v_val_598_, lean_object* v_cfg_599_){
_start:
{
lean_object* v_toWorkspaceConfig_600_; lean_object* v_toLeanConfig_601_; uint8_t v_bootstrap_602_; lean_object* v_extraDepTargets_603_; uint8_t v_precompileModules_604_; lean_object* v_moreGlobalServerArgs_605_; lean_object* v_buildDir_606_; lean_object* v_leanLibDir_607_; lean_object* v_nativeLibDir_608_; lean_object* v_binDir_609_; lean_object* v_irDir_610_; lean_object* v_releaseRepo_611_; lean_object* v_buildArchive_612_; uint8_t v_preferReleaseBuild_613_; lean_object* v_testDriver_614_; lean_object* v_testDriverArgs_615_; lean_object* v_lintDriver_616_; lean_object* v_lintDriverArgs_617_; lean_object* v_version_618_; lean_object* v_versionTags_619_; lean_object* v_description_620_; lean_object* v_keywords_621_; lean_object* v_homepage_622_; lean_object* v_license_623_; lean_object* v_licenseFiles_624_; lean_object* v_readmeFile_625_; uint8_t v_reservoir_626_; lean_object* v_enableArtifactCache_x3f_627_; lean_object* v_restoreAllArtifacts_x3f_628_; uint8_t v_libPrefixOnWindows_629_; uint8_t v_allowImportAll_630_; lean_object* v_builtinLint_x3f_631_; lean_object* v_checks_632_; uint8_t v_fixedToolchain_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_toWorkspaceConfig_600_ = lean_ctor_get(v_cfg_599_, 0);
v_toLeanConfig_601_ = lean_ctor_get(v_cfg_599_, 1);
v_bootstrap_602_ = lean_ctor_get_uint8(v_cfg_599_, sizeof(void*)*28);
v_extraDepTargets_603_ = lean_ctor_get(v_cfg_599_, 2);
v_precompileModules_604_ = lean_ctor_get_uint8(v_cfg_599_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_605_ = lean_ctor_get(v_cfg_599_, 3);
v_buildDir_606_ = lean_ctor_get(v_cfg_599_, 5);
v_leanLibDir_607_ = lean_ctor_get(v_cfg_599_, 6);
v_nativeLibDir_608_ = lean_ctor_get(v_cfg_599_, 7);
v_binDir_609_ = lean_ctor_get(v_cfg_599_, 8);
v_irDir_610_ = lean_ctor_get(v_cfg_599_, 9);
v_releaseRepo_611_ = lean_ctor_get(v_cfg_599_, 10);
v_buildArchive_612_ = lean_ctor_get(v_cfg_599_, 11);
v_preferReleaseBuild_613_ = lean_ctor_get_uint8(v_cfg_599_, sizeof(void*)*28 + 2);
v_testDriver_614_ = lean_ctor_get(v_cfg_599_, 12);
v_testDriverArgs_615_ = lean_ctor_get(v_cfg_599_, 13);
v_lintDriver_616_ = lean_ctor_get(v_cfg_599_, 14);
v_lintDriverArgs_617_ = lean_ctor_get(v_cfg_599_, 15);
v_version_618_ = lean_ctor_get(v_cfg_599_, 16);
v_versionTags_619_ = lean_ctor_get(v_cfg_599_, 17);
v_description_620_ = lean_ctor_get(v_cfg_599_, 18);
v_keywords_621_ = lean_ctor_get(v_cfg_599_, 19);
v_homepage_622_ = lean_ctor_get(v_cfg_599_, 20);
v_license_623_ = lean_ctor_get(v_cfg_599_, 21);
v_licenseFiles_624_ = lean_ctor_get(v_cfg_599_, 22);
v_readmeFile_625_ = lean_ctor_get(v_cfg_599_, 23);
v_reservoir_626_ = lean_ctor_get_uint8(v_cfg_599_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_627_ = lean_ctor_get(v_cfg_599_, 24);
v_restoreAllArtifacts_x3f_628_ = lean_ctor_get(v_cfg_599_, 25);
v_libPrefixOnWindows_629_ = lean_ctor_get_uint8(v_cfg_599_, sizeof(void*)*28 + 4);
v_allowImportAll_630_ = lean_ctor_get_uint8(v_cfg_599_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_631_ = lean_ctor_get(v_cfg_599_, 26);
v_checks_632_ = lean_ctor_get(v_cfg_599_, 27);
v_fixedToolchain_633_ = lean_ctor_get_uint8(v_cfg_599_, sizeof(void*)*28 + 6);
v_isSharedCheck_640_ = !lean_is_exclusive(v_cfg_599_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v_cfg_599_, 4);
lean_dec(v_unused_641_);
v___x_635_ = v_cfg_599_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_checks_632_);
lean_inc(v_builtinLint_x3f_631_);
lean_inc(v_restoreAllArtifacts_x3f_628_);
lean_inc(v_enableArtifactCache_x3f_627_);
lean_inc(v_readmeFile_625_);
lean_inc(v_licenseFiles_624_);
lean_inc(v_license_623_);
lean_inc(v_homepage_622_);
lean_inc(v_keywords_621_);
lean_inc(v_description_620_);
lean_inc(v_versionTags_619_);
lean_inc(v_version_618_);
lean_inc(v_lintDriverArgs_617_);
lean_inc(v_lintDriver_616_);
lean_inc(v_testDriverArgs_615_);
lean_inc(v_testDriver_614_);
lean_inc(v_buildArchive_612_);
lean_inc(v_releaseRepo_611_);
lean_inc(v_irDir_610_);
lean_inc(v_binDir_609_);
lean_inc(v_nativeLibDir_608_);
lean_inc(v_leanLibDir_607_);
lean_inc(v_buildDir_606_);
lean_inc(v_moreGlobalServerArgs_605_);
lean_inc(v_extraDepTargets_603_);
lean_inc(v_toLeanConfig_601_);
lean_inc(v_toWorkspaceConfig_600_);
lean_dec(v_cfg_599_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 4, v_val_598_);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_toWorkspaceConfig_600_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_toLeanConfig_601_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_extraDepTargets_603_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_moreGlobalServerArgs_605_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_val_598_);
lean_ctor_set(v_reuseFailAlloc_639_, 5, v_buildDir_606_);
lean_ctor_set(v_reuseFailAlloc_639_, 6, v_leanLibDir_607_);
lean_ctor_set(v_reuseFailAlloc_639_, 7, v_nativeLibDir_608_);
lean_ctor_set(v_reuseFailAlloc_639_, 8, v_binDir_609_);
lean_ctor_set(v_reuseFailAlloc_639_, 9, v_irDir_610_);
lean_ctor_set(v_reuseFailAlloc_639_, 10, v_releaseRepo_611_);
lean_ctor_set(v_reuseFailAlloc_639_, 11, v_buildArchive_612_);
lean_ctor_set(v_reuseFailAlloc_639_, 12, v_testDriver_614_);
lean_ctor_set(v_reuseFailAlloc_639_, 13, v_testDriverArgs_615_);
lean_ctor_set(v_reuseFailAlloc_639_, 14, v_lintDriver_616_);
lean_ctor_set(v_reuseFailAlloc_639_, 15, v_lintDriverArgs_617_);
lean_ctor_set(v_reuseFailAlloc_639_, 16, v_version_618_);
lean_ctor_set(v_reuseFailAlloc_639_, 17, v_versionTags_619_);
lean_ctor_set(v_reuseFailAlloc_639_, 18, v_description_620_);
lean_ctor_set(v_reuseFailAlloc_639_, 19, v_keywords_621_);
lean_ctor_set(v_reuseFailAlloc_639_, 20, v_homepage_622_);
lean_ctor_set(v_reuseFailAlloc_639_, 21, v_license_623_);
lean_ctor_set(v_reuseFailAlloc_639_, 22, v_licenseFiles_624_);
lean_ctor_set(v_reuseFailAlloc_639_, 23, v_readmeFile_625_);
lean_ctor_set(v_reuseFailAlloc_639_, 24, v_enableArtifactCache_x3f_627_);
lean_ctor_set(v_reuseFailAlloc_639_, 25, v_restoreAllArtifacts_x3f_628_);
lean_ctor_set(v_reuseFailAlloc_639_, 26, v_builtinLint_x3f_631_);
lean_ctor_set(v_reuseFailAlloc_639_, 27, v_checks_632_);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, sizeof(void*)*28, v_bootstrap_602_);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, sizeof(void*)*28 + 1, v_precompileModules_604_);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, sizeof(void*)*28 + 2, v_preferReleaseBuild_613_);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, sizeof(void*)*28 + 3, v_reservoir_626_);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_629_);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, sizeof(void*)*28 + 5, v_allowImportAll_630_);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, sizeof(void*)*28 + 6, v_fixedToolchain_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__2(lean_object* v_f_642_, lean_object* v_cfg_643_){
_start:
{
lean_object* v_toWorkspaceConfig_644_; lean_object* v_toLeanConfig_645_; uint8_t v_bootstrap_646_; lean_object* v_extraDepTargets_647_; uint8_t v_precompileModules_648_; lean_object* v_moreGlobalServerArgs_649_; lean_object* v_srcDir_650_; lean_object* v_buildDir_651_; lean_object* v_leanLibDir_652_; lean_object* v_nativeLibDir_653_; lean_object* v_binDir_654_; lean_object* v_irDir_655_; lean_object* v_releaseRepo_656_; lean_object* v_buildArchive_657_; uint8_t v_preferReleaseBuild_658_; lean_object* v_testDriver_659_; lean_object* v_testDriverArgs_660_; lean_object* v_lintDriver_661_; lean_object* v_lintDriverArgs_662_; lean_object* v_version_663_; lean_object* v_versionTags_664_; lean_object* v_description_665_; lean_object* v_keywords_666_; lean_object* v_homepage_667_; lean_object* v_license_668_; lean_object* v_licenseFiles_669_; lean_object* v_readmeFile_670_; uint8_t v_reservoir_671_; lean_object* v_enableArtifactCache_x3f_672_; lean_object* v_restoreAllArtifacts_x3f_673_; uint8_t v_libPrefixOnWindows_674_; uint8_t v_allowImportAll_675_; lean_object* v_builtinLint_x3f_676_; lean_object* v_checks_677_; uint8_t v_fixedToolchain_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_686_; 
v_toWorkspaceConfig_644_ = lean_ctor_get(v_cfg_643_, 0);
v_toLeanConfig_645_ = lean_ctor_get(v_cfg_643_, 1);
v_bootstrap_646_ = lean_ctor_get_uint8(v_cfg_643_, sizeof(void*)*28);
v_extraDepTargets_647_ = lean_ctor_get(v_cfg_643_, 2);
v_precompileModules_648_ = lean_ctor_get_uint8(v_cfg_643_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_649_ = lean_ctor_get(v_cfg_643_, 3);
v_srcDir_650_ = lean_ctor_get(v_cfg_643_, 4);
v_buildDir_651_ = lean_ctor_get(v_cfg_643_, 5);
v_leanLibDir_652_ = lean_ctor_get(v_cfg_643_, 6);
v_nativeLibDir_653_ = lean_ctor_get(v_cfg_643_, 7);
v_binDir_654_ = lean_ctor_get(v_cfg_643_, 8);
v_irDir_655_ = lean_ctor_get(v_cfg_643_, 9);
v_releaseRepo_656_ = lean_ctor_get(v_cfg_643_, 10);
v_buildArchive_657_ = lean_ctor_get(v_cfg_643_, 11);
v_preferReleaseBuild_658_ = lean_ctor_get_uint8(v_cfg_643_, sizeof(void*)*28 + 2);
v_testDriver_659_ = lean_ctor_get(v_cfg_643_, 12);
v_testDriverArgs_660_ = lean_ctor_get(v_cfg_643_, 13);
v_lintDriver_661_ = lean_ctor_get(v_cfg_643_, 14);
v_lintDriverArgs_662_ = lean_ctor_get(v_cfg_643_, 15);
v_version_663_ = lean_ctor_get(v_cfg_643_, 16);
v_versionTags_664_ = lean_ctor_get(v_cfg_643_, 17);
v_description_665_ = lean_ctor_get(v_cfg_643_, 18);
v_keywords_666_ = lean_ctor_get(v_cfg_643_, 19);
v_homepage_667_ = lean_ctor_get(v_cfg_643_, 20);
v_license_668_ = lean_ctor_get(v_cfg_643_, 21);
v_licenseFiles_669_ = lean_ctor_get(v_cfg_643_, 22);
v_readmeFile_670_ = lean_ctor_get(v_cfg_643_, 23);
v_reservoir_671_ = lean_ctor_get_uint8(v_cfg_643_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_672_ = lean_ctor_get(v_cfg_643_, 24);
v_restoreAllArtifacts_x3f_673_ = lean_ctor_get(v_cfg_643_, 25);
v_libPrefixOnWindows_674_ = lean_ctor_get_uint8(v_cfg_643_, sizeof(void*)*28 + 4);
v_allowImportAll_675_ = lean_ctor_get_uint8(v_cfg_643_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_676_ = lean_ctor_get(v_cfg_643_, 26);
v_checks_677_ = lean_ctor_get(v_cfg_643_, 27);
v_fixedToolchain_678_ = lean_ctor_get_uint8(v_cfg_643_, sizeof(void*)*28 + 6);
v_isSharedCheck_686_ = !lean_is_exclusive(v_cfg_643_);
if (v_isSharedCheck_686_ == 0)
{
v___x_680_ = v_cfg_643_;
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_checks_677_);
lean_inc(v_builtinLint_x3f_676_);
lean_inc(v_restoreAllArtifacts_x3f_673_);
lean_inc(v_enableArtifactCache_x3f_672_);
lean_inc(v_readmeFile_670_);
lean_inc(v_licenseFiles_669_);
lean_inc(v_license_668_);
lean_inc(v_homepage_667_);
lean_inc(v_keywords_666_);
lean_inc(v_description_665_);
lean_inc(v_versionTags_664_);
lean_inc(v_version_663_);
lean_inc(v_lintDriverArgs_662_);
lean_inc(v_lintDriver_661_);
lean_inc(v_testDriverArgs_660_);
lean_inc(v_testDriver_659_);
lean_inc(v_buildArchive_657_);
lean_inc(v_releaseRepo_656_);
lean_inc(v_irDir_655_);
lean_inc(v_binDir_654_);
lean_inc(v_nativeLibDir_653_);
lean_inc(v_leanLibDir_652_);
lean_inc(v_buildDir_651_);
lean_inc(v_srcDir_650_);
lean_inc(v_moreGlobalServerArgs_649_);
lean_inc(v_extraDepTargets_647_);
lean_inc(v_toLeanConfig_645_);
lean_inc(v_toWorkspaceConfig_644_);
lean_dec(v_cfg_643_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = lean_apply_1(v_f_642_, v_srcDir_650_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 4, v___x_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_toWorkspaceConfig_644_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_toLeanConfig_645_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_extraDepTargets_647_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_moreGlobalServerArgs_649_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_685_, 5, v_buildDir_651_);
lean_ctor_set(v_reuseFailAlloc_685_, 6, v_leanLibDir_652_);
lean_ctor_set(v_reuseFailAlloc_685_, 7, v_nativeLibDir_653_);
lean_ctor_set(v_reuseFailAlloc_685_, 8, v_binDir_654_);
lean_ctor_set(v_reuseFailAlloc_685_, 9, v_irDir_655_);
lean_ctor_set(v_reuseFailAlloc_685_, 10, v_releaseRepo_656_);
lean_ctor_set(v_reuseFailAlloc_685_, 11, v_buildArchive_657_);
lean_ctor_set(v_reuseFailAlloc_685_, 12, v_testDriver_659_);
lean_ctor_set(v_reuseFailAlloc_685_, 13, v_testDriverArgs_660_);
lean_ctor_set(v_reuseFailAlloc_685_, 14, v_lintDriver_661_);
lean_ctor_set(v_reuseFailAlloc_685_, 15, v_lintDriverArgs_662_);
lean_ctor_set(v_reuseFailAlloc_685_, 16, v_version_663_);
lean_ctor_set(v_reuseFailAlloc_685_, 17, v_versionTags_664_);
lean_ctor_set(v_reuseFailAlloc_685_, 18, v_description_665_);
lean_ctor_set(v_reuseFailAlloc_685_, 19, v_keywords_666_);
lean_ctor_set(v_reuseFailAlloc_685_, 20, v_homepage_667_);
lean_ctor_set(v_reuseFailAlloc_685_, 21, v_license_668_);
lean_ctor_set(v_reuseFailAlloc_685_, 22, v_licenseFiles_669_);
lean_ctor_set(v_reuseFailAlloc_685_, 23, v_readmeFile_670_);
lean_ctor_set(v_reuseFailAlloc_685_, 24, v_enableArtifactCache_x3f_672_);
lean_ctor_set(v_reuseFailAlloc_685_, 25, v_restoreAllArtifacts_x3f_673_);
lean_ctor_set(v_reuseFailAlloc_685_, 26, v_builtinLint_x3f_676_);
lean_ctor_set(v_reuseFailAlloc_685_, 27, v_checks_677_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*28, v_bootstrap_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*28 + 1, v_precompileModules_648_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*28 + 2, v_preferReleaseBuild_658_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*28 + 3, v_reservoir_671_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_674_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*28 + 5, v_allowImportAll_675_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*28 + 6, v_fixedToolchain_678_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__3(lean_object* v_x_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__1));
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__3___boxed(lean_object* v_x_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lake_PackageConfig_srcDir___proj___redArg___lam__3(v_x_689_);
lean_dec_ref(v_x_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg(){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___redArg___closed__4));
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___boxed(lean_object* v___dummy_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lake_PackageConfig_srcDir___proj___redArg();
return v_res_703_;
}
}
static lean_object* _init_l_Lake_PackageConfig_srcDir___proj___closed__0(void){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lake_PackageConfig_srcDir___proj___redArg();
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object* v_p_705_, lean_object* v_n_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_obj_once(&l_Lake_PackageConfig_srcDir___proj___closed__0, &l_Lake_PackageConfig_srcDir___proj___closed__0_once, _init_l_Lake_PackageConfig_srcDir___proj___closed__0);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object* v_p_708_, lean_object* v_n_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lake_PackageConfig_srcDir___proj(v_p_708_, v_n_709_);
lean_dec(v_n_709_);
lean_dec(v_p_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = lean_obj_once(&l_Lake_PackageConfig_srcDir___proj___closed__0, &l_Lake_PackageConfig_srcDir___proj___closed__0_once, _init_l_Lake_PackageConfig_srcDir___proj___closed__0);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___redArg___boxed(lean_object* v___dummy_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lake_PackageConfig_srcDir_instConfigField___redArg();
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object* v_p_715_, lean_object* v_n_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_obj_once(&l_Lake_PackageConfig_srcDir___proj___closed__0, &l_Lake_PackageConfig_srcDir___proj___closed__0_once, _init_l_Lake_PackageConfig_srcDir___proj___closed__0);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object* v_p_718_, lean_object* v_n_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lake_PackageConfig_srcDir_instConfigField(v_p_718_, v_n_719_);
lean_dec(v_n_719_);
lean_dec(v_p_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__0(lean_object* v_cfg_721_){
_start:
{
lean_object* v_buildDir_722_; 
v_buildDir_722_ = lean_ctor_get(v_cfg_721_, 5);
lean_inc_ref(v_buildDir_722_);
return v_buildDir_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lake_PackageConfig_buildDir___proj___redArg___lam__0(v_cfg_723_);
lean_dec_ref(v_cfg_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__1(lean_object* v_val_725_, lean_object* v_cfg_726_){
_start:
{
lean_object* v_toWorkspaceConfig_727_; lean_object* v_toLeanConfig_728_; uint8_t v_bootstrap_729_; lean_object* v_extraDepTargets_730_; uint8_t v_precompileModules_731_; lean_object* v_moreGlobalServerArgs_732_; lean_object* v_srcDir_733_; lean_object* v_leanLibDir_734_; lean_object* v_nativeLibDir_735_; lean_object* v_binDir_736_; lean_object* v_irDir_737_; lean_object* v_releaseRepo_738_; lean_object* v_buildArchive_739_; uint8_t v_preferReleaseBuild_740_; lean_object* v_testDriver_741_; lean_object* v_testDriverArgs_742_; lean_object* v_lintDriver_743_; lean_object* v_lintDriverArgs_744_; lean_object* v_version_745_; lean_object* v_versionTags_746_; lean_object* v_description_747_; lean_object* v_keywords_748_; lean_object* v_homepage_749_; lean_object* v_license_750_; lean_object* v_licenseFiles_751_; lean_object* v_readmeFile_752_; uint8_t v_reservoir_753_; lean_object* v_enableArtifactCache_x3f_754_; lean_object* v_restoreAllArtifacts_x3f_755_; uint8_t v_libPrefixOnWindows_756_; uint8_t v_allowImportAll_757_; lean_object* v_builtinLint_x3f_758_; lean_object* v_checks_759_; uint8_t v_fixedToolchain_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_toWorkspaceConfig_727_ = lean_ctor_get(v_cfg_726_, 0);
v_toLeanConfig_728_ = lean_ctor_get(v_cfg_726_, 1);
v_bootstrap_729_ = lean_ctor_get_uint8(v_cfg_726_, sizeof(void*)*28);
v_extraDepTargets_730_ = lean_ctor_get(v_cfg_726_, 2);
v_precompileModules_731_ = lean_ctor_get_uint8(v_cfg_726_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_732_ = lean_ctor_get(v_cfg_726_, 3);
v_srcDir_733_ = lean_ctor_get(v_cfg_726_, 4);
v_leanLibDir_734_ = lean_ctor_get(v_cfg_726_, 6);
v_nativeLibDir_735_ = lean_ctor_get(v_cfg_726_, 7);
v_binDir_736_ = lean_ctor_get(v_cfg_726_, 8);
v_irDir_737_ = lean_ctor_get(v_cfg_726_, 9);
v_releaseRepo_738_ = lean_ctor_get(v_cfg_726_, 10);
v_buildArchive_739_ = lean_ctor_get(v_cfg_726_, 11);
v_preferReleaseBuild_740_ = lean_ctor_get_uint8(v_cfg_726_, sizeof(void*)*28 + 2);
v_testDriver_741_ = lean_ctor_get(v_cfg_726_, 12);
v_testDriverArgs_742_ = lean_ctor_get(v_cfg_726_, 13);
v_lintDriver_743_ = lean_ctor_get(v_cfg_726_, 14);
v_lintDriverArgs_744_ = lean_ctor_get(v_cfg_726_, 15);
v_version_745_ = lean_ctor_get(v_cfg_726_, 16);
v_versionTags_746_ = lean_ctor_get(v_cfg_726_, 17);
v_description_747_ = lean_ctor_get(v_cfg_726_, 18);
v_keywords_748_ = lean_ctor_get(v_cfg_726_, 19);
v_homepage_749_ = lean_ctor_get(v_cfg_726_, 20);
v_license_750_ = lean_ctor_get(v_cfg_726_, 21);
v_licenseFiles_751_ = lean_ctor_get(v_cfg_726_, 22);
v_readmeFile_752_ = lean_ctor_get(v_cfg_726_, 23);
v_reservoir_753_ = lean_ctor_get_uint8(v_cfg_726_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_754_ = lean_ctor_get(v_cfg_726_, 24);
v_restoreAllArtifacts_x3f_755_ = lean_ctor_get(v_cfg_726_, 25);
v_libPrefixOnWindows_756_ = lean_ctor_get_uint8(v_cfg_726_, sizeof(void*)*28 + 4);
v_allowImportAll_757_ = lean_ctor_get_uint8(v_cfg_726_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_758_ = lean_ctor_get(v_cfg_726_, 26);
v_checks_759_ = lean_ctor_get(v_cfg_726_, 27);
v_fixedToolchain_760_ = lean_ctor_get_uint8(v_cfg_726_, sizeof(void*)*28 + 6);
v_isSharedCheck_767_ = !lean_is_exclusive(v_cfg_726_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v_cfg_726_, 5);
lean_dec(v_unused_768_);
v___x_762_ = v_cfg_726_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_checks_759_);
lean_inc(v_builtinLint_x3f_758_);
lean_inc(v_restoreAllArtifacts_x3f_755_);
lean_inc(v_enableArtifactCache_x3f_754_);
lean_inc(v_readmeFile_752_);
lean_inc(v_licenseFiles_751_);
lean_inc(v_license_750_);
lean_inc(v_homepage_749_);
lean_inc(v_keywords_748_);
lean_inc(v_description_747_);
lean_inc(v_versionTags_746_);
lean_inc(v_version_745_);
lean_inc(v_lintDriverArgs_744_);
lean_inc(v_lintDriver_743_);
lean_inc(v_testDriverArgs_742_);
lean_inc(v_testDriver_741_);
lean_inc(v_buildArchive_739_);
lean_inc(v_releaseRepo_738_);
lean_inc(v_irDir_737_);
lean_inc(v_binDir_736_);
lean_inc(v_nativeLibDir_735_);
lean_inc(v_leanLibDir_734_);
lean_inc(v_srcDir_733_);
lean_inc(v_moreGlobalServerArgs_732_);
lean_inc(v_extraDepTargets_730_);
lean_inc(v_toLeanConfig_728_);
lean_inc(v_toWorkspaceConfig_727_);
lean_dec(v_cfg_726_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 5, v_val_725_);
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_toWorkspaceConfig_727_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_toLeanConfig_728_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v_extraDepTargets_730_);
lean_ctor_set(v_reuseFailAlloc_766_, 3, v_moreGlobalServerArgs_732_);
lean_ctor_set(v_reuseFailAlloc_766_, 4, v_srcDir_733_);
lean_ctor_set(v_reuseFailAlloc_766_, 5, v_val_725_);
lean_ctor_set(v_reuseFailAlloc_766_, 6, v_leanLibDir_734_);
lean_ctor_set(v_reuseFailAlloc_766_, 7, v_nativeLibDir_735_);
lean_ctor_set(v_reuseFailAlloc_766_, 8, v_binDir_736_);
lean_ctor_set(v_reuseFailAlloc_766_, 9, v_irDir_737_);
lean_ctor_set(v_reuseFailAlloc_766_, 10, v_releaseRepo_738_);
lean_ctor_set(v_reuseFailAlloc_766_, 11, v_buildArchive_739_);
lean_ctor_set(v_reuseFailAlloc_766_, 12, v_testDriver_741_);
lean_ctor_set(v_reuseFailAlloc_766_, 13, v_testDriverArgs_742_);
lean_ctor_set(v_reuseFailAlloc_766_, 14, v_lintDriver_743_);
lean_ctor_set(v_reuseFailAlloc_766_, 15, v_lintDriverArgs_744_);
lean_ctor_set(v_reuseFailAlloc_766_, 16, v_version_745_);
lean_ctor_set(v_reuseFailAlloc_766_, 17, v_versionTags_746_);
lean_ctor_set(v_reuseFailAlloc_766_, 18, v_description_747_);
lean_ctor_set(v_reuseFailAlloc_766_, 19, v_keywords_748_);
lean_ctor_set(v_reuseFailAlloc_766_, 20, v_homepage_749_);
lean_ctor_set(v_reuseFailAlloc_766_, 21, v_license_750_);
lean_ctor_set(v_reuseFailAlloc_766_, 22, v_licenseFiles_751_);
lean_ctor_set(v_reuseFailAlloc_766_, 23, v_readmeFile_752_);
lean_ctor_set(v_reuseFailAlloc_766_, 24, v_enableArtifactCache_x3f_754_);
lean_ctor_set(v_reuseFailAlloc_766_, 25, v_restoreAllArtifacts_x3f_755_);
lean_ctor_set(v_reuseFailAlloc_766_, 26, v_builtinLint_x3f_758_);
lean_ctor_set(v_reuseFailAlloc_766_, 27, v_checks_759_);
lean_ctor_set_uint8(v_reuseFailAlloc_766_, sizeof(void*)*28, v_bootstrap_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_766_, sizeof(void*)*28 + 1, v_precompileModules_731_);
lean_ctor_set_uint8(v_reuseFailAlloc_766_, sizeof(void*)*28 + 2, v_preferReleaseBuild_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_766_, sizeof(void*)*28 + 3, v_reservoir_753_);
lean_ctor_set_uint8(v_reuseFailAlloc_766_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_756_);
lean_ctor_set_uint8(v_reuseFailAlloc_766_, sizeof(void*)*28 + 5, v_allowImportAll_757_);
lean_ctor_set_uint8(v_reuseFailAlloc_766_, sizeof(void*)*28 + 6, v_fixedToolchain_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__2(lean_object* v_f_769_, lean_object* v_cfg_770_){
_start:
{
lean_object* v_toWorkspaceConfig_771_; lean_object* v_toLeanConfig_772_; uint8_t v_bootstrap_773_; lean_object* v_extraDepTargets_774_; uint8_t v_precompileModules_775_; lean_object* v_moreGlobalServerArgs_776_; lean_object* v_srcDir_777_; lean_object* v_buildDir_778_; lean_object* v_leanLibDir_779_; lean_object* v_nativeLibDir_780_; lean_object* v_binDir_781_; lean_object* v_irDir_782_; lean_object* v_releaseRepo_783_; lean_object* v_buildArchive_784_; uint8_t v_preferReleaseBuild_785_; lean_object* v_testDriver_786_; lean_object* v_testDriverArgs_787_; lean_object* v_lintDriver_788_; lean_object* v_lintDriverArgs_789_; lean_object* v_version_790_; lean_object* v_versionTags_791_; lean_object* v_description_792_; lean_object* v_keywords_793_; lean_object* v_homepage_794_; lean_object* v_license_795_; lean_object* v_licenseFiles_796_; lean_object* v_readmeFile_797_; uint8_t v_reservoir_798_; lean_object* v_enableArtifactCache_x3f_799_; lean_object* v_restoreAllArtifacts_x3f_800_; uint8_t v_libPrefixOnWindows_801_; uint8_t v_allowImportAll_802_; lean_object* v_builtinLint_x3f_803_; lean_object* v_checks_804_; uint8_t v_fixedToolchain_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_toWorkspaceConfig_771_ = lean_ctor_get(v_cfg_770_, 0);
v_toLeanConfig_772_ = lean_ctor_get(v_cfg_770_, 1);
v_bootstrap_773_ = lean_ctor_get_uint8(v_cfg_770_, sizeof(void*)*28);
v_extraDepTargets_774_ = lean_ctor_get(v_cfg_770_, 2);
v_precompileModules_775_ = lean_ctor_get_uint8(v_cfg_770_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_776_ = lean_ctor_get(v_cfg_770_, 3);
v_srcDir_777_ = lean_ctor_get(v_cfg_770_, 4);
v_buildDir_778_ = lean_ctor_get(v_cfg_770_, 5);
v_leanLibDir_779_ = lean_ctor_get(v_cfg_770_, 6);
v_nativeLibDir_780_ = lean_ctor_get(v_cfg_770_, 7);
v_binDir_781_ = lean_ctor_get(v_cfg_770_, 8);
v_irDir_782_ = lean_ctor_get(v_cfg_770_, 9);
v_releaseRepo_783_ = lean_ctor_get(v_cfg_770_, 10);
v_buildArchive_784_ = lean_ctor_get(v_cfg_770_, 11);
v_preferReleaseBuild_785_ = lean_ctor_get_uint8(v_cfg_770_, sizeof(void*)*28 + 2);
v_testDriver_786_ = lean_ctor_get(v_cfg_770_, 12);
v_testDriverArgs_787_ = lean_ctor_get(v_cfg_770_, 13);
v_lintDriver_788_ = lean_ctor_get(v_cfg_770_, 14);
v_lintDriverArgs_789_ = lean_ctor_get(v_cfg_770_, 15);
v_version_790_ = lean_ctor_get(v_cfg_770_, 16);
v_versionTags_791_ = lean_ctor_get(v_cfg_770_, 17);
v_description_792_ = lean_ctor_get(v_cfg_770_, 18);
v_keywords_793_ = lean_ctor_get(v_cfg_770_, 19);
v_homepage_794_ = lean_ctor_get(v_cfg_770_, 20);
v_license_795_ = lean_ctor_get(v_cfg_770_, 21);
v_licenseFiles_796_ = lean_ctor_get(v_cfg_770_, 22);
v_readmeFile_797_ = lean_ctor_get(v_cfg_770_, 23);
v_reservoir_798_ = lean_ctor_get_uint8(v_cfg_770_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_799_ = lean_ctor_get(v_cfg_770_, 24);
v_restoreAllArtifacts_x3f_800_ = lean_ctor_get(v_cfg_770_, 25);
v_libPrefixOnWindows_801_ = lean_ctor_get_uint8(v_cfg_770_, sizeof(void*)*28 + 4);
v_allowImportAll_802_ = lean_ctor_get_uint8(v_cfg_770_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_803_ = lean_ctor_get(v_cfg_770_, 26);
v_checks_804_ = lean_ctor_get(v_cfg_770_, 27);
v_fixedToolchain_805_ = lean_ctor_get_uint8(v_cfg_770_, sizeof(void*)*28 + 6);
v_isSharedCheck_813_ = !lean_is_exclusive(v_cfg_770_);
if (v_isSharedCheck_813_ == 0)
{
v___x_807_ = v_cfg_770_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_checks_804_);
lean_inc(v_builtinLint_x3f_803_);
lean_inc(v_restoreAllArtifacts_x3f_800_);
lean_inc(v_enableArtifactCache_x3f_799_);
lean_inc(v_readmeFile_797_);
lean_inc(v_licenseFiles_796_);
lean_inc(v_license_795_);
lean_inc(v_homepage_794_);
lean_inc(v_keywords_793_);
lean_inc(v_description_792_);
lean_inc(v_versionTags_791_);
lean_inc(v_version_790_);
lean_inc(v_lintDriverArgs_789_);
lean_inc(v_lintDriver_788_);
lean_inc(v_testDriverArgs_787_);
lean_inc(v_testDriver_786_);
lean_inc(v_buildArchive_784_);
lean_inc(v_releaseRepo_783_);
lean_inc(v_irDir_782_);
lean_inc(v_binDir_781_);
lean_inc(v_nativeLibDir_780_);
lean_inc(v_leanLibDir_779_);
lean_inc(v_buildDir_778_);
lean_inc(v_srcDir_777_);
lean_inc(v_moreGlobalServerArgs_776_);
lean_inc(v_extraDepTargets_774_);
lean_inc(v_toLeanConfig_772_);
lean_inc(v_toWorkspaceConfig_771_);
lean_dec(v_cfg_770_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_apply_1(v_f_769_, v_buildDir_778_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 5, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_toWorkspaceConfig_771_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_toLeanConfig_772_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_extraDepTargets_774_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_moreGlobalServerArgs_776_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v_srcDir_777_);
lean_ctor_set(v_reuseFailAlloc_812_, 5, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_812_, 6, v_leanLibDir_779_);
lean_ctor_set(v_reuseFailAlloc_812_, 7, v_nativeLibDir_780_);
lean_ctor_set(v_reuseFailAlloc_812_, 8, v_binDir_781_);
lean_ctor_set(v_reuseFailAlloc_812_, 9, v_irDir_782_);
lean_ctor_set(v_reuseFailAlloc_812_, 10, v_releaseRepo_783_);
lean_ctor_set(v_reuseFailAlloc_812_, 11, v_buildArchive_784_);
lean_ctor_set(v_reuseFailAlloc_812_, 12, v_testDriver_786_);
lean_ctor_set(v_reuseFailAlloc_812_, 13, v_testDriverArgs_787_);
lean_ctor_set(v_reuseFailAlloc_812_, 14, v_lintDriver_788_);
lean_ctor_set(v_reuseFailAlloc_812_, 15, v_lintDriverArgs_789_);
lean_ctor_set(v_reuseFailAlloc_812_, 16, v_version_790_);
lean_ctor_set(v_reuseFailAlloc_812_, 17, v_versionTags_791_);
lean_ctor_set(v_reuseFailAlloc_812_, 18, v_description_792_);
lean_ctor_set(v_reuseFailAlloc_812_, 19, v_keywords_793_);
lean_ctor_set(v_reuseFailAlloc_812_, 20, v_homepage_794_);
lean_ctor_set(v_reuseFailAlloc_812_, 21, v_license_795_);
lean_ctor_set(v_reuseFailAlloc_812_, 22, v_licenseFiles_796_);
lean_ctor_set(v_reuseFailAlloc_812_, 23, v_readmeFile_797_);
lean_ctor_set(v_reuseFailAlloc_812_, 24, v_enableArtifactCache_x3f_799_);
lean_ctor_set(v_reuseFailAlloc_812_, 25, v_restoreAllArtifacts_x3f_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 26, v_builtinLint_x3f_803_);
lean_ctor_set(v_reuseFailAlloc_812_, 27, v_checks_804_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*28, v_bootstrap_773_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*28 + 1, v_precompileModules_775_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*28 + 2, v_preferReleaseBuild_785_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*28 + 3, v_reservoir_798_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_801_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*28 + 5, v_allowImportAll_802_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*28 + 6, v_fixedToolchain_805_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__3(lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lake_defaultBuildDir;
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__3___boxed(lean_object* v_x_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lake_PackageConfig_buildDir___proj___redArg___lam__3(v_x_816_);
lean_dec_ref(v_x_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg(){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = ((lean_object*)(l_Lake_PackageConfig_buildDir___proj___redArg___closed__4));
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___boxed(lean_object* v___dummy_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lake_PackageConfig_buildDir___proj___redArg();
return v_res_830_;
}
}
static lean_object* _init_l_Lake_PackageConfig_buildDir___proj___closed__0(void){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lake_PackageConfig_buildDir___proj___redArg();
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object* v_p_832_, lean_object* v_n_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = lean_obj_once(&l_Lake_PackageConfig_buildDir___proj___closed__0, &l_Lake_PackageConfig_buildDir___proj___closed__0_once, _init_l_Lake_PackageConfig_buildDir___proj___closed__0);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object* v_p_835_, lean_object* v_n_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lake_PackageConfig_buildDir___proj(v_p_835_, v_n_836_);
lean_dec(v_n_836_);
lean_dec(v_p_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = lean_obj_once(&l_Lake_PackageConfig_buildDir___proj___closed__0, &l_Lake_PackageConfig_buildDir___proj___closed__0_once, _init_l_Lake_PackageConfig_buildDir___proj___closed__0);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___redArg___boxed(lean_object* v___dummy_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lake_PackageConfig_buildDir_instConfigField___redArg();
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object* v_p_842_, lean_object* v_n_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = lean_obj_once(&l_Lake_PackageConfig_buildDir___proj___closed__0, &l_Lake_PackageConfig_buildDir___proj___closed__0_once, _init_l_Lake_PackageConfig_buildDir___proj___closed__0);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object* v_p_845_, lean_object* v_n_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lake_PackageConfig_buildDir_instConfigField(v_p_845_, v_n_846_);
lean_dec(v_n_846_);
lean_dec(v_p_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0(lean_object* v_cfg_848_){
_start:
{
lean_object* v_leanLibDir_849_; 
v_leanLibDir_849_ = lean_ctor_get(v_cfg_848_, 6);
lean_inc_ref(v_leanLibDir_849_);
return v_leanLibDir_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0(v_cfg_850_);
lean_dec_ref(v_cfg_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__1(lean_object* v_val_852_, lean_object* v_cfg_853_){
_start:
{
lean_object* v_toWorkspaceConfig_854_; lean_object* v_toLeanConfig_855_; uint8_t v_bootstrap_856_; lean_object* v_extraDepTargets_857_; uint8_t v_precompileModules_858_; lean_object* v_moreGlobalServerArgs_859_; lean_object* v_srcDir_860_; lean_object* v_buildDir_861_; lean_object* v_nativeLibDir_862_; lean_object* v_binDir_863_; lean_object* v_irDir_864_; lean_object* v_releaseRepo_865_; lean_object* v_buildArchive_866_; uint8_t v_preferReleaseBuild_867_; lean_object* v_testDriver_868_; lean_object* v_testDriverArgs_869_; lean_object* v_lintDriver_870_; lean_object* v_lintDriverArgs_871_; lean_object* v_version_872_; lean_object* v_versionTags_873_; lean_object* v_description_874_; lean_object* v_keywords_875_; lean_object* v_homepage_876_; lean_object* v_license_877_; lean_object* v_licenseFiles_878_; lean_object* v_readmeFile_879_; uint8_t v_reservoir_880_; lean_object* v_enableArtifactCache_x3f_881_; lean_object* v_restoreAllArtifacts_x3f_882_; uint8_t v_libPrefixOnWindows_883_; uint8_t v_allowImportAll_884_; lean_object* v_builtinLint_x3f_885_; lean_object* v_checks_886_; uint8_t v_fixedToolchain_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_toWorkspaceConfig_854_ = lean_ctor_get(v_cfg_853_, 0);
v_toLeanConfig_855_ = lean_ctor_get(v_cfg_853_, 1);
v_bootstrap_856_ = lean_ctor_get_uint8(v_cfg_853_, sizeof(void*)*28);
v_extraDepTargets_857_ = lean_ctor_get(v_cfg_853_, 2);
v_precompileModules_858_ = lean_ctor_get_uint8(v_cfg_853_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_859_ = lean_ctor_get(v_cfg_853_, 3);
v_srcDir_860_ = lean_ctor_get(v_cfg_853_, 4);
v_buildDir_861_ = lean_ctor_get(v_cfg_853_, 5);
v_nativeLibDir_862_ = lean_ctor_get(v_cfg_853_, 7);
v_binDir_863_ = lean_ctor_get(v_cfg_853_, 8);
v_irDir_864_ = lean_ctor_get(v_cfg_853_, 9);
v_releaseRepo_865_ = lean_ctor_get(v_cfg_853_, 10);
v_buildArchive_866_ = lean_ctor_get(v_cfg_853_, 11);
v_preferReleaseBuild_867_ = lean_ctor_get_uint8(v_cfg_853_, sizeof(void*)*28 + 2);
v_testDriver_868_ = lean_ctor_get(v_cfg_853_, 12);
v_testDriverArgs_869_ = lean_ctor_get(v_cfg_853_, 13);
v_lintDriver_870_ = lean_ctor_get(v_cfg_853_, 14);
v_lintDriverArgs_871_ = lean_ctor_get(v_cfg_853_, 15);
v_version_872_ = lean_ctor_get(v_cfg_853_, 16);
v_versionTags_873_ = lean_ctor_get(v_cfg_853_, 17);
v_description_874_ = lean_ctor_get(v_cfg_853_, 18);
v_keywords_875_ = lean_ctor_get(v_cfg_853_, 19);
v_homepage_876_ = lean_ctor_get(v_cfg_853_, 20);
v_license_877_ = lean_ctor_get(v_cfg_853_, 21);
v_licenseFiles_878_ = lean_ctor_get(v_cfg_853_, 22);
v_readmeFile_879_ = lean_ctor_get(v_cfg_853_, 23);
v_reservoir_880_ = lean_ctor_get_uint8(v_cfg_853_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_881_ = lean_ctor_get(v_cfg_853_, 24);
v_restoreAllArtifacts_x3f_882_ = lean_ctor_get(v_cfg_853_, 25);
v_libPrefixOnWindows_883_ = lean_ctor_get_uint8(v_cfg_853_, sizeof(void*)*28 + 4);
v_allowImportAll_884_ = lean_ctor_get_uint8(v_cfg_853_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_885_ = lean_ctor_get(v_cfg_853_, 26);
v_checks_886_ = lean_ctor_get(v_cfg_853_, 27);
v_fixedToolchain_887_ = lean_ctor_get_uint8(v_cfg_853_, sizeof(void*)*28 + 6);
v_isSharedCheck_894_ = !lean_is_exclusive(v_cfg_853_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_cfg_853_, 6);
lean_dec(v_unused_895_);
v___x_889_ = v_cfg_853_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_checks_886_);
lean_inc(v_builtinLint_x3f_885_);
lean_inc(v_restoreAllArtifacts_x3f_882_);
lean_inc(v_enableArtifactCache_x3f_881_);
lean_inc(v_readmeFile_879_);
lean_inc(v_licenseFiles_878_);
lean_inc(v_license_877_);
lean_inc(v_homepage_876_);
lean_inc(v_keywords_875_);
lean_inc(v_description_874_);
lean_inc(v_versionTags_873_);
lean_inc(v_version_872_);
lean_inc(v_lintDriverArgs_871_);
lean_inc(v_lintDriver_870_);
lean_inc(v_testDriverArgs_869_);
lean_inc(v_testDriver_868_);
lean_inc(v_buildArchive_866_);
lean_inc(v_releaseRepo_865_);
lean_inc(v_irDir_864_);
lean_inc(v_binDir_863_);
lean_inc(v_nativeLibDir_862_);
lean_inc(v_buildDir_861_);
lean_inc(v_srcDir_860_);
lean_inc(v_moreGlobalServerArgs_859_);
lean_inc(v_extraDepTargets_857_);
lean_inc(v_toLeanConfig_855_);
lean_inc(v_toWorkspaceConfig_854_);
lean_dec(v_cfg_853_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 6, v_val_852_);
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_toWorkspaceConfig_854_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_toLeanConfig_855_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_extraDepTargets_857_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v_moreGlobalServerArgs_859_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v_srcDir_860_);
lean_ctor_set(v_reuseFailAlloc_893_, 5, v_buildDir_861_);
lean_ctor_set(v_reuseFailAlloc_893_, 6, v_val_852_);
lean_ctor_set(v_reuseFailAlloc_893_, 7, v_nativeLibDir_862_);
lean_ctor_set(v_reuseFailAlloc_893_, 8, v_binDir_863_);
lean_ctor_set(v_reuseFailAlloc_893_, 9, v_irDir_864_);
lean_ctor_set(v_reuseFailAlloc_893_, 10, v_releaseRepo_865_);
lean_ctor_set(v_reuseFailAlloc_893_, 11, v_buildArchive_866_);
lean_ctor_set(v_reuseFailAlloc_893_, 12, v_testDriver_868_);
lean_ctor_set(v_reuseFailAlloc_893_, 13, v_testDriverArgs_869_);
lean_ctor_set(v_reuseFailAlloc_893_, 14, v_lintDriver_870_);
lean_ctor_set(v_reuseFailAlloc_893_, 15, v_lintDriverArgs_871_);
lean_ctor_set(v_reuseFailAlloc_893_, 16, v_version_872_);
lean_ctor_set(v_reuseFailAlloc_893_, 17, v_versionTags_873_);
lean_ctor_set(v_reuseFailAlloc_893_, 18, v_description_874_);
lean_ctor_set(v_reuseFailAlloc_893_, 19, v_keywords_875_);
lean_ctor_set(v_reuseFailAlloc_893_, 20, v_homepage_876_);
lean_ctor_set(v_reuseFailAlloc_893_, 21, v_license_877_);
lean_ctor_set(v_reuseFailAlloc_893_, 22, v_licenseFiles_878_);
lean_ctor_set(v_reuseFailAlloc_893_, 23, v_readmeFile_879_);
lean_ctor_set(v_reuseFailAlloc_893_, 24, v_enableArtifactCache_x3f_881_);
lean_ctor_set(v_reuseFailAlloc_893_, 25, v_restoreAllArtifacts_x3f_882_);
lean_ctor_set(v_reuseFailAlloc_893_, 26, v_builtinLint_x3f_885_);
lean_ctor_set(v_reuseFailAlloc_893_, 27, v_checks_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*28, v_bootstrap_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*28 + 1, v_precompileModules_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*28 + 2, v_preferReleaseBuild_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*28 + 3, v_reservoir_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*28 + 5, v_allowImportAll_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*28 + 6, v_fixedToolchain_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__2(lean_object* v_f_896_, lean_object* v_cfg_897_){
_start:
{
lean_object* v_toWorkspaceConfig_898_; lean_object* v_toLeanConfig_899_; uint8_t v_bootstrap_900_; lean_object* v_extraDepTargets_901_; uint8_t v_precompileModules_902_; lean_object* v_moreGlobalServerArgs_903_; lean_object* v_srcDir_904_; lean_object* v_buildDir_905_; lean_object* v_leanLibDir_906_; lean_object* v_nativeLibDir_907_; lean_object* v_binDir_908_; lean_object* v_irDir_909_; lean_object* v_releaseRepo_910_; lean_object* v_buildArchive_911_; uint8_t v_preferReleaseBuild_912_; lean_object* v_testDriver_913_; lean_object* v_testDriverArgs_914_; lean_object* v_lintDriver_915_; lean_object* v_lintDriverArgs_916_; lean_object* v_version_917_; lean_object* v_versionTags_918_; lean_object* v_description_919_; lean_object* v_keywords_920_; lean_object* v_homepage_921_; lean_object* v_license_922_; lean_object* v_licenseFiles_923_; lean_object* v_readmeFile_924_; uint8_t v_reservoir_925_; lean_object* v_enableArtifactCache_x3f_926_; lean_object* v_restoreAllArtifacts_x3f_927_; uint8_t v_libPrefixOnWindows_928_; uint8_t v_allowImportAll_929_; lean_object* v_builtinLint_x3f_930_; lean_object* v_checks_931_; uint8_t v_fixedToolchain_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
v_toWorkspaceConfig_898_ = lean_ctor_get(v_cfg_897_, 0);
v_toLeanConfig_899_ = lean_ctor_get(v_cfg_897_, 1);
v_bootstrap_900_ = lean_ctor_get_uint8(v_cfg_897_, sizeof(void*)*28);
v_extraDepTargets_901_ = lean_ctor_get(v_cfg_897_, 2);
v_precompileModules_902_ = lean_ctor_get_uint8(v_cfg_897_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_903_ = lean_ctor_get(v_cfg_897_, 3);
v_srcDir_904_ = lean_ctor_get(v_cfg_897_, 4);
v_buildDir_905_ = lean_ctor_get(v_cfg_897_, 5);
v_leanLibDir_906_ = lean_ctor_get(v_cfg_897_, 6);
v_nativeLibDir_907_ = lean_ctor_get(v_cfg_897_, 7);
v_binDir_908_ = lean_ctor_get(v_cfg_897_, 8);
v_irDir_909_ = lean_ctor_get(v_cfg_897_, 9);
v_releaseRepo_910_ = lean_ctor_get(v_cfg_897_, 10);
v_buildArchive_911_ = lean_ctor_get(v_cfg_897_, 11);
v_preferReleaseBuild_912_ = lean_ctor_get_uint8(v_cfg_897_, sizeof(void*)*28 + 2);
v_testDriver_913_ = lean_ctor_get(v_cfg_897_, 12);
v_testDriverArgs_914_ = lean_ctor_get(v_cfg_897_, 13);
v_lintDriver_915_ = lean_ctor_get(v_cfg_897_, 14);
v_lintDriverArgs_916_ = lean_ctor_get(v_cfg_897_, 15);
v_version_917_ = lean_ctor_get(v_cfg_897_, 16);
v_versionTags_918_ = lean_ctor_get(v_cfg_897_, 17);
v_description_919_ = lean_ctor_get(v_cfg_897_, 18);
v_keywords_920_ = lean_ctor_get(v_cfg_897_, 19);
v_homepage_921_ = lean_ctor_get(v_cfg_897_, 20);
v_license_922_ = lean_ctor_get(v_cfg_897_, 21);
v_licenseFiles_923_ = lean_ctor_get(v_cfg_897_, 22);
v_readmeFile_924_ = lean_ctor_get(v_cfg_897_, 23);
v_reservoir_925_ = lean_ctor_get_uint8(v_cfg_897_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_926_ = lean_ctor_get(v_cfg_897_, 24);
v_restoreAllArtifacts_x3f_927_ = lean_ctor_get(v_cfg_897_, 25);
v_libPrefixOnWindows_928_ = lean_ctor_get_uint8(v_cfg_897_, sizeof(void*)*28 + 4);
v_allowImportAll_929_ = lean_ctor_get_uint8(v_cfg_897_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_930_ = lean_ctor_get(v_cfg_897_, 26);
v_checks_931_ = lean_ctor_get(v_cfg_897_, 27);
v_fixedToolchain_932_ = lean_ctor_get_uint8(v_cfg_897_, sizeof(void*)*28 + 6);
v_isSharedCheck_940_ = !lean_is_exclusive(v_cfg_897_);
if (v_isSharedCheck_940_ == 0)
{
v___x_934_ = v_cfg_897_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_checks_931_);
lean_inc(v_builtinLint_x3f_930_);
lean_inc(v_restoreAllArtifacts_x3f_927_);
lean_inc(v_enableArtifactCache_x3f_926_);
lean_inc(v_readmeFile_924_);
lean_inc(v_licenseFiles_923_);
lean_inc(v_license_922_);
lean_inc(v_homepage_921_);
lean_inc(v_keywords_920_);
lean_inc(v_description_919_);
lean_inc(v_versionTags_918_);
lean_inc(v_version_917_);
lean_inc(v_lintDriverArgs_916_);
lean_inc(v_lintDriver_915_);
lean_inc(v_testDriverArgs_914_);
lean_inc(v_testDriver_913_);
lean_inc(v_buildArchive_911_);
lean_inc(v_releaseRepo_910_);
lean_inc(v_irDir_909_);
lean_inc(v_binDir_908_);
lean_inc(v_nativeLibDir_907_);
lean_inc(v_leanLibDir_906_);
lean_inc(v_buildDir_905_);
lean_inc(v_srcDir_904_);
lean_inc(v_moreGlobalServerArgs_903_);
lean_inc(v_extraDepTargets_901_);
lean_inc(v_toLeanConfig_899_);
lean_inc(v_toWorkspaceConfig_898_);
lean_dec(v_cfg_897_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = lean_apply_1(v_f_896_, v_leanLibDir_906_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 6, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_toWorkspaceConfig_898_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_toLeanConfig_899_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_extraDepTargets_901_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_moreGlobalServerArgs_903_);
lean_ctor_set(v_reuseFailAlloc_939_, 4, v_srcDir_904_);
lean_ctor_set(v_reuseFailAlloc_939_, 5, v_buildDir_905_);
lean_ctor_set(v_reuseFailAlloc_939_, 6, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_939_, 7, v_nativeLibDir_907_);
lean_ctor_set(v_reuseFailAlloc_939_, 8, v_binDir_908_);
lean_ctor_set(v_reuseFailAlloc_939_, 9, v_irDir_909_);
lean_ctor_set(v_reuseFailAlloc_939_, 10, v_releaseRepo_910_);
lean_ctor_set(v_reuseFailAlloc_939_, 11, v_buildArchive_911_);
lean_ctor_set(v_reuseFailAlloc_939_, 12, v_testDriver_913_);
lean_ctor_set(v_reuseFailAlloc_939_, 13, v_testDriverArgs_914_);
lean_ctor_set(v_reuseFailAlloc_939_, 14, v_lintDriver_915_);
lean_ctor_set(v_reuseFailAlloc_939_, 15, v_lintDriverArgs_916_);
lean_ctor_set(v_reuseFailAlloc_939_, 16, v_version_917_);
lean_ctor_set(v_reuseFailAlloc_939_, 17, v_versionTags_918_);
lean_ctor_set(v_reuseFailAlloc_939_, 18, v_description_919_);
lean_ctor_set(v_reuseFailAlloc_939_, 19, v_keywords_920_);
lean_ctor_set(v_reuseFailAlloc_939_, 20, v_homepage_921_);
lean_ctor_set(v_reuseFailAlloc_939_, 21, v_license_922_);
lean_ctor_set(v_reuseFailAlloc_939_, 22, v_licenseFiles_923_);
lean_ctor_set(v_reuseFailAlloc_939_, 23, v_readmeFile_924_);
lean_ctor_set(v_reuseFailAlloc_939_, 24, v_enableArtifactCache_x3f_926_);
lean_ctor_set(v_reuseFailAlloc_939_, 25, v_restoreAllArtifacts_x3f_927_);
lean_ctor_set(v_reuseFailAlloc_939_, 26, v_builtinLint_x3f_930_);
lean_ctor_set(v_reuseFailAlloc_939_, 27, v_checks_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, sizeof(void*)*28, v_bootstrap_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, sizeof(void*)*28 + 1, v_precompileModules_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, sizeof(void*)*28 + 2, v_preferReleaseBuild_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, sizeof(void*)*28 + 3, v_reservoir_925_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, sizeof(void*)*28 + 5, v_allowImportAll_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, sizeof(void*)*28 + 6, v_fixedToolchain_932_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3(lean_object* v_x_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lake_defaultLeanLibDir;
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3___boxed(lean_object* v_x_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3(v_x_943_);
lean_dec_ref(v_x_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg(){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__4));
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___boxed(lean_object* v___dummy_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lake_PackageConfig_leanLibDir___proj___redArg();
return v_res_957_;
}
}
static lean_object* _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0(void){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lake_PackageConfig_leanLibDir___proj___redArg();
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object* v_p_959_, lean_object* v_n_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = lean_obj_once(&l_Lake_PackageConfig_leanLibDir___proj___closed__0, &l_Lake_PackageConfig_leanLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object* v_p_962_, lean_object* v_n_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_962_, v_n_963_);
lean_dec(v_n_963_);
lean_dec(v_p_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = lean_obj_once(&l_Lake_PackageConfig_leanLibDir___proj___closed__0, &l_Lake_PackageConfig_leanLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___redArg___boxed(lean_object* v___dummy_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lake_PackageConfig_leanLibDir_instConfigField___redArg();
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object* v_p_969_, lean_object* v_n_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = lean_obj_once(&l_Lake_PackageConfig_leanLibDir___proj___closed__0, &l_Lake_PackageConfig_leanLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object* v_p_972_, lean_object* v_n_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lake_PackageConfig_leanLibDir_instConfigField(v_p_972_, v_n_973_);
lean_dec(v_n_973_);
lean_dec(v_p_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0(lean_object* v_cfg_975_){
_start:
{
lean_object* v_nativeLibDir_976_; 
v_nativeLibDir_976_ = lean_ctor_get(v_cfg_975_, 7);
lean_inc_ref(v_nativeLibDir_976_);
return v_nativeLibDir_976_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0(v_cfg_977_);
lean_dec_ref(v_cfg_977_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__1(lean_object* v_val_979_, lean_object* v_cfg_980_){
_start:
{
lean_object* v_toWorkspaceConfig_981_; lean_object* v_toLeanConfig_982_; uint8_t v_bootstrap_983_; lean_object* v_extraDepTargets_984_; uint8_t v_precompileModules_985_; lean_object* v_moreGlobalServerArgs_986_; lean_object* v_srcDir_987_; lean_object* v_buildDir_988_; lean_object* v_leanLibDir_989_; lean_object* v_binDir_990_; lean_object* v_irDir_991_; lean_object* v_releaseRepo_992_; lean_object* v_buildArchive_993_; uint8_t v_preferReleaseBuild_994_; lean_object* v_testDriver_995_; lean_object* v_testDriverArgs_996_; lean_object* v_lintDriver_997_; lean_object* v_lintDriverArgs_998_; lean_object* v_version_999_; lean_object* v_versionTags_1000_; lean_object* v_description_1001_; lean_object* v_keywords_1002_; lean_object* v_homepage_1003_; lean_object* v_license_1004_; lean_object* v_licenseFiles_1005_; lean_object* v_readmeFile_1006_; uint8_t v_reservoir_1007_; lean_object* v_enableArtifactCache_x3f_1008_; lean_object* v_restoreAllArtifacts_x3f_1009_; uint8_t v_libPrefixOnWindows_1010_; uint8_t v_allowImportAll_1011_; lean_object* v_builtinLint_x3f_1012_; lean_object* v_checks_1013_; uint8_t v_fixedToolchain_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_toWorkspaceConfig_981_ = lean_ctor_get(v_cfg_980_, 0);
v_toLeanConfig_982_ = lean_ctor_get(v_cfg_980_, 1);
v_bootstrap_983_ = lean_ctor_get_uint8(v_cfg_980_, sizeof(void*)*28);
v_extraDepTargets_984_ = lean_ctor_get(v_cfg_980_, 2);
v_precompileModules_985_ = lean_ctor_get_uint8(v_cfg_980_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_986_ = lean_ctor_get(v_cfg_980_, 3);
v_srcDir_987_ = lean_ctor_get(v_cfg_980_, 4);
v_buildDir_988_ = lean_ctor_get(v_cfg_980_, 5);
v_leanLibDir_989_ = lean_ctor_get(v_cfg_980_, 6);
v_binDir_990_ = lean_ctor_get(v_cfg_980_, 8);
v_irDir_991_ = lean_ctor_get(v_cfg_980_, 9);
v_releaseRepo_992_ = lean_ctor_get(v_cfg_980_, 10);
v_buildArchive_993_ = lean_ctor_get(v_cfg_980_, 11);
v_preferReleaseBuild_994_ = lean_ctor_get_uint8(v_cfg_980_, sizeof(void*)*28 + 2);
v_testDriver_995_ = lean_ctor_get(v_cfg_980_, 12);
v_testDriverArgs_996_ = lean_ctor_get(v_cfg_980_, 13);
v_lintDriver_997_ = lean_ctor_get(v_cfg_980_, 14);
v_lintDriverArgs_998_ = lean_ctor_get(v_cfg_980_, 15);
v_version_999_ = lean_ctor_get(v_cfg_980_, 16);
v_versionTags_1000_ = lean_ctor_get(v_cfg_980_, 17);
v_description_1001_ = lean_ctor_get(v_cfg_980_, 18);
v_keywords_1002_ = lean_ctor_get(v_cfg_980_, 19);
v_homepage_1003_ = lean_ctor_get(v_cfg_980_, 20);
v_license_1004_ = lean_ctor_get(v_cfg_980_, 21);
v_licenseFiles_1005_ = lean_ctor_get(v_cfg_980_, 22);
v_readmeFile_1006_ = lean_ctor_get(v_cfg_980_, 23);
v_reservoir_1007_ = lean_ctor_get_uint8(v_cfg_980_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1008_ = lean_ctor_get(v_cfg_980_, 24);
v_restoreAllArtifacts_x3f_1009_ = lean_ctor_get(v_cfg_980_, 25);
v_libPrefixOnWindows_1010_ = lean_ctor_get_uint8(v_cfg_980_, sizeof(void*)*28 + 4);
v_allowImportAll_1011_ = lean_ctor_get_uint8(v_cfg_980_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1012_ = lean_ctor_get(v_cfg_980_, 26);
v_checks_1013_ = lean_ctor_get(v_cfg_980_, 27);
v_fixedToolchain_1014_ = lean_ctor_get_uint8(v_cfg_980_, sizeof(void*)*28 + 6);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_cfg_980_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_cfg_980_, 7);
lean_dec(v_unused_1022_);
v___x_1016_ = v_cfg_980_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_checks_1013_);
lean_inc(v_builtinLint_x3f_1012_);
lean_inc(v_restoreAllArtifacts_x3f_1009_);
lean_inc(v_enableArtifactCache_x3f_1008_);
lean_inc(v_readmeFile_1006_);
lean_inc(v_licenseFiles_1005_);
lean_inc(v_license_1004_);
lean_inc(v_homepage_1003_);
lean_inc(v_keywords_1002_);
lean_inc(v_description_1001_);
lean_inc(v_versionTags_1000_);
lean_inc(v_version_999_);
lean_inc(v_lintDriverArgs_998_);
lean_inc(v_lintDriver_997_);
lean_inc(v_testDriverArgs_996_);
lean_inc(v_testDriver_995_);
lean_inc(v_buildArchive_993_);
lean_inc(v_releaseRepo_992_);
lean_inc(v_irDir_991_);
lean_inc(v_binDir_990_);
lean_inc(v_leanLibDir_989_);
lean_inc(v_buildDir_988_);
lean_inc(v_srcDir_987_);
lean_inc(v_moreGlobalServerArgs_986_);
lean_inc(v_extraDepTargets_984_);
lean_inc(v_toLeanConfig_982_);
lean_inc(v_toWorkspaceConfig_981_);
lean_dec(v_cfg_980_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 7, v_val_979_);
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_toWorkspaceConfig_981_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_toLeanConfig_982_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_extraDepTargets_984_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_moreGlobalServerArgs_986_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_srcDir_987_);
lean_ctor_set(v_reuseFailAlloc_1020_, 5, v_buildDir_988_);
lean_ctor_set(v_reuseFailAlloc_1020_, 6, v_leanLibDir_989_);
lean_ctor_set(v_reuseFailAlloc_1020_, 7, v_val_979_);
lean_ctor_set(v_reuseFailAlloc_1020_, 8, v_binDir_990_);
lean_ctor_set(v_reuseFailAlloc_1020_, 9, v_irDir_991_);
lean_ctor_set(v_reuseFailAlloc_1020_, 10, v_releaseRepo_992_);
lean_ctor_set(v_reuseFailAlloc_1020_, 11, v_buildArchive_993_);
lean_ctor_set(v_reuseFailAlloc_1020_, 12, v_testDriver_995_);
lean_ctor_set(v_reuseFailAlloc_1020_, 13, v_testDriverArgs_996_);
lean_ctor_set(v_reuseFailAlloc_1020_, 14, v_lintDriver_997_);
lean_ctor_set(v_reuseFailAlloc_1020_, 15, v_lintDriverArgs_998_);
lean_ctor_set(v_reuseFailAlloc_1020_, 16, v_version_999_);
lean_ctor_set(v_reuseFailAlloc_1020_, 17, v_versionTags_1000_);
lean_ctor_set(v_reuseFailAlloc_1020_, 18, v_description_1001_);
lean_ctor_set(v_reuseFailAlloc_1020_, 19, v_keywords_1002_);
lean_ctor_set(v_reuseFailAlloc_1020_, 20, v_homepage_1003_);
lean_ctor_set(v_reuseFailAlloc_1020_, 21, v_license_1004_);
lean_ctor_set(v_reuseFailAlloc_1020_, 22, v_licenseFiles_1005_);
lean_ctor_set(v_reuseFailAlloc_1020_, 23, v_readmeFile_1006_);
lean_ctor_set(v_reuseFailAlloc_1020_, 24, v_enableArtifactCache_x3f_1008_);
lean_ctor_set(v_reuseFailAlloc_1020_, 25, v_restoreAllArtifacts_x3f_1009_);
lean_ctor_set(v_reuseFailAlloc_1020_, 26, v_builtinLint_x3f_1012_);
lean_ctor_set(v_reuseFailAlloc_1020_, 27, v_checks_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1020_, sizeof(void*)*28, v_bootstrap_983_);
lean_ctor_set_uint8(v_reuseFailAlloc_1020_, sizeof(void*)*28 + 1, v_precompileModules_985_);
lean_ctor_set_uint8(v_reuseFailAlloc_1020_, sizeof(void*)*28 + 2, v_preferReleaseBuild_994_);
lean_ctor_set_uint8(v_reuseFailAlloc_1020_, sizeof(void*)*28 + 3, v_reservoir_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1020_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1010_);
lean_ctor_set_uint8(v_reuseFailAlloc_1020_, sizeof(void*)*28 + 5, v_allowImportAll_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1020_, sizeof(void*)*28 + 6, v_fixedToolchain_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__2(lean_object* v_f_1023_, lean_object* v_cfg_1024_){
_start:
{
lean_object* v_toWorkspaceConfig_1025_; lean_object* v_toLeanConfig_1026_; uint8_t v_bootstrap_1027_; lean_object* v_extraDepTargets_1028_; uint8_t v_precompileModules_1029_; lean_object* v_moreGlobalServerArgs_1030_; lean_object* v_srcDir_1031_; lean_object* v_buildDir_1032_; lean_object* v_leanLibDir_1033_; lean_object* v_nativeLibDir_1034_; lean_object* v_binDir_1035_; lean_object* v_irDir_1036_; lean_object* v_releaseRepo_1037_; lean_object* v_buildArchive_1038_; uint8_t v_preferReleaseBuild_1039_; lean_object* v_testDriver_1040_; lean_object* v_testDriverArgs_1041_; lean_object* v_lintDriver_1042_; lean_object* v_lintDriverArgs_1043_; lean_object* v_version_1044_; lean_object* v_versionTags_1045_; lean_object* v_description_1046_; lean_object* v_keywords_1047_; lean_object* v_homepage_1048_; lean_object* v_license_1049_; lean_object* v_licenseFiles_1050_; lean_object* v_readmeFile_1051_; uint8_t v_reservoir_1052_; lean_object* v_enableArtifactCache_x3f_1053_; lean_object* v_restoreAllArtifacts_x3f_1054_; uint8_t v_libPrefixOnWindows_1055_; uint8_t v_allowImportAll_1056_; lean_object* v_builtinLint_x3f_1057_; lean_object* v_checks_1058_; uint8_t v_fixedToolchain_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1067_; 
v_toWorkspaceConfig_1025_ = lean_ctor_get(v_cfg_1024_, 0);
v_toLeanConfig_1026_ = lean_ctor_get(v_cfg_1024_, 1);
v_bootstrap_1027_ = lean_ctor_get_uint8(v_cfg_1024_, sizeof(void*)*28);
v_extraDepTargets_1028_ = lean_ctor_get(v_cfg_1024_, 2);
v_precompileModules_1029_ = lean_ctor_get_uint8(v_cfg_1024_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1030_ = lean_ctor_get(v_cfg_1024_, 3);
v_srcDir_1031_ = lean_ctor_get(v_cfg_1024_, 4);
v_buildDir_1032_ = lean_ctor_get(v_cfg_1024_, 5);
v_leanLibDir_1033_ = lean_ctor_get(v_cfg_1024_, 6);
v_nativeLibDir_1034_ = lean_ctor_get(v_cfg_1024_, 7);
v_binDir_1035_ = lean_ctor_get(v_cfg_1024_, 8);
v_irDir_1036_ = lean_ctor_get(v_cfg_1024_, 9);
v_releaseRepo_1037_ = lean_ctor_get(v_cfg_1024_, 10);
v_buildArchive_1038_ = lean_ctor_get(v_cfg_1024_, 11);
v_preferReleaseBuild_1039_ = lean_ctor_get_uint8(v_cfg_1024_, sizeof(void*)*28 + 2);
v_testDriver_1040_ = lean_ctor_get(v_cfg_1024_, 12);
v_testDriverArgs_1041_ = lean_ctor_get(v_cfg_1024_, 13);
v_lintDriver_1042_ = lean_ctor_get(v_cfg_1024_, 14);
v_lintDriverArgs_1043_ = lean_ctor_get(v_cfg_1024_, 15);
v_version_1044_ = lean_ctor_get(v_cfg_1024_, 16);
v_versionTags_1045_ = lean_ctor_get(v_cfg_1024_, 17);
v_description_1046_ = lean_ctor_get(v_cfg_1024_, 18);
v_keywords_1047_ = lean_ctor_get(v_cfg_1024_, 19);
v_homepage_1048_ = lean_ctor_get(v_cfg_1024_, 20);
v_license_1049_ = lean_ctor_get(v_cfg_1024_, 21);
v_licenseFiles_1050_ = lean_ctor_get(v_cfg_1024_, 22);
v_readmeFile_1051_ = lean_ctor_get(v_cfg_1024_, 23);
v_reservoir_1052_ = lean_ctor_get_uint8(v_cfg_1024_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1053_ = lean_ctor_get(v_cfg_1024_, 24);
v_restoreAllArtifacts_x3f_1054_ = lean_ctor_get(v_cfg_1024_, 25);
v_libPrefixOnWindows_1055_ = lean_ctor_get_uint8(v_cfg_1024_, sizeof(void*)*28 + 4);
v_allowImportAll_1056_ = lean_ctor_get_uint8(v_cfg_1024_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1057_ = lean_ctor_get(v_cfg_1024_, 26);
v_checks_1058_ = lean_ctor_get(v_cfg_1024_, 27);
v_fixedToolchain_1059_ = lean_ctor_get_uint8(v_cfg_1024_, sizeof(void*)*28 + 6);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_cfg_1024_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1061_ = v_cfg_1024_;
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_checks_1058_);
lean_inc(v_builtinLint_x3f_1057_);
lean_inc(v_restoreAllArtifacts_x3f_1054_);
lean_inc(v_enableArtifactCache_x3f_1053_);
lean_inc(v_readmeFile_1051_);
lean_inc(v_licenseFiles_1050_);
lean_inc(v_license_1049_);
lean_inc(v_homepage_1048_);
lean_inc(v_keywords_1047_);
lean_inc(v_description_1046_);
lean_inc(v_versionTags_1045_);
lean_inc(v_version_1044_);
lean_inc(v_lintDriverArgs_1043_);
lean_inc(v_lintDriver_1042_);
lean_inc(v_testDriverArgs_1041_);
lean_inc(v_testDriver_1040_);
lean_inc(v_buildArchive_1038_);
lean_inc(v_releaseRepo_1037_);
lean_inc(v_irDir_1036_);
lean_inc(v_binDir_1035_);
lean_inc(v_nativeLibDir_1034_);
lean_inc(v_leanLibDir_1033_);
lean_inc(v_buildDir_1032_);
lean_inc(v_srcDir_1031_);
lean_inc(v_moreGlobalServerArgs_1030_);
lean_inc(v_extraDepTargets_1028_);
lean_inc(v_toLeanConfig_1026_);
lean_inc(v_toWorkspaceConfig_1025_);
lean_dec(v_cfg_1024_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = lean_apply_1(v_f_1023_, v_nativeLibDir_1034_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 7, v___x_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_toWorkspaceConfig_1025_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_toLeanConfig_1026_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v_extraDepTargets_1028_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v_moreGlobalServerArgs_1030_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v_srcDir_1031_);
lean_ctor_set(v_reuseFailAlloc_1066_, 5, v_buildDir_1032_);
lean_ctor_set(v_reuseFailAlloc_1066_, 6, v_leanLibDir_1033_);
lean_ctor_set(v_reuseFailAlloc_1066_, 7, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1066_, 8, v_binDir_1035_);
lean_ctor_set(v_reuseFailAlloc_1066_, 9, v_irDir_1036_);
lean_ctor_set(v_reuseFailAlloc_1066_, 10, v_releaseRepo_1037_);
lean_ctor_set(v_reuseFailAlloc_1066_, 11, v_buildArchive_1038_);
lean_ctor_set(v_reuseFailAlloc_1066_, 12, v_testDriver_1040_);
lean_ctor_set(v_reuseFailAlloc_1066_, 13, v_testDriverArgs_1041_);
lean_ctor_set(v_reuseFailAlloc_1066_, 14, v_lintDriver_1042_);
lean_ctor_set(v_reuseFailAlloc_1066_, 15, v_lintDriverArgs_1043_);
lean_ctor_set(v_reuseFailAlloc_1066_, 16, v_version_1044_);
lean_ctor_set(v_reuseFailAlloc_1066_, 17, v_versionTags_1045_);
lean_ctor_set(v_reuseFailAlloc_1066_, 18, v_description_1046_);
lean_ctor_set(v_reuseFailAlloc_1066_, 19, v_keywords_1047_);
lean_ctor_set(v_reuseFailAlloc_1066_, 20, v_homepage_1048_);
lean_ctor_set(v_reuseFailAlloc_1066_, 21, v_license_1049_);
lean_ctor_set(v_reuseFailAlloc_1066_, 22, v_licenseFiles_1050_);
lean_ctor_set(v_reuseFailAlloc_1066_, 23, v_readmeFile_1051_);
lean_ctor_set(v_reuseFailAlloc_1066_, 24, v_enableArtifactCache_x3f_1053_);
lean_ctor_set(v_reuseFailAlloc_1066_, 25, v_restoreAllArtifacts_x3f_1054_);
lean_ctor_set(v_reuseFailAlloc_1066_, 26, v_builtinLint_x3f_1057_);
lean_ctor_set(v_reuseFailAlloc_1066_, 27, v_checks_1058_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*28, v_bootstrap_1027_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*28 + 1, v_precompileModules_1029_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1039_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*28 + 3, v_reservoir_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*28 + 5, v_allowImportAll_1056_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*28 + 6, v_fixedToolchain_1059_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3(lean_object* v_x_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lake_defaultNativeLibDir;
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3___boxed(lean_object* v_x_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3(v_x_1070_);
lean_dec_ref(v_x_1070_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg(){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = ((lean_object*)(l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__4));
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___boxed(lean_object* v___dummy_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg();
return v_res_1084_;
}
}
static lean_object* _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0(void){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg();
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object* v_p_1086_, lean_object* v_n_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_obj_once(&l_Lake_PackageConfig_nativeLibDir___proj___closed__0, &l_Lake_PackageConfig_nativeLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object* v_p_1089_, lean_object* v_n_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_1089_, v_n_1090_);
lean_dec(v_n_1090_);
lean_dec(v_p_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_obj_once(&l_Lake_PackageConfig_nativeLibDir___proj___closed__0, &l_Lake_PackageConfig_nativeLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg___boxed(lean_object* v___dummy_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg();
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object* v_p_1096_, lean_object* v_n_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_obj_once(&l_Lake_PackageConfig_nativeLibDir___proj___closed__0, &l_Lake_PackageConfig_nativeLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object* v_p_1099_, lean_object* v_n_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lake_PackageConfig_nativeLibDir_instConfigField(v_p_1099_, v_n_1100_);
lean_dec(v_n_1100_);
lean_dec(v_p_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__0(lean_object* v_cfg_1102_){
_start:
{
lean_object* v_binDir_1103_; 
v_binDir_1103_ = lean_ctor_get(v_cfg_1102_, 8);
lean_inc_ref(v_binDir_1103_);
return v_binDir_1103_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lake_PackageConfig_binDir___proj___redArg___lam__0(v_cfg_1104_);
lean_dec_ref(v_cfg_1104_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__1(lean_object* v_val_1106_, lean_object* v_cfg_1107_){
_start:
{
lean_object* v_toWorkspaceConfig_1108_; lean_object* v_toLeanConfig_1109_; uint8_t v_bootstrap_1110_; lean_object* v_extraDepTargets_1111_; uint8_t v_precompileModules_1112_; lean_object* v_moreGlobalServerArgs_1113_; lean_object* v_srcDir_1114_; lean_object* v_buildDir_1115_; lean_object* v_leanLibDir_1116_; lean_object* v_nativeLibDir_1117_; lean_object* v_irDir_1118_; lean_object* v_releaseRepo_1119_; lean_object* v_buildArchive_1120_; uint8_t v_preferReleaseBuild_1121_; lean_object* v_testDriver_1122_; lean_object* v_testDriverArgs_1123_; lean_object* v_lintDriver_1124_; lean_object* v_lintDriverArgs_1125_; lean_object* v_version_1126_; lean_object* v_versionTags_1127_; lean_object* v_description_1128_; lean_object* v_keywords_1129_; lean_object* v_homepage_1130_; lean_object* v_license_1131_; lean_object* v_licenseFiles_1132_; lean_object* v_readmeFile_1133_; uint8_t v_reservoir_1134_; lean_object* v_enableArtifactCache_x3f_1135_; lean_object* v_restoreAllArtifacts_x3f_1136_; uint8_t v_libPrefixOnWindows_1137_; uint8_t v_allowImportAll_1138_; lean_object* v_builtinLint_x3f_1139_; lean_object* v_checks_1140_; uint8_t v_fixedToolchain_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_toWorkspaceConfig_1108_ = lean_ctor_get(v_cfg_1107_, 0);
v_toLeanConfig_1109_ = lean_ctor_get(v_cfg_1107_, 1);
v_bootstrap_1110_ = lean_ctor_get_uint8(v_cfg_1107_, sizeof(void*)*28);
v_extraDepTargets_1111_ = lean_ctor_get(v_cfg_1107_, 2);
v_precompileModules_1112_ = lean_ctor_get_uint8(v_cfg_1107_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1113_ = lean_ctor_get(v_cfg_1107_, 3);
v_srcDir_1114_ = lean_ctor_get(v_cfg_1107_, 4);
v_buildDir_1115_ = lean_ctor_get(v_cfg_1107_, 5);
v_leanLibDir_1116_ = lean_ctor_get(v_cfg_1107_, 6);
v_nativeLibDir_1117_ = lean_ctor_get(v_cfg_1107_, 7);
v_irDir_1118_ = lean_ctor_get(v_cfg_1107_, 9);
v_releaseRepo_1119_ = lean_ctor_get(v_cfg_1107_, 10);
v_buildArchive_1120_ = lean_ctor_get(v_cfg_1107_, 11);
v_preferReleaseBuild_1121_ = lean_ctor_get_uint8(v_cfg_1107_, sizeof(void*)*28 + 2);
v_testDriver_1122_ = lean_ctor_get(v_cfg_1107_, 12);
v_testDriverArgs_1123_ = lean_ctor_get(v_cfg_1107_, 13);
v_lintDriver_1124_ = lean_ctor_get(v_cfg_1107_, 14);
v_lintDriverArgs_1125_ = lean_ctor_get(v_cfg_1107_, 15);
v_version_1126_ = lean_ctor_get(v_cfg_1107_, 16);
v_versionTags_1127_ = lean_ctor_get(v_cfg_1107_, 17);
v_description_1128_ = lean_ctor_get(v_cfg_1107_, 18);
v_keywords_1129_ = lean_ctor_get(v_cfg_1107_, 19);
v_homepage_1130_ = lean_ctor_get(v_cfg_1107_, 20);
v_license_1131_ = lean_ctor_get(v_cfg_1107_, 21);
v_licenseFiles_1132_ = lean_ctor_get(v_cfg_1107_, 22);
v_readmeFile_1133_ = lean_ctor_get(v_cfg_1107_, 23);
v_reservoir_1134_ = lean_ctor_get_uint8(v_cfg_1107_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1135_ = lean_ctor_get(v_cfg_1107_, 24);
v_restoreAllArtifacts_x3f_1136_ = lean_ctor_get(v_cfg_1107_, 25);
v_libPrefixOnWindows_1137_ = lean_ctor_get_uint8(v_cfg_1107_, sizeof(void*)*28 + 4);
v_allowImportAll_1138_ = lean_ctor_get_uint8(v_cfg_1107_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1139_ = lean_ctor_get(v_cfg_1107_, 26);
v_checks_1140_ = lean_ctor_get(v_cfg_1107_, 27);
v_fixedToolchain_1141_ = lean_ctor_get_uint8(v_cfg_1107_, sizeof(void*)*28 + 6);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_cfg_1107_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v_cfg_1107_, 8);
lean_dec(v_unused_1149_);
v___x_1143_ = v_cfg_1107_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_checks_1140_);
lean_inc(v_builtinLint_x3f_1139_);
lean_inc(v_restoreAllArtifacts_x3f_1136_);
lean_inc(v_enableArtifactCache_x3f_1135_);
lean_inc(v_readmeFile_1133_);
lean_inc(v_licenseFiles_1132_);
lean_inc(v_license_1131_);
lean_inc(v_homepage_1130_);
lean_inc(v_keywords_1129_);
lean_inc(v_description_1128_);
lean_inc(v_versionTags_1127_);
lean_inc(v_version_1126_);
lean_inc(v_lintDriverArgs_1125_);
lean_inc(v_lintDriver_1124_);
lean_inc(v_testDriverArgs_1123_);
lean_inc(v_testDriver_1122_);
lean_inc(v_buildArchive_1120_);
lean_inc(v_releaseRepo_1119_);
lean_inc(v_irDir_1118_);
lean_inc(v_nativeLibDir_1117_);
lean_inc(v_leanLibDir_1116_);
lean_inc(v_buildDir_1115_);
lean_inc(v_srcDir_1114_);
lean_inc(v_moreGlobalServerArgs_1113_);
lean_inc(v_extraDepTargets_1111_);
lean_inc(v_toLeanConfig_1109_);
lean_inc(v_toWorkspaceConfig_1108_);
lean_dec(v_cfg_1107_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 8, v_val_1106_);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_toWorkspaceConfig_1108_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_toLeanConfig_1109_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_extraDepTargets_1111_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_moreGlobalServerArgs_1113_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_srcDir_1114_);
lean_ctor_set(v_reuseFailAlloc_1147_, 5, v_buildDir_1115_);
lean_ctor_set(v_reuseFailAlloc_1147_, 6, v_leanLibDir_1116_);
lean_ctor_set(v_reuseFailAlloc_1147_, 7, v_nativeLibDir_1117_);
lean_ctor_set(v_reuseFailAlloc_1147_, 8, v_val_1106_);
lean_ctor_set(v_reuseFailAlloc_1147_, 9, v_irDir_1118_);
lean_ctor_set(v_reuseFailAlloc_1147_, 10, v_releaseRepo_1119_);
lean_ctor_set(v_reuseFailAlloc_1147_, 11, v_buildArchive_1120_);
lean_ctor_set(v_reuseFailAlloc_1147_, 12, v_testDriver_1122_);
lean_ctor_set(v_reuseFailAlloc_1147_, 13, v_testDriverArgs_1123_);
lean_ctor_set(v_reuseFailAlloc_1147_, 14, v_lintDriver_1124_);
lean_ctor_set(v_reuseFailAlloc_1147_, 15, v_lintDriverArgs_1125_);
lean_ctor_set(v_reuseFailAlloc_1147_, 16, v_version_1126_);
lean_ctor_set(v_reuseFailAlloc_1147_, 17, v_versionTags_1127_);
lean_ctor_set(v_reuseFailAlloc_1147_, 18, v_description_1128_);
lean_ctor_set(v_reuseFailAlloc_1147_, 19, v_keywords_1129_);
lean_ctor_set(v_reuseFailAlloc_1147_, 20, v_homepage_1130_);
lean_ctor_set(v_reuseFailAlloc_1147_, 21, v_license_1131_);
lean_ctor_set(v_reuseFailAlloc_1147_, 22, v_licenseFiles_1132_);
lean_ctor_set(v_reuseFailAlloc_1147_, 23, v_readmeFile_1133_);
lean_ctor_set(v_reuseFailAlloc_1147_, 24, v_enableArtifactCache_x3f_1135_);
lean_ctor_set(v_reuseFailAlloc_1147_, 25, v_restoreAllArtifacts_x3f_1136_);
lean_ctor_set(v_reuseFailAlloc_1147_, 26, v_builtinLint_x3f_1139_);
lean_ctor_set(v_reuseFailAlloc_1147_, 27, v_checks_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1147_, sizeof(void*)*28, v_bootstrap_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1147_, sizeof(void*)*28 + 1, v_precompileModules_1112_);
lean_ctor_set_uint8(v_reuseFailAlloc_1147_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1121_);
lean_ctor_set_uint8(v_reuseFailAlloc_1147_, sizeof(void*)*28 + 3, v_reservoir_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1147_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1137_);
lean_ctor_set_uint8(v_reuseFailAlloc_1147_, sizeof(void*)*28 + 5, v_allowImportAll_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1147_, sizeof(void*)*28 + 6, v_fixedToolchain_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__2(lean_object* v_f_1150_, lean_object* v_cfg_1151_){
_start:
{
lean_object* v_toWorkspaceConfig_1152_; lean_object* v_toLeanConfig_1153_; uint8_t v_bootstrap_1154_; lean_object* v_extraDepTargets_1155_; uint8_t v_precompileModules_1156_; lean_object* v_moreGlobalServerArgs_1157_; lean_object* v_srcDir_1158_; lean_object* v_buildDir_1159_; lean_object* v_leanLibDir_1160_; lean_object* v_nativeLibDir_1161_; lean_object* v_binDir_1162_; lean_object* v_irDir_1163_; lean_object* v_releaseRepo_1164_; lean_object* v_buildArchive_1165_; uint8_t v_preferReleaseBuild_1166_; lean_object* v_testDriver_1167_; lean_object* v_testDriverArgs_1168_; lean_object* v_lintDriver_1169_; lean_object* v_lintDriverArgs_1170_; lean_object* v_version_1171_; lean_object* v_versionTags_1172_; lean_object* v_description_1173_; lean_object* v_keywords_1174_; lean_object* v_homepage_1175_; lean_object* v_license_1176_; lean_object* v_licenseFiles_1177_; lean_object* v_readmeFile_1178_; uint8_t v_reservoir_1179_; lean_object* v_enableArtifactCache_x3f_1180_; lean_object* v_restoreAllArtifacts_x3f_1181_; uint8_t v_libPrefixOnWindows_1182_; uint8_t v_allowImportAll_1183_; lean_object* v_builtinLint_x3f_1184_; lean_object* v_checks_1185_; uint8_t v_fixedToolchain_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
v_toWorkspaceConfig_1152_ = lean_ctor_get(v_cfg_1151_, 0);
v_toLeanConfig_1153_ = lean_ctor_get(v_cfg_1151_, 1);
v_bootstrap_1154_ = lean_ctor_get_uint8(v_cfg_1151_, sizeof(void*)*28);
v_extraDepTargets_1155_ = lean_ctor_get(v_cfg_1151_, 2);
v_precompileModules_1156_ = lean_ctor_get_uint8(v_cfg_1151_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1157_ = lean_ctor_get(v_cfg_1151_, 3);
v_srcDir_1158_ = lean_ctor_get(v_cfg_1151_, 4);
v_buildDir_1159_ = lean_ctor_get(v_cfg_1151_, 5);
v_leanLibDir_1160_ = lean_ctor_get(v_cfg_1151_, 6);
v_nativeLibDir_1161_ = lean_ctor_get(v_cfg_1151_, 7);
v_binDir_1162_ = lean_ctor_get(v_cfg_1151_, 8);
v_irDir_1163_ = lean_ctor_get(v_cfg_1151_, 9);
v_releaseRepo_1164_ = lean_ctor_get(v_cfg_1151_, 10);
v_buildArchive_1165_ = lean_ctor_get(v_cfg_1151_, 11);
v_preferReleaseBuild_1166_ = lean_ctor_get_uint8(v_cfg_1151_, sizeof(void*)*28 + 2);
v_testDriver_1167_ = lean_ctor_get(v_cfg_1151_, 12);
v_testDriverArgs_1168_ = lean_ctor_get(v_cfg_1151_, 13);
v_lintDriver_1169_ = lean_ctor_get(v_cfg_1151_, 14);
v_lintDriverArgs_1170_ = lean_ctor_get(v_cfg_1151_, 15);
v_version_1171_ = lean_ctor_get(v_cfg_1151_, 16);
v_versionTags_1172_ = lean_ctor_get(v_cfg_1151_, 17);
v_description_1173_ = lean_ctor_get(v_cfg_1151_, 18);
v_keywords_1174_ = lean_ctor_get(v_cfg_1151_, 19);
v_homepage_1175_ = lean_ctor_get(v_cfg_1151_, 20);
v_license_1176_ = lean_ctor_get(v_cfg_1151_, 21);
v_licenseFiles_1177_ = lean_ctor_get(v_cfg_1151_, 22);
v_readmeFile_1178_ = lean_ctor_get(v_cfg_1151_, 23);
v_reservoir_1179_ = lean_ctor_get_uint8(v_cfg_1151_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1180_ = lean_ctor_get(v_cfg_1151_, 24);
v_restoreAllArtifacts_x3f_1181_ = lean_ctor_get(v_cfg_1151_, 25);
v_libPrefixOnWindows_1182_ = lean_ctor_get_uint8(v_cfg_1151_, sizeof(void*)*28 + 4);
v_allowImportAll_1183_ = lean_ctor_get_uint8(v_cfg_1151_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1184_ = lean_ctor_get(v_cfg_1151_, 26);
v_checks_1185_ = lean_ctor_get(v_cfg_1151_, 27);
v_fixedToolchain_1186_ = lean_ctor_get_uint8(v_cfg_1151_, sizeof(void*)*28 + 6);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_cfg_1151_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1188_ = v_cfg_1151_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_checks_1185_);
lean_inc(v_builtinLint_x3f_1184_);
lean_inc(v_restoreAllArtifacts_x3f_1181_);
lean_inc(v_enableArtifactCache_x3f_1180_);
lean_inc(v_readmeFile_1178_);
lean_inc(v_licenseFiles_1177_);
lean_inc(v_license_1176_);
lean_inc(v_homepage_1175_);
lean_inc(v_keywords_1174_);
lean_inc(v_description_1173_);
lean_inc(v_versionTags_1172_);
lean_inc(v_version_1171_);
lean_inc(v_lintDriverArgs_1170_);
lean_inc(v_lintDriver_1169_);
lean_inc(v_testDriverArgs_1168_);
lean_inc(v_testDriver_1167_);
lean_inc(v_buildArchive_1165_);
lean_inc(v_releaseRepo_1164_);
lean_inc(v_irDir_1163_);
lean_inc(v_binDir_1162_);
lean_inc(v_nativeLibDir_1161_);
lean_inc(v_leanLibDir_1160_);
lean_inc(v_buildDir_1159_);
lean_inc(v_srcDir_1158_);
lean_inc(v_moreGlobalServerArgs_1157_);
lean_inc(v_extraDepTargets_1155_);
lean_inc(v_toLeanConfig_1153_);
lean_inc(v_toWorkspaceConfig_1152_);
lean_dec(v_cfg_1151_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_apply_1(v_f_1150_, v_binDir_1162_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 8, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_toWorkspaceConfig_1152_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_toLeanConfig_1153_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_extraDepTargets_1155_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_moreGlobalServerArgs_1157_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_srcDir_1158_);
lean_ctor_set(v_reuseFailAlloc_1193_, 5, v_buildDir_1159_);
lean_ctor_set(v_reuseFailAlloc_1193_, 6, v_leanLibDir_1160_);
lean_ctor_set(v_reuseFailAlloc_1193_, 7, v_nativeLibDir_1161_);
lean_ctor_set(v_reuseFailAlloc_1193_, 8, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1193_, 9, v_irDir_1163_);
lean_ctor_set(v_reuseFailAlloc_1193_, 10, v_releaseRepo_1164_);
lean_ctor_set(v_reuseFailAlloc_1193_, 11, v_buildArchive_1165_);
lean_ctor_set(v_reuseFailAlloc_1193_, 12, v_testDriver_1167_);
lean_ctor_set(v_reuseFailAlloc_1193_, 13, v_testDriverArgs_1168_);
lean_ctor_set(v_reuseFailAlloc_1193_, 14, v_lintDriver_1169_);
lean_ctor_set(v_reuseFailAlloc_1193_, 15, v_lintDriverArgs_1170_);
lean_ctor_set(v_reuseFailAlloc_1193_, 16, v_version_1171_);
lean_ctor_set(v_reuseFailAlloc_1193_, 17, v_versionTags_1172_);
lean_ctor_set(v_reuseFailAlloc_1193_, 18, v_description_1173_);
lean_ctor_set(v_reuseFailAlloc_1193_, 19, v_keywords_1174_);
lean_ctor_set(v_reuseFailAlloc_1193_, 20, v_homepage_1175_);
lean_ctor_set(v_reuseFailAlloc_1193_, 21, v_license_1176_);
lean_ctor_set(v_reuseFailAlloc_1193_, 22, v_licenseFiles_1177_);
lean_ctor_set(v_reuseFailAlloc_1193_, 23, v_readmeFile_1178_);
lean_ctor_set(v_reuseFailAlloc_1193_, 24, v_enableArtifactCache_x3f_1180_);
lean_ctor_set(v_reuseFailAlloc_1193_, 25, v_restoreAllArtifacts_x3f_1181_);
lean_ctor_set(v_reuseFailAlloc_1193_, 26, v_builtinLint_x3f_1184_);
lean_ctor_set(v_reuseFailAlloc_1193_, 27, v_checks_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*28, v_bootstrap_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*28 + 1, v_precompileModules_1156_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1166_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*28 + 3, v_reservoir_1179_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*28 + 5, v_allowImportAll_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*28 + 6, v_fixedToolchain_1186_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__3(lean_object* v_x_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lake_defaultBinDir;
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__3___boxed(lean_object* v_x_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lake_PackageConfig_binDir___proj___redArg___lam__3(v_x_1197_);
lean_dec_ref(v_x_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg(){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = ((lean_object*)(l_Lake_PackageConfig_binDir___proj___redArg___closed__4));
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___boxed(lean_object* v___dummy_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lake_PackageConfig_binDir___proj___redArg();
return v_res_1211_;
}
}
static lean_object* _init_l_Lake_PackageConfig_binDir___proj___closed__0(void){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lake_PackageConfig_binDir___proj___redArg();
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object* v_p_1213_, lean_object* v_n_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_obj_once(&l_Lake_PackageConfig_binDir___proj___closed__0, &l_Lake_PackageConfig_binDir___proj___closed__0_once, _init_l_Lake_PackageConfig_binDir___proj___closed__0);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object* v_p_1216_, lean_object* v_n_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lake_PackageConfig_binDir___proj(v_p_1216_, v_n_1217_);
lean_dec(v_n_1217_);
lean_dec(v_p_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_obj_once(&l_Lake_PackageConfig_binDir___proj___closed__0, &l_Lake_PackageConfig_binDir___proj___closed__0_once, _init_l_Lake_PackageConfig_binDir___proj___closed__0);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___redArg___boxed(lean_object* v___dummy_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lake_PackageConfig_binDir_instConfigField___redArg();
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object* v_p_1223_, lean_object* v_n_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_obj_once(&l_Lake_PackageConfig_binDir___proj___closed__0, &l_Lake_PackageConfig_binDir___proj___closed__0_once, _init_l_Lake_PackageConfig_binDir___proj___closed__0);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object* v_p_1226_, lean_object* v_n_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lake_PackageConfig_binDir_instConfigField(v_p_1226_, v_n_1227_);
lean_dec(v_n_1227_);
lean_dec(v_p_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__0(lean_object* v_cfg_1229_){
_start:
{
lean_object* v_irDir_1230_; 
v_irDir_1230_ = lean_ctor_get(v_cfg_1229_, 9);
lean_inc_ref(v_irDir_1230_);
return v_irDir_1230_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lake_PackageConfig_irDir___proj___redArg___lam__0(v_cfg_1231_);
lean_dec_ref(v_cfg_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__1(lean_object* v_val_1233_, lean_object* v_cfg_1234_){
_start:
{
lean_object* v_toWorkspaceConfig_1235_; lean_object* v_toLeanConfig_1236_; uint8_t v_bootstrap_1237_; lean_object* v_extraDepTargets_1238_; uint8_t v_precompileModules_1239_; lean_object* v_moreGlobalServerArgs_1240_; lean_object* v_srcDir_1241_; lean_object* v_buildDir_1242_; lean_object* v_leanLibDir_1243_; lean_object* v_nativeLibDir_1244_; lean_object* v_binDir_1245_; lean_object* v_releaseRepo_1246_; lean_object* v_buildArchive_1247_; uint8_t v_preferReleaseBuild_1248_; lean_object* v_testDriver_1249_; lean_object* v_testDriverArgs_1250_; lean_object* v_lintDriver_1251_; lean_object* v_lintDriverArgs_1252_; lean_object* v_version_1253_; lean_object* v_versionTags_1254_; lean_object* v_description_1255_; lean_object* v_keywords_1256_; lean_object* v_homepage_1257_; lean_object* v_license_1258_; lean_object* v_licenseFiles_1259_; lean_object* v_readmeFile_1260_; uint8_t v_reservoir_1261_; lean_object* v_enableArtifactCache_x3f_1262_; lean_object* v_restoreAllArtifacts_x3f_1263_; uint8_t v_libPrefixOnWindows_1264_; uint8_t v_allowImportAll_1265_; lean_object* v_builtinLint_x3f_1266_; lean_object* v_checks_1267_; uint8_t v_fixedToolchain_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
v_toWorkspaceConfig_1235_ = lean_ctor_get(v_cfg_1234_, 0);
v_toLeanConfig_1236_ = lean_ctor_get(v_cfg_1234_, 1);
v_bootstrap_1237_ = lean_ctor_get_uint8(v_cfg_1234_, sizeof(void*)*28);
v_extraDepTargets_1238_ = lean_ctor_get(v_cfg_1234_, 2);
v_precompileModules_1239_ = lean_ctor_get_uint8(v_cfg_1234_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1240_ = lean_ctor_get(v_cfg_1234_, 3);
v_srcDir_1241_ = lean_ctor_get(v_cfg_1234_, 4);
v_buildDir_1242_ = lean_ctor_get(v_cfg_1234_, 5);
v_leanLibDir_1243_ = lean_ctor_get(v_cfg_1234_, 6);
v_nativeLibDir_1244_ = lean_ctor_get(v_cfg_1234_, 7);
v_binDir_1245_ = lean_ctor_get(v_cfg_1234_, 8);
v_releaseRepo_1246_ = lean_ctor_get(v_cfg_1234_, 10);
v_buildArchive_1247_ = lean_ctor_get(v_cfg_1234_, 11);
v_preferReleaseBuild_1248_ = lean_ctor_get_uint8(v_cfg_1234_, sizeof(void*)*28 + 2);
v_testDriver_1249_ = lean_ctor_get(v_cfg_1234_, 12);
v_testDriverArgs_1250_ = lean_ctor_get(v_cfg_1234_, 13);
v_lintDriver_1251_ = lean_ctor_get(v_cfg_1234_, 14);
v_lintDriverArgs_1252_ = lean_ctor_get(v_cfg_1234_, 15);
v_version_1253_ = lean_ctor_get(v_cfg_1234_, 16);
v_versionTags_1254_ = lean_ctor_get(v_cfg_1234_, 17);
v_description_1255_ = lean_ctor_get(v_cfg_1234_, 18);
v_keywords_1256_ = lean_ctor_get(v_cfg_1234_, 19);
v_homepage_1257_ = lean_ctor_get(v_cfg_1234_, 20);
v_license_1258_ = lean_ctor_get(v_cfg_1234_, 21);
v_licenseFiles_1259_ = lean_ctor_get(v_cfg_1234_, 22);
v_readmeFile_1260_ = lean_ctor_get(v_cfg_1234_, 23);
v_reservoir_1261_ = lean_ctor_get_uint8(v_cfg_1234_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1262_ = lean_ctor_get(v_cfg_1234_, 24);
v_restoreAllArtifacts_x3f_1263_ = lean_ctor_get(v_cfg_1234_, 25);
v_libPrefixOnWindows_1264_ = lean_ctor_get_uint8(v_cfg_1234_, sizeof(void*)*28 + 4);
v_allowImportAll_1265_ = lean_ctor_get_uint8(v_cfg_1234_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1266_ = lean_ctor_get(v_cfg_1234_, 26);
v_checks_1267_ = lean_ctor_get(v_cfg_1234_, 27);
v_fixedToolchain_1268_ = lean_ctor_get_uint8(v_cfg_1234_, sizeof(void*)*28 + 6);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_cfg_1234_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v_cfg_1234_, 9);
lean_dec(v_unused_1276_);
v___x_1270_ = v_cfg_1234_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_checks_1267_);
lean_inc(v_builtinLint_x3f_1266_);
lean_inc(v_restoreAllArtifacts_x3f_1263_);
lean_inc(v_enableArtifactCache_x3f_1262_);
lean_inc(v_readmeFile_1260_);
lean_inc(v_licenseFiles_1259_);
lean_inc(v_license_1258_);
lean_inc(v_homepage_1257_);
lean_inc(v_keywords_1256_);
lean_inc(v_description_1255_);
lean_inc(v_versionTags_1254_);
lean_inc(v_version_1253_);
lean_inc(v_lintDriverArgs_1252_);
lean_inc(v_lintDriver_1251_);
lean_inc(v_testDriverArgs_1250_);
lean_inc(v_testDriver_1249_);
lean_inc(v_buildArchive_1247_);
lean_inc(v_releaseRepo_1246_);
lean_inc(v_binDir_1245_);
lean_inc(v_nativeLibDir_1244_);
lean_inc(v_leanLibDir_1243_);
lean_inc(v_buildDir_1242_);
lean_inc(v_srcDir_1241_);
lean_inc(v_moreGlobalServerArgs_1240_);
lean_inc(v_extraDepTargets_1238_);
lean_inc(v_toLeanConfig_1236_);
lean_inc(v_toWorkspaceConfig_1235_);
lean_dec(v_cfg_1234_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 9, v_val_1233_);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_toWorkspaceConfig_1235_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_toLeanConfig_1236_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_extraDepTargets_1238_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_moreGlobalServerArgs_1240_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_srcDir_1241_);
lean_ctor_set(v_reuseFailAlloc_1274_, 5, v_buildDir_1242_);
lean_ctor_set(v_reuseFailAlloc_1274_, 6, v_leanLibDir_1243_);
lean_ctor_set(v_reuseFailAlloc_1274_, 7, v_nativeLibDir_1244_);
lean_ctor_set(v_reuseFailAlloc_1274_, 8, v_binDir_1245_);
lean_ctor_set(v_reuseFailAlloc_1274_, 9, v_val_1233_);
lean_ctor_set(v_reuseFailAlloc_1274_, 10, v_releaseRepo_1246_);
lean_ctor_set(v_reuseFailAlloc_1274_, 11, v_buildArchive_1247_);
lean_ctor_set(v_reuseFailAlloc_1274_, 12, v_testDriver_1249_);
lean_ctor_set(v_reuseFailAlloc_1274_, 13, v_testDriverArgs_1250_);
lean_ctor_set(v_reuseFailAlloc_1274_, 14, v_lintDriver_1251_);
lean_ctor_set(v_reuseFailAlloc_1274_, 15, v_lintDriverArgs_1252_);
lean_ctor_set(v_reuseFailAlloc_1274_, 16, v_version_1253_);
lean_ctor_set(v_reuseFailAlloc_1274_, 17, v_versionTags_1254_);
lean_ctor_set(v_reuseFailAlloc_1274_, 18, v_description_1255_);
lean_ctor_set(v_reuseFailAlloc_1274_, 19, v_keywords_1256_);
lean_ctor_set(v_reuseFailAlloc_1274_, 20, v_homepage_1257_);
lean_ctor_set(v_reuseFailAlloc_1274_, 21, v_license_1258_);
lean_ctor_set(v_reuseFailAlloc_1274_, 22, v_licenseFiles_1259_);
lean_ctor_set(v_reuseFailAlloc_1274_, 23, v_readmeFile_1260_);
lean_ctor_set(v_reuseFailAlloc_1274_, 24, v_enableArtifactCache_x3f_1262_);
lean_ctor_set(v_reuseFailAlloc_1274_, 25, v_restoreAllArtifacts_x3f_1263_);
lean_ctor_set(v_reuseFailAlloc_1274_, 26, v_builtinLint_x3f_1266_);
lean_ctor_set(v_reuseFailAlloc_1274_, 27, v_checks_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*28, v_bootstrap_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*28 + 1, v_precompileModules_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*28 + 3, v_reservoir_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*28 + 5, v_allowImportAll_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*28 + 6, v_fixedToolchain_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__2(lean_object* v_f_1277_, lean_object* v_cfg_1278_){
_start:
{
lean_object* v_toWorkspaceConfig_1279_; lean_object* v_toLeanConfig_1280_; uint8_t v_bootstrap_1281_; lean_object* v_extraDepTargets_1282_; uint8_t v_precompileModules_1283_; lean_object* v_moreGlobalServerArgs_1284_; lean_object* v_srcDir_1285_; lean_object* v_buildDir_1286_; lean_object* v_leanLibDir_1287_; lean_object* v_nativeLibDir_1288_; lean_object* v_binDir_1289_; lean_object* v_irDir_1290_; lean_object* v_releaseRepo_1291_; lean_object* v_buildArchive_1292_; uint8_t v_preferReleaseBuild_1293_; lean_object* v_testDriver_1294_; lean_object* v_testDriverArgs_1295_; lean_object* v_lintDriver_1296_; lean_object* v_lintDriverArgs_1297_; lean_object* v_version_1298_; lean_object* v_versionTags_1299_; lean_object* v_description_1300_; lean_object* v_keywords_1301_; lean_object* v_homepage_1302_; lean_object* v_license_1303_; lean_object* v_licenseFiles_1304_; lean_object* v_readmeFile_1305_; uint8_t v_reservoir_1306_; lean_object* v_enableArtifactCache_x3f_1307_; lean_object* v_restoreAllArtifacts_x3f_1308_; uint8_t v_libPrefixOnWindows_1309_; uint8_t v_allowImportAll_1310_; lean_object* v_builtinLint_x3f_1311_; lean_object* v_checks_1312_; uint8_t v_fixedToolchain_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1321_; 
v_toWorkspaceConfig_1279_ = lean_ctor_get(v_cfg_1278_, 0);
v_toLeanConfig_1280_ = lean_ctor_get(v_cfg_1278_, 1);
v_bootstrap_1281_ = lean_ctor_get_uint8(v_cfg_1278_, sizeof(void*)*28);
v_extraDepTargets_1282_ = lean_ctor_get(v_cfg_1278_, 2);
v_precompileModules_1283_ = lean_ctor_get_uint8(v_cfg_1278_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1284_ = lean_ctor_get(v_cfg_1278_, 3);
v_srcDir_1285_ = lean_ctor_get(v_cfg_1278_, 4);
v_buildDir_1286_ = lean_ctor_get(v_cfg_1278_, 5);
v_leanLibDir_1287_ = lean_ctor_get(v_cfg_1278_, 6);
v_nativeLibDir_1288_ = lean_ctor_get(v_cfg_1278_, 7);
v_binDir_1289_ = lean_ctor_get(v_cfg_1278_, 8);
v_irDir_1290_ = lean_ctor_get(v_cfg_1278_, 9);
v_releaseRepo_1291_ = lean_ctor_get(v_cfg_1278_, 10);
v_buildArchive_1292_ = lean_ctor_get(v_cfg_1278_, 11);
v_preferReleaseBuild_1293_ = lean_ctor_get_uint8(v_cfg_1278_, sizeof(void*)*28 + 2);
v_testDriver_1294_ = lean_ctor_get(v_cfg_1278_, 12);
v_testDriverArgs_1295_ = lean_ctor_get(v_cfg_1278_, 13);
v_lintDriver_1296_ = lean_ctor_get(v_cfg_1278_, 14);
v_lintDriverArgs_1297_ = lean_ctor_get(v_cfg_1278_, 15);
v_version_1298_ = lean_ctor_get(v_cfg_1278_, 16);
v_versionTags_1299_ = lean_ctor_get(v_cfg_1278_, 17);
v_description_1300_ = lean_ctor_get(v_cfg_1278_, 18);
v_keywords_1301_ = lean_ctor_get(v_cfg_1278_, 19);
v_homepage_1302_ = lean_ctor_get(v_cfg_1278_, 20);
v_license_1303_ = lean_ctor_get(v_cfg_1278_, 21);
v_licenseFiles_1304_ = lean_ctor_get(v_cfg_1278_, 22);
v_readmeFile_1305_ = lean_ctor_get(v_cfg_1278_, 23);
v_reservoir_1306_ = lean_ctor_get_uint8(v_cfg_1278_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1307_ = lean_ctor_get(v_cfg_1278_, 24);
v_restoreAllArtifacts_x3f_1308_ = lean_ctor_get(v_cfg_1278_, 25);
v_libPrefixOnWindows_1309_ = lean_ctor_get_uint8(v_cfg_1278_, sizeof(void*)*28 + 4);
v_allowImportAll_1310_ = lean_ctor_get_uint8(v_cfg_1278_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1311_ = lean_ctor_get(v_cfg_1278_, 26);
v_checks_1312_ = lean_ctor_get(v_cfg_1278_, 27);
v_fixedToolchain_1313_ = lean_ctor_get_uint8(v_cfg_1278_, sizeof(void*)*28 + 6);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_cfg_1278_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1315_ = v_cfg_1278_;
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_checks_1312_);
lean_inc(v_builtinLint_x3f_1311_);
lean_inc(v_restoreAllArtifacts_x3f_1308_);
lean_inc(v_enableArtifactCache_x3f_1307_);
lean_inc(v_readmeFile_1305_);
lean_inc(v_licenseFiles_1304_);
lean_inc(v_license_1303_);
lean_inc(v_homepage_1302_);
lean_inc(v_keywords_1301_);
lean_inc(v_description_1300_);
lean_inc(v_versionTags_1299_);
lean_inc(v_version_1298_);
lean_inc(v_lintDriverArgs_1297_);
lean_inc(v_lintDriver_1296_);
lean_inc(v_testDriverArgs_1295_);
lean_inc(v_testDriver_1294_);
lean_inc(v_buildArchive_1292_);
lean_inc(v_releaseRepo_1291_);
lean_inc(v_irDir_1290_);
lean_inc(v_binDir_1289_);
lean_inc(v_nativeLibDir_1288_);
lean_inc(v_leanLibDir_1287_);
lean_inc(v_buildDir_1286_);
lean_inc(v_srcDir_1285_);
lean_inc(v_moreGlobalServerArgs_1284_);
lean_inc(v_extraDepTargets_1282_);
lean_inc(v_toLeanConfig_1280_);
lean_inc(v_toWorkspaceConfig_1279_);
lean_dec(v_cfg_1278_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = lean_apply_1(v_f_1277_, v_irDir_1290_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 9, v___x_1317_);
v___x_1319_ = v___x_1315_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_toWorkspaceConfig_1279_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_toLeanConfig_1280_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_extraDepTargets_1282_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v_moreGlobalServerArgs_1284_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v_srcDir_1285_);
lean_ctor_set(v_reuseFailAlloc_1320_, 5, v_buildDir_1286_);
lean_ctor_set(v_reuseFailAlloc_1320_, 6, v_leanLibDir_1287_);
lean_ctor_set(v_reuseFailAlloc_1320_, 7, v_nativeLibDir_1288_);
lean_ctor_set(v_reuseFailAlloc_1320_, 8, v_binDir_1289_);
lean_ctor_set(v_reuseFailAlloc_1320_, 9, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1320_, 10, v_releaseRepo_1291_);
lean_ctor_set(v_reuseFailAlloc_1320_, 11, v_buildArchive_1292_);
lean_ctor_set(v_reuseFailAlloc_1320_, 12, v_testDriver_1294_);
lean_ctor_set(v_reuseFailAlloc_1320_, 13, v_testDriverArgs_1295_);
lean_ctor_set(v_reuseFailAlloc_1320_, 14, v_lintDriver_1296_);
lean_ctor_set(v_reuseFailAlloc_1320_, 15, v_lintDriverArgs_1297_);
lean_ctor_set(v_reuseFailAlloc_1320_, 16, v_version_1298_);
lean_ctor_set(v_reuseFailAlloc_1320_, 17, v_versionTags_1299_);
lean_ctor_set(v_reuseFailAlloc_1320_, 18, v_description_1300_);
lean_ctor_set(v_reuseFailAlloc_1320_, 19, v_keywords_1301_);
lean_ctor_set(v_reuseFailAlloc_1320_, 20, v_homepage_1302_);
lean_ctor_set(v_reuseFailAlloc_1320_, 21, v_license_1303_);
lean_ctor_set(v_reuseFailAlloc_1320_, 22, v_licenseFiles_1304_);
lean_ctor_set(v_reuseFailAlloc_1320_, 23, v_readmeFile_1305_);
lean_ctor_set(v_reuseFailAlloc_1320_, 24, v_enableArtifactCache_x3f_1307_);
lean_ctor_set(v_reuseFailAlloc_1320_, 25, v_restoreAllArtifacts_x3f_1308_);
lean_ctor_set(v_reuseFailAlloc_1320_, 26, v_builtinLint_x3f_1311_);
lean_ctor_set(v_reuseFailAlloc_1320_, 27, v_checks_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*28, v_bootstrap_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*28 + 1, v_precompileModules_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*28 + 3, v_reservoir_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*28 + 5, v_allowImportAll_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*28 + 6, v_fixedToolchain_1313_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__3(lean_object* v_x_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lake_defaultIrDir;
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__3___boxed(lean_object* v_x_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lake_PackageConfig_irDir___proj___redArg___lam__3(v_x_1324_);
lean_dec_ref(v_x_1324_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg(){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = ((lean_object*)(l_Lake_PackageConfig_irDir___proj___redArg___closed__4));
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___boxed(lean_object* v___dummy_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lake_PackageConfig_irDir___proj___redArg();
return v_res_1338_;
}
}
static lean_object* _init_l_Lake_PackageConfig_irDir___proj___closed__0(void){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lake_PackageConfig_irDir___proj___redArg();
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object* v_p_1340_, lean_object* v_n_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_obj_once(&l_Lake_PackageConfig_irDir___proj___closed__0, &l_Lake_PackageConfig_irDir___proj___closed__0_once, _init_l_Lake_PackageConfig_irDir___proj___closed__0);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object* v_p_1343_, lean_object* v_n_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lake_PackageConfig_irDir___proj(v_p_1343_, v_n_1344_);
lean_dec(v_n_1344_);
lean_dec(v_p_1343_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_obj_once(&l_Lake_PackageConfig_irDir___proj___closed__0, &l_Lake_PackageConfig_irDir___proj___closed__0_once, _init_l_Lake_PackageConfig_irDir___proj___closed__0);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___redArg___boxed(lean_object* v___dummy_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lake_PackageConfig_irDir_instConfigField___redArg();
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object* v_p_1350_, lean_object* v_n_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_obj_once(&l_Lake_PackageConfig_irDir___proj___closed__0, &l_Lake_PackageConfig_irDir___proj___closed__0_once, _init_l_Lake_PackageConfig_irDir___proj___closed__0);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object* v_p_1353_, lean_object* v_n_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lake_PackageConfig_irDir_instConfigField(v_p_1353_, v_n_1354_);
lean_dec(v_n_1354_);
lean_dec(v_p_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0(lean_object* v_cfg_1356_){
_start:
{
lean_object* v_releaseRepo_1357_; 
v_releaseRepo_1357_ = lean_ctor_get(v_cfg_1356_, 10);
lean_inc(v_releaseRepo_1357_);
return v_releaseRepo_1357_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0___boxed(lean_object* v_cfg_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0(v_cfg_1358_);
lean_dec_ref(v_cfg_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__1(lean_object* v_val_1360_, lean_object* v_cfg_1361_){
_start:
{
lean_object* v_toWorkspaceConfig_1362_; lean_object* v_toLeanConfig_1363_; uint8_t v_bootstrap_1364_; lean_object* v_extraDepTargets_1365_; uint8_t v_precompileModules_1366_; lean_object* v_moreGlobalServerArgs_1367_; lean_object* v_srcDir_1368_; lean_object* v_buildDir_1369_; lean_object* v_leanLibDir_1370_; lean_object* v_nativeLibDir_1371_; lean_object* v_binDir_1372_; lean_object* v_irDir_1373_; lean_object* v_buildArchive_1374_; uint8_t v_preferReleaseBuild_1375_; lean_object* v_testDriver_1376_; lean_object* v_testDriverArgs_1377_; lean_object* v_lintDriver_1378_; lean_object* v_lintDriverArgs_1379_; lean_object* v_version_1380_; lean_object* v_versionTags_1381_; lean_object* v_description_1382_; lean_object* v_keywords_1383_; lean_object* v_homepage_1384_; lean_object* v_license_1385_; lean_object* v_licenseFiles_1386_; lean_object* v_readmeFile_1387_; uint8_t v_reservoir_1388_; lean_object* v_enableArtifactCache_x3f_1389_; lean_object* v_restoreAllArtifacts_x3f_1390_; uint8_t v_libPrefixOnWindows_1391_; uint8_t v_allowImportAll_1392_; lean_object* v_builtinLint_x3f_1393_; lean_object* v_checks_1394_; uint8_t v_fixedToolchain_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
v_toWorkspaceConfig_1362_ = lean_ctor_get(v_cfg_1361_, 0);
v_toLeanConfig_1363_ = lean_ctor_get(v_cfg_1361_, 1);
v_bootstrap_1364_ = lean_ctor_get_uint8(v_cfg_1361_, sizeof(void*)*28);
v_extraDepTargets_1365_ = lean_ctor_get(v_cfg_1361_, 2);
v_precompileModules_1366_ = lean_ctor_get_uint8(v_cfg_1361_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1367_ = lean_ctor_get(v_cfg_1361_, 3);
v_srcDir_1368_ = lean_ctor_get(v_cfg_1361_, 4);
v_buildDir_1369_ = lean_ctor_get(v_cfg_1361_, 5);
v_leanLibDir_1370_ = lean_ctor_get(v_cfg_1361_, 6);
v_nativeLibDir_1371_ = lean_ctor_get(v_cfg_1361_, 7);
v_binDir_1372_ = lean_ctor_get(v_cfg_1361_, 8);
v_irDir_1373_ = lean_ctor_get(v_cfg_1361_, 9);
v_buildArchive_1374_ = lean_ctor_get(v_cfg_1361_, 11);
v_preferReleaseBuild_1375_ = lean_ctor_get_uint8(v_cfg_1361_, sizeof(void*)*28 + 2);
v_testDriver_1376_ = lean_ctor_get(v_cfg_1361_, 12);
v_testDriverArgs_1377_ = lean_ctor_get(v_cfg_1361_, 13);
v_lintDriver_1378_ = lean_ctor_get(v_cfg_1361_, 14);
v_lintDriverArgs_1379_ = lean_ctor_get(v_cfg_1361_, 15);
v_version_1380_ = lean_ctor_get(v_cfg_1361_, 16);
v_versionTags_1381_ = lean_ctor_get(v_cfg_1361_, 17);
v_description_1382_ = lean_ctor_get(v_cfg_1361_, 18);
v_keywords_1383_ = lean_ctor_get(v_cfg_1361_, 19);
v_homepage_1384_ = lean_ctor_get(v_cfg_1361_, 20);
v_license_1385_ = lean_ctor_get(v_cfg_1361_, 21);
v_licenseFiles_1386_ = lean_ctor_get(v_cfg_1361_, 22);
v_readmeFile_1387_ = lean_ctor_get(v_cfg_1361_, 23);
v_reservoir_1388_ = lean_ctor_get_uint8(v_cfg_1361_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1389_ = lean_ctor_get(v_cfg_1361_, 24);
v_restoreAllArtifacts_x3f_1390_ = lean_ctor_get(v_cfg_1361_, 25);
v_libPrefixOnWindows_1391_ = lean_ctor_get_uint8(v_cfg_1361_, sizeof(void*)*28 + 4);
v_allowImportAll_1392_ = lean_ctor_get_uint8(v_cfg_1361_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1393_ = lean_ctor_get(v_cfg_1361_, 26);
v_checks_1394_ = lean_ctor_get(v_cfg_1361_, 27);
v_fixedToolchain_1395_ = lean_ctor_get_uint8(v_cfg_1361_, sizeof(void*)*28 + 6);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_cfg_1361_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v_cfg_1361_, 10);
lean_dec(v_unused_1403_);
v___x_1397_ = v_cfg_1361_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_checks_1394_);
lean_inc(v_builtinLint_x3f_1393_);
lean_inc(v_restoreAllArtifacts_x3f_1390_);
lean_inc(v_enableArtifactCache_x3f_1389_);
lean_inc(v_readmeFile_1387_);
lean_inc(v_licenseFiles_1386_);
lean_inc(v_license_1385_);
lean_inc(v_homepage_1384_);
lean_inc(v_keywords_1383_);
lean_inc(v_description_1382_);
lean_inc(v_versionTags_1381_);
lean_inc(v_version_1380_);
lean_inc(v_lintDriverArgs_1379_);
lean_inc(v_lintDriver_1378_);
lean_inc(v_testDriverArgs_1377_);
lean_inc(v_testDriver_1376_);
lean_inc(v_buildArchive_1374_);
lean_inc(v_irDir_1373_);
lean_inc(v_binDir_1372_);
lean_inc(v_nativeLibDir_1371_);
lean_inc(v_leanLibDir_1370_);
lean_inc(v_buildDir_1369_);
lean_inc(v_srcDir_1368_);
lean_inc(v_moreGlobalServerArgs_1367_);
lean_inc(v_extraDepTargets_1365_);
lean_inc(v_toLeanConfig_1363_);
lean_inc(v_toWorkspaceConfig_1362_);
lean_dec(v_cfg_1361_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 10, v_val_1360_);
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_toWorkspaceConfig_1362_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_toLeanConfig_1363_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_extraDepTargets_1365_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_moreGlobalServerArgs_1367_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_srcDir_1368_);
lean_ctor_set(v_reuseFailAlloc_1401_, 5, v_buildDir_1369_);
lean_ctor_set(v_reuseFailAlloc_1401_, 6, v_leanLibDir_1370_);
lean_ctor_set(v_reuseFailAlloc_1401_, 7, v_nativeLibDir_1371_);
lean_ctor_set(v_reuseFailAlloc_1401_, 8, v_binDir_1372_);
lean_ctor_set(v_reuseFailAlloc_1401_, 9, v_irDir_1373_);
lean_ctor_set(v_reuseFailAlloc_1401_, 10, v_val_1360_);
lean_ctor_set(v_reuseFailAlloc_1401_, 11, v_buildArchive_1374_);
lean_ctor_set(v_reuseFailAlloc_1401_, 12, v_testDriver_1376_);
lean_ctor_set(v_reuseFailAlloc_1401_, 13, v_testDriverArgs_1377_);
lean_ctor_set(v_reuseFailAlloc_1401_, 14, v_lintDriver_1378_);
lean_ctor_set(v_reuseFailAlloc_1401_, 15, v_lintDriverArgs_1379_);
lean_ctor_set(v_reuseFailAlloc_1401_, 16, v_version_1380_);
lean_ctor_set(v_reuseFailAlloc_1401_, 17, v_versionTags_1381_);
lean_ctor_set(v_reuseFailAlloc_1401_, 18, v_description_1382_);
lean_ctor_set(v_reuseFailAlloc_1401_, 19, v_keywords_1383_);
lean_ctor_set(v_reuseFailAlloc_1401_, 20, v_homepage_1384_);
lean_ctor_set(v_reuseFailAlloc_1401_, 21, v_license_1385_);
lean_ctor_set(v_reuseFailAlloc_1401_, 22, v_licenseFiles_1386_);
lean_ctor_set(v_reuseFailAlloc_1401_, 23, v_readmeFile_1387_);
lean_ctor_set(v_reuseFailAlloc_1401_, 24, v_enableArtifactCache_x3f_1389_);
lean_ctor_set(v_reuseFailAlloc_1401_, 25, v_restoreAllArtifacts_x3f_1390_);
lean_ctor_set(v_reuseFailAlloc_1401_, 26, v_builtinLint_x3f_1393_);
lean_ctor_set(v_reuseFailAlloc_1401_, 27, v_checks_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, sizeof(void*)*28, v_bootstrap_1364_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, sizeof(void*)*28 + 1, v_precompileModules_1366_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1375_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, sizeof(void*)*28 + 3, v_reservoir_1388_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, sizeof(void*)*28 + 5, v_allowImportAll_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, sizeof(void*)*28 + 6, v_fixedToolchain_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__2(lean_object* v_f_1404_, lean_object* v_cfg_1405_){
_start:
{
lean_object* v_toWorkspaceConfig_1406_; lean_object* v_toLeanConfig_1407_; uint8_t v_bootstrap_1408_; lean_object* v_extraDepTargets_1409_; uint8_t v_precompileModules_1410_; lean_object* v_moreGlobalServerArgs_1411_; lean_object* v_srcDir_1412_; lean_object* v_buildDir_1413_; lean_object* v_leanLibDir_1414_; lean_object* v_nativeLibDir_1415_; lean_object* v_binDir_1416_; lean_object* v_irDir_1417_; lean_object* v_releaseRepo_1418_; lean_object* v_buildArchive_1419_; uint8_t v_preferReleaseBuild_1420_; lean_object* v_testDriver_1421_; lean_object* v_testDriverArgs_1422_; lean_object* v_lintDriver_1423_; lean_object* v_lintDriverArgs_1424_; lean_object* v_version_1425_; lean_object* v_versionTags_1426_; lean_object* v_description_1427_; lean_object* v_keywords_1428_; lean_object* v_homepage_1429_; lean_object* v_license_1430_; lean_object* v_licenseFiles_1431_; lean_object* v_readmeFile_1432_; uint8_t v_reservoir_1433_; lean_object* v_enableArtifactCache_x3f_1434_; lean_object* v_restoreAllArtifacts_x3f_1435_; uint8_t v_libPrefixOnWindows_1436_; uint8_t v_allowImportAll_1437_; lean_object* v_builtinLint_x3f_1438_; lean_object* v_checks_1439_; uint8_t v_fixedToolchain_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1448_; 
v_toWorkspaceConfig_1406_ = lean_ctor_get(v_cfg_1405_, 0);
v_toLeanConfig_1407_ = lean_ctor_get(v_cfg_1405_, 1);
v_bootstrap_1408_ = lean_ctor_get_uint8(v_cfg_1405_, sizeof(void*)*28);
v_extraDepTargets_1409_ = lean_ctor_get(v_cfg_1405_, 2);
v_precompileModules_1410_ = lean_ctor_get_uint8(v_cfg_1405_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1411_ = lean_ctor_get(v_cfg_1405_, 3);
v_srcDir_1412_ = lean_ctor_get(v_cfg_1405_, 4);
v_buildDir_1413_ = lean_ctor_get(v_cfg_1405_, 5);
v_leanLibDir_1414_ = lean_ctor_get(v_cfg_1405_, 6);
v_nativeLibDir_1415_ = lean_ctor_get(v_cfg_1405_, 7);
v_binDir_1416_ = lean_ctor_get(v_cfg_1405_, 8);
v_irDir_1417_ = lean_ctor_get(v_cfg_1405_, 9);
v_releaseRepo_1418_ = lean_ctor_get(v_cfg_1405_, 10);
v_buildArchive_1419_ = lean_ctor_get(v_cfg_1405_, 11);
v_preferReleaseBuild_1420_ = lean_ctor_get_uint8(v_cfg_1405_, sizeof(void*)*28 + 2);
v_testDriver_1421_ = lean_ctor_get(v_cfg_1405_, 12);
v_testDriverArgs_1422_ = lean_ctor_get(v_cfg_1405_, 13);
v_lintDriver_1423_ = lean_ctor_get(v_cfg_1405_, 14);
v_lintDriverArgs_1424_ = lean_ctor_get(v_cfg_1405_, 15);
v_version_1425_ = lean_ctor_get(v_cfg_1405_, 16);
v_versionTags_1426_ = lean_ctor_get(v_cfg_1405_, 17);
v_description_1427_ = lean_ctor_get(v_cfg_1405_, 18);
v_keywords_1428_ = lean_ctor_get(v_cfg_1405_, 19);
v_homepage_1429_ = lean_ctor_get(v_cfg_1405_, 20);
v_license_1430_ = lean_ctor_get(v_cfg_1405_, 21);
v_licenseFiles_1431_ = lean_ctor_get(v_cfg_1405_, 22);
v_readmeFile_1432_ = lean_ctor_get(v_cfg_1405_, 23);
v_reservoir_1433_ = lean_ctor_get_uint8(v_cfg_1405_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1434_ = lean_ctor_get(v_cfg_1405_, 24);
v_restoreAllArtifacts_x3f_1435_ = lean_ctor_get(v_cfg_1405_, 25);
v_libPrefixOnWindows_1436_ = lean_ctor_get_uint8(v_cfg_1405_, sizeof(void*)*28 + 4);
v_allowImportAll_1437_ = lean_ctor_get_uint8(v_cfg_1405_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1438_ = lean_ctor_get(v_cfg_1405_, 26);
v_checks_1439_ = lean_ctor_get(v_cfg_1405_, 27);
v_fixedToolchain_1440_ = lean_ctor_get_uint8(v_cfg_1405_, sizeof(void*)*28 + 6);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_cfg_1405_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1442_ = v_cfg_1405_;
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_checks_1439_);
lean_inc(v_builtinLint_x3f_1438_);
lean_inc(v_restoreAllArtifacts_x3f_1435_);
lean_inc(v_enableArtifactCache_x3f_1434_);
lean_inc(v_readmeFile_1432_);
lean_inc(v_licenseFiles_1431_);
lean_inc(v_license_1430_);
lean_inc(v_homepage_1429_);
lean_inc(v_keywords_1428_);
lean_inc(v_description_1427_);
lean_inc(v_versionTags_1426_);
lean_inc(v_version_1425_);
lean_inc(v_lintDriverArgs_1424_);
lean_inc(v_lintDriver_1423_);
lean_inc(v_testDriverArgs_1422_);
lean_inc(v_testDriver_1421_);
lean_inc(v_buildArchive_1419_);
lean_inc(v_releaseRepo_1418_);
lean_inc(v_irDir_1417_);
lean_inc(v_binDir_1416_);
lean_inc(v_nativeLibDir_1415_);
lean_inc(v_leanLibDir_1414_);
lean_inc(v_buildDir_1413_);
lean_inc(v_srcDir_1412_);
lean_inc(v_moreGlobalServerArgs_1411_);
lean_inc(v_extraDepTargets_1409_);
lean_inc(v_toLeanConfig_1407_);
lean_inc(v_toWorkspaceConfig_1406_);
lean_dec(v_cfg_1405_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_apply_1(v_f_1404_, v_releaseRepo_1418_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 10, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_toWorkspaceConfig_1406_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_toLeanConfig_1407_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_extraDepTargets_1409_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_moreGlobalServerArgs_1411_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_srcDir_1412_);
lean_ctor_set(v_reuseFailAlloc_1447_, 5, v_buildDir_1413_);
lean_ctor_set(v_reuseFailAlloc_1447_, 6, v_leanLibDir_1414_);
lean_ctor_set(v_reuseFailAlloc_1447_, 7, v_nativeLibDir_1415_);
lean_ctor_set(v_reuseFailAlloc_1447_, 8, v_binDir_1416_);
lean_ctor_set(v_reuseFailAlloc_1447_, 9, v_irDir_1417_);
lean_ctor_set(v_reuseFailAlloc_1447_, 10, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1447_, 11, v_buildArchive_1419_);
lean_ctor_set(v_reuseFailAlloc_1447_, 12, v_testDriver_1421_);
lean_ctor_set(v_reuseFailAlloc_1447_, 13, v_testDriverArgs_1422_);
lean_ctor_set(v_reuseFailAlloc_1447_, 14, v_lintDriver_1423_);
lean_ctor_set(v_reuseFailAlloc_1447_, 15, v_lintDriverArgs_1424_);
lean_ctor_set(v_reuseFailAlloc_1447_, 16, v_version_1425_);
lean_ctor_set(v_reuseFailAlloc_1447_, 17, v_versionTags_1426_);
lean_ctor_set(v_reuseFailAlloc_1447_, 18, v_description_1427_);
lean_ctor_set(v_reuseFailAlloc_1447_, 19, v_keywords_1428_);
lean_ctor_set(v_reuseFailAlloc_1447_, 20, v_homepage_1429_);
lean_ctor_set(v_reuseFailAlloc_1447_, 21, v_license_1430_);
lean_ctor_set(v_reuseFailAlloc_1447_, 22, v_licenseFiles_1431_);
lean_ctor_set(v_reuseFailAlloc_1447_, 23, v_readmeFile_1432_);
lean_ctor_set(v_reuseFailAlloc_1447_, 24, v_enableArtifactCache_x3f_1434_);
lean_ctor_set(v_reuseFailAlloc_1447_, 25, v_restoreAllArtifacts_x3f_1435_);
lean_ctor_set(v_reuseFailAlloc_1447_, 26, v_builtinLint_x3f_1438_);
lean_ctor_set(v_reuseFailAlloc_1447_, 27, v_checks_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*28, v_bootstrap_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*28 + 1, v_precompileModules_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1420_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*28 + 3, v_reservoir_1433_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*28 + 5, v_allowImportAll_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*28 + 6, v_fixedToolchain_1440_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3(lean_object* v_x_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_box(0);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3___boxed(lean_object* v_x_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3(v_x_1451_);
lean_dec_ref(v_x_1451_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg(){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = ((lean_object*)(l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__4));
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___boxed(lean_object* v___dummy_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lake_PackageConfig_releaseRepo___proj___redArg();
return v_res_1465_;
}
}
static lean_object* _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0(void){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lake_PackageConfig_releaseRepo___proj___redArg();
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object* v_p_1467_, lean_object* v_n_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object* v_p_1470_, lean_object* v_n_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1470_, v_n_1471_);
lean_dec(v_n_1471_);
lean_dec(v_p_1470_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___redArg(){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___redArg___boxed(lean_object* v___dummy_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lake_PackageConfig_releaseRepo_instConfigField___redArg();
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object* v_p_1477_, lean_object* v_n_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object* v_p_1480_, lean_object* v_n_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lake_PackageConfig_releaseRepo_instConfigField(v_p_1480_, v_n_1481_);
lean_dec(v_n_1481_);
lean_dec(v_p_1480_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg();
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object* v_p_1487_, lean_object* v_n_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object* v_p_1490_, lean_object* v_n_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(v_p_1490_, v_n_1491_);
lean_dec(v_n_1491_);
lean_dec(v_p_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0(lean_object* v_cfg_1493_){
_start:
{
lean_object* v_buildArchive_1494_; 
v_buildArchive_1494_ = lean_ctor_get(v_cfg_1493_, 11);
lean_inc(v_buildArchive_1494_);
return v_buildArchive_1494_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0___boxed(lean_object* v_cfg_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0(v_cfg_1495_);
lean_dec_ref(v_cfg_1495_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__1(lean_object* v_val_1497_, lean_object* v_cfg_1498_){
_start:
{
lean_object* v_toWorkspaceConfig_1499_; lean_object* v_toLeanConfig_1500_; uint8_t v_bootstrap_1501_; lean_object* v_extraDepTargets_1502_; uint8_t v_precompileModules_1503_; lean_object* v_moreGlobalServerArgs_1504_; lean_object* v_srcDir_1505_; lean_object* v_buildDir_1506_; lean_object* v_leanLibDir_1507_; lean_object* v_nativeLibDir_1508_; lean_object* v_binDir_1509_; lean_object* v_irDir_1510_; lean_object* v_releaseRepo_1511_; uint8_t v_preferReleaseBuild_1512_; lean_object* v_testDriver_1513_; lean_object* v_testDriverArgs_1514_; lean_object* v_lintDriver_1515_; lean_object* v_lintDriverArgs_1516_; lean_object* v_version_1517_; lean_object* v_versionTags_1518_; lean_object* v_description_1519_; lean_object* v_keywords_1520_; lean_object* v_homepage_1521_; lean_object* v_license_1522_; lean_object* v_licenseFiles_1523_; lean_object* v_readmeFile_1524_; uint8_t v_reservoir_1525_; lean_object* v_enableArtifactCache_x3f_1526_; lean_object* v_restoreAllArtifacts_x3f_1527_; uint8_t v_libPrefixOnWindows_1528_; uint8_t v_allowImportAll_1529_; lean_object* v_builtinLint_x3f_1530_; lean_object* v_checks_1531_; uint8_t v_fixedToolchain_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_toWorkspaceConfig_1499_ = lean_ctor_get(v_cfg_1498_, 0);
v_toLeanConfig_1500_ = lean_ctor_get(v_cfg_1498_, 1);
v_bootstrap_1501_ = lean_ctor_get_uint8(v_cfg_1498_, sizeof(void*)*28);
v_extraDepTargets_1502_ = lean_ctor_get(v_cfg_1498_, 2);
v_precompileModules_1503_ = lean_ctor_get_uint8(v_cfg_1498_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1504_ = lean_ctor_get(v_cfg_1498_, 3);
v_srcDir_1505_ = lean_ctor_get(v_cfg_1498_, 4);
v_buildDir_1506_ = lean_ctor_get(v_cfg_1498_, 5);
v_leanLibDir_1507_ = lean_ctor_get(v_cfg_1498_, 6);
v_nativeLibDir_1508_ = lean_ctor_get(v_cfg_1498_, 7);
v_binDir_1509_ = lean_ctor_get(v_cfg_1498_, 8);
v_irDir_1510_ = lean_ctor_get(v_cfg_1498_, 9);
v_releaseRepo_1511_ = lean_ctor_get(v_cfg_1498_, 10);
v_preferReleaseBuild_1512_ = lean_ctor_get_uint8(v_cfg_1498_, sizeof(void*)*28 + 2);
v_testDriver_1513_ = lean_ctor_get(v_cfg_1498_, 12);
v_testDriverArgs_1514_ = lean_ctor_get(v_cfg_1498_, 13);
v_lintDriver_1515_ = lean_ctor_get(v_cfg_1498_, 14);
v_lintDriverArgs_1516_ = lean_ctor_get(v_cfg_1498_, 15);
v_version_1517_ = lean_ctor_get(v_cfg_1498_, 16);
v_versionTags_1518_ = lean_ctor_get(v_cfg_1498_, 17);
v_description_1519_ = lean_ctor_get(v_cfg_1498_, 18);
v_keywords_1520_ = lean_ctor_get(v_cfg_1498_, 19);
v_homepage_1521_ = lean_ctor_get(v_cfg_1498_, 20);
v_license_1522_ = lean_ctor_get(v_cfg_1498_, 21);
v_licenseFiles_1523_ = lean_ctor_get(v_cfg_1498_, 22);
v_readmeFile_1524_ = lean_ctor_get(v_cfg_1498_, 23);
v_reservoir_1525_ = lean_ctor_get_uint8(v_cfg_1498_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1526_ = lean_ctor_get(v_cfg_1498_, 24);
v_restoreAllArtifacts_x3f_1527_ = lean_ctor_get(v_cfg_1498_, 25);
v_libPrefixOnWindows_1528_ = lean_ctor_get_uint8(v_cfg_1498_, sizeof(void*)*28 + 4);
v_allowImportAll_1529_ = lean_ctor_get_uint8(v_cfg_1498_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1530_ = lean_ctor_get(v_cfg_1498_, 26);
v_checks_1531_ = lean_ctor_get(v_cfg_1498_, 27);
v_fixedToolchain_1532_ = lean_ctor_get_uint8(v_cfg_1498_, sizeof(void*)*28 + 6);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_cfg_1498_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v_cfg_1498_, 11);
lean_dec(v_unused_1540_);
v___x_1534_ = v_cfg_1498_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_checks_1531_);
lean_inc(v_builtinLint_x3f_1530_);
lean_inc(v_restoreAllArtifacts_x3f_1527_);
lean_inc(v_enableArtifactCache_x3f_1526_);
lean_inc(v_readmeFile_1524_);
lean_inc(v_licenseFiles_1523_);
lean_inc(v_license_1522_);
lean_inc(v_homepage_1521_);
lean_inc(v_keywords_1520_);
lean_inc(v_description_1519_);
lean_inc(v_versionTags_1518_);
lean_inc(v_version_1517_);
lean_inc(v_lintDriverArgs_1516_);
lean_inc(v_lintDriver_1515_);
lean_inc(v_testDriverArgs_1514_);
lean_inc(v_testDriver_1513_);
lean_inc(v_releaseRepo_1511_);
lean_inc(v_irDir_1510_);
lean_inc(v_binDir_1509_);
lean_inc(v_nativeLibDir_1508_);
lean_inc(v_leanLibDir_1507_);
lean_inc(v_buildDir_1506_);
lean_inc(v_srcDir_1505_);
lean_inc(v_moreGlobalServerArgs_1504_);
lean_inc(v_extraDepTargets_1502_);
lean_inc(v_toLeanConfig_1500_);
lean_inc(v_toWorkspaceConfig_1499_);
lean_dec(v_cfg_1498_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 11, v_val_1497_);
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_toWorkspaceConfig_1499_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_toLeanConfig_1500_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_extraDepTargets_1502_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_moreGlobalServerArgs_1504_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_srcDir_1505_);
lean_ctor_set(v_reuseFailAlloc_1538_, 5, v_buildDir_1506_);
lean_ctor_set(v_reuseFailAlloc_1538_, 6, v_leanLibDir_1507_);
lean_ctor_set(v_reuseFailAlloc_1538_, 7, v_nativeLibDir_1508_);
lean_ctor_set(v_reuseFailAlloc_1538_, 8, v_binDir_1509_);
lean_ctor_set(v_reuseFailAlloc_1538_, 9, v_irDir_1510_);
lean_ctor_set(v_reuseFailAlloc_1538_, 10, v_releaseRepo_1511_);
lean_ctor_set(v_reuseFailAlloc_1538_, 11, v_val_1497_);
lean_ctor_set(v_reuseFailAlloc_1538_, 12, v_testDriver_1513_);
lean_ctor_set(v_reuseFailAlloc_1538_, 13, v_testDriverArgs_1514_);
lean_ctor_set(v_reuseFailAlloc_1538_, 14, v_lintDriver_1515_);
lean_ctor_set(v_reuseFailAlloc_1538_, 15, v_lintDriverArgs_1516_);
lean_ctor_set(v_reuseFailAlloc_1538_, 16, v_version_1517_);
lean_ctor_set(v_reuseFailAlloc_1538_, 17, v_versionTags_1518_);
lean_ctor_set(v_reuseFailAlloc_1538_, 18, v_description_1519_);
lean_ctor_set(v_reuseFailAlloc_1538_, 19, v_keywords_1520_);
lean_ctor_set(v_reuseFailAlloc_1538_, 20, v_homepage_1521_);
lean_ctor_set(v_reuseFailAlloc_1538_, 21, v_license_1522_);
lean_ctor_set(v_reuseFailAlloc_1538_, 22, v_licenseFiles_1523_);
lean_ctor_set(v_reuseFailAlloc_1538_, 23, v_readmeFile_1524_);
lean_ctor_set(v_reuseFailAlloc_1538_, 24, v_enableArtifactCache_x3f_1526_);
lean_ctor_set(v_reuseFailAlloc_1538_, 25, v_restoreAllArtifacts_x3f_1527_);
lean_ctor_set(v_reuseFailAlloc_1538_, 26, v_builtinLint_x3f_1530_);
lean_ctor_set(v_reuseFailAlloc_1538_, 27, v_checks_1531_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*28, v_bootstrap_1501_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*28 + 1, v_precompileModules_1503_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1512_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*28 + 3, v_reservoir_1525_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1528_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*28 + 5, v_allowImportAll_1529_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*28 + 6, v_fixedToolchain_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__2(lean_object* v_f_1541_, lean_object* v_cfg_1542_){
_start:
{
lean_object* v_toWorkspaceConfig_1543_; lean_object* v_toLeanConfig_1544_; uint8_t v_bootstrap_1545_; lean_object* v_extraDepTargets_1546_; uint8_t v_precompileModules_1547_; lean_object* v_moreGlobalServerArgs_1548_; lean_object* v_srcDir_1549_; lean_object* v_buildDir_1550_; lean_object* v_leanLibDir_1551_; lean_object* v_nativeLibDir_1552_; lean_object* v_binDir_1553_; lean_object* v_irDir_1554_; lean_object* v_releaseRepo_1555_; lean_object* v_buildArchive_1556_; uint8_t v_preferReleaseBuild_1557_; lean_object* v_testDriver_1558_; lean_object* v_testDriverArgs_1559_; lean_object* v_lintDriver_1560_; lean_object* v_lintDriverArgs_1561_; lean_object* v_version_1562_; lean_object* v_versionTags_1563_; lean_object* v_description_1564_; lean_object* v_keywords_1565_; lean_object* v_homepage_1566_; lean_object* v_license_1567_; lean_object* v_licenseFiles_1568_; lean_object* v_readmeFile_1569_; uint8_t v_reservoir_1570_; lean_object* v_enableArtifactCache_x3f_1571_; lean_object* v_restoreAllArtifacts_x3f_1572_; uint8_t v_libPrefixOnWindows_1573_; uint8_t v_allowImportAll_1574_; lean_object* v_builtinLint_x3f_1575_; lean_object* v_checks_1576_; uint8_t v_fixedToolchain_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1585_; 
v_toWorkspaceConfig_1543_ = lean_ctor_get(v_cfg_1542_, 0);
v_toLeanConfig_1544_ = lean_ctor_get(v_cfg_1542_, 1);
v_bootstrap_1545_ = lean_ctor_get_uint8(v_cfg_1542_, sizeof(void*)*28);
v_extraDepTargets_1546_ = lean_ctor_get(v_cfg_1542_, 2);
v_precompileModules_1547_ = lean_ctor_get_uint8(v_cfg_1542_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1548_ = lean_ctor_get(v_cfg_1542_, 3);
v_srcDir_1549_ = lean_ctor_get(v_cfg_1542_, 4);
v_buildDir_1550_ = lean_ctor_get(v_cfg_1542_, 5);
v_leanLibDir_1551_ = lean_ctor_get(v_cfg_1542_, 6);
v_nativeLibDir_1552_ = lean_ctor_get(v_cfg_1542_, 7);
v_binDir_1553_ = lean_ctor_get(v_cfg_1542_, 8);
v_irDir_1554_ = lean_ctor_get(v_cfg_1542_, 9);
v_releaseRepo_1555_ = lean_ctor_get(v_cfg_1542_, 10);
v_buildArchive_1556_ = lean_ctor_get(v_cfg_1542_, 11);
v_preferReleaseBuild_1557_ = lean_ctor_get_uint8(v_cfg_1542_, sizeof(void*)*28 + 2);
v_testDriver_1558_ = lean_ctor_get(v_cfg_1542_, 12);
v_testDriverArgs_1559_ = lean_ctor_get(v_cfg_1542_, 13);
v_lintDriver_1560_ = lean_ctor_get(v_cfg_1542_, 14);
v_lintDriverArgs_1561_ = lean_ctor_get(v_cfg_1542_, 15);
v_version_1562_ = lean_ctor_get(v_cfg_1542_, 16);
v_versionTags_1563_ = lean_ctor_get(v_cfg_1542_, 17);
v_description_1564_ = lean_ctor_get(v_cfg_1542_, 18);
v_keywords_1565_ = lean_ctor_get(v_cfg_1542_, 19);
v_homepage_1566_ = lean_ctor_get(v_cfg_1542_, 20);
v_license_1567_ = lean_ctor_get(v_cfg_1542_, 21);
v_licenseFiles_1568_ = lean_ctor_get(v_cfg_1542_, 22);
v_readmeFile_1569_ = lean_ctor_get(v_cfg_1542_, 23);
v_reservoir_1570_ = lean_ctor_get_uint8(v_cfg_1542_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1571_ = lean_ctor_get(v_cfg_1542_, 24);
v_restoreAllArtifacts_x3f_1572_ = lean_ctor_get(v_cfg_1542_, 25);
v_libPrefixOnWindows_1573_ = lean_ctor_get_uint8(v_cfg_1542_, sizeof(void*)*28 + 4);
v_allowImportAll_1574_ = lean_ctor_get_uint8(v_cfg_1542_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1575_ = lean_ctor_get(v_cfg_1542_, 26);
v_checks_1576_ = lean_ctor_get(v_cfg_1542_, 27);
v_fixedToolchain_1577_ = lean_ctor_get_uint8(v_cfg_1542_, sizeof(void*)*28 + 6);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_cfg_1542_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1579_ = v_cfg_1542_;
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_checks_1576_);
lean_inc(v_builtinLint_x3f_1575_);
lean_inc(v_restoreAllArtifacts_x3f_1572_);
lean_inc(v_enableArtifactCache_x3f_1571_);
lean_inc(v_readmeFile_1569_);
lean_inc(v_licenseFiles_1568_);
lean_inc(v_license_1567_);
lean_inc(v_homepage_1566_);
lean_inc(v_keywords_1565_);
lean_inc(v_description_1564_);
lean_inc(v_versionTags_1563_);
lean_inc(v_version_1562_);
lean_inc(v_lintDriverArgs_1561_);
lean_inc(v_lintDriver_1560_);
lean_inc(v_testDriverArgs_1559_);
lean_inc(v_testDriver_1558_);
lean_inc(v_buildArchive_1556_);
lean_inc(v_releaseRepo_1555_);
lean_inc(v_irDir_1554_);
lean_inc(v_binDir_1553_);
lean_inc(v_nativeLibDir_1552_);
lean_inc(v_leanLibDir_1551_);
lean_inc(v_buildDir_1550_);
lean_inc(v_srcDir_1549_);
lean_inc(v_moreGlobalServerArgs_1548_);
lean_inc(v_extraDepTargets_1546_);
lean_inc(v_toLeanConfig_1544_);
lean_inc(v_toWorkspaceConfig_1543_);
lean_dec(v_cfg_1542_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = lean_apply_1(v_f_1541_, v_buildArchive_1556_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 11, v___x_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_toWorkspaceConfig_1543_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_toLeanConfig_1544_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_extraDepTargets_1546_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v_moreGlobalServerArgs_1548_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v_srcDir_1549_);
lean_ctor_set(v_reuseFailAlloc_1584_, 5, v_buildDir_1550_);
lean_ctor_set(v_reuseFailAlloc_1584_, 6, v_leanLibDir_1551_);
lean_ctor_set(v_reuseFailAlloc_1584_, 7, v_nativeLibDir_1552_);
lean_ctor_set(v_reuseFailAlloc_1584_, 8, v_binDir_1553_);
lean_ctor_set(v_reuseFailAlloc_1584_, 9, v_irDir_1554_);
lean_ctor_set(v_reuseFailAlloc_1584_, 10, v_releaseRepo_1555_);
lean_ctor_set(v_reuseFailAlloc_1584_, 11, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1584_, 12, v_testDriver_1558_);
lean_ctor_set(v_reuseFailAlloc_1584_, 13, v_testDriverArgs_1559_);
lean_ctor_set(v_reuseFailAlloc_1584_, 14, v_lintDriver_1560_);
lean_ctor_set(v_reuseFailAlloc_1584_, 15, v_lintDriverArgs_1561_);
lean_ctor_set(v_reuseFailAlloc_1584_, 16, v_version_1562_);
lean_ctor_set(v_reuseFailAlloc_1584_, 17, v_versionTags_1563_);
lean_ctor_set(v_reuseFailAlloc_1584_, 18, v_description_1564_);
lean_ctor_set(v_reuseFailAlloc_1584_, 19, v_keywords_1565_);
lean_ctor_set(v_reuseFailAlloc_1584_, 20, v_homepage_1566_);
lean_ctor_set(v_reuseFailAlloc_1584_, 21, v_license_1567_);
lean_ctor_set(v_reuseFailAlloc_1584_, 22, v_licenseFiles_1568_);
lean_ctor_set(v_reuseFailAlloc_1584_, 23, v_readmeFile_1569_);
lean_ctor_set(v_reuseFailAlloc_1584_, 24, v_enableArtifactCache_x3f_1571_);
lean_ctor_set(v_reuseFailAlloc_1584_, 25, v_restoreAllArtifacts_x3f_1572_);
lean_ctor_set(v_reuseFailAlloc_1584_, 26, v_builtinLint_x3f_1575_);
lean_ctor_set(v_reuseFailAlloc_1584_, 27, v_checks_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*28, v_bootstrap_1545_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*28 + 1, v_precompileModules_1547_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*28 + 3, v_reservoir_1570_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1573_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*28 + 5, v_allowImportAll_1574_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*28 + 6, v_fixedToolchain_1577_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg(){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = ((lean_object*)(l_Lake_PackageConfig_buildArchive___proj___redArg___closed__3));
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___boxed(lean_object* v___dummy_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lake_PackageConfig_buildArchive___proj___redArg();
return v_res_1597_;
}
}
static lean_object* _init_l_Lake_PackageConfig_buildArchive___proj___closed__0(void){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lake_PackageConfig_buildArchive___proj___redArg();
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object* v_p_1599_, lean_object* v_n_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object* v_p_1602_, lean_object* v_n_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1602_, v_n_1603_);
lean_dec(v_n_1603_);
lean_dec(v_p_1602_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___redArg(){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___redArg___boxed(lean_object* v___dummy_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lake_PackageConfig_buildArchive_instConfigField___redArg();
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object* v_p_1609_, lean_object* v_n_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object* v_p_1612_, lean_object* v_n_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lake_PackageConfig_buildArchive_instConfigField(v_p_1612_, v_n_1613_);
lean_dec(v_n_1613_);
lean_dec(v_p_1612_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg();
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object* v_p_1619_, lean_object* v_n_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object* v_p_1622_, lean_object* v_n_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField(v_p_1622_, v_n_1623_);
lean_dec(v_n_1623_);
lean_dec(v_p_1622_);
return v_res_1624_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0(lean_object* v_cfg_1625_){
_start:
{
uint8_t v_preferReleaseBuild_1626_; 
v_preferReleaseBuild_1626_ = lean_ctor_get_uint8(v_cfg_1625_, sizeof(void*)*28 + 2);
return v_preferReleaseBuild_1626_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0___boxed(lean_object* v_cfg_1627_){
_start:
{
uint8_t v_res_1628_; lean_object* v_r_1629_; 
v_res_1628_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0(v_cfg_1627_);
lean_dec_ref(v_cfg_1627_);
v_r_1629_ = lean_box(v_res_1628_);
return v_r_1629_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1(uint8_t v_val_1630_, lean_object* v_cfg_1631_){
_start:
{
lean_object* v_toWorkspaceConfig_1632_; lean_object* v_toLeanConfig_1633_; uint8_t v_bootstrap_1634_; lean_object* v_extraDepTargets_1635_; uint8_t v_precompileModules_1636_; lean_object* v_moreGlobalServerArgs_1637_; lean_object* v_srcDir_1638_; lean_object* v_buildDir_1639_; lean_object* v_leanLibDir_1640_; lean_object* v_nativeLibDir_1641_; lean_object* v_binDir_1642_; lean_object* v_irDir_1643_; lean_object* v_releaseRepo_1644_; lean_object* v_buildArchive_1645_; lean_object* v_testDriver_1646_; lean_object* v_testDriverArgs_1647_; lean_object* v_lintDriver_1648_; lean_object* v_lintDriverArgs_1649_; lean_object* v_version_1650_; lean_object* v_versionTags_1651_; lean_object* v_description_1652_; lean_object* v_keywords_1653_; lean_object* v_homepage_1654_; lean_object* v_license_1655_; lean_object* v_licenseFiles_1656_; lean_object* v_readmeFile_1657_; uint8_t v_reservoir_1658_; lean_object* v_enableArtifactCache_x3f_1659_; lean_object* v_restoreAllArtifacts_x3f_1660_; uint8_t v_libPrefixOnWindows_1661_; uint8_t v_allowImportAll_1662_; lean_object* v_builtinLint_x3f_1663_; lean_object* v_checks_1664_; uint8_t v_fixedToolchain_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_toWorkspaceConfig_1632_ = lean_ctor_get(v_cfg_1631_, 0);
v_toLeanConfig_1633_ = lean_ctor_get(v_cfg_1631_, 1);
v_bootstrap_1634_ = lean_ctor_get_uint8(v_cfg_1631_, sizeof(void*)*28);
v_extraDepTargets_1635_ = lean_ctor_get(v_cfg_1631_, 2);
v_precompileModules_1636_ = lean_ctor_get_uint8(v_cfg_1631_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1637_ = lean_ctor_get(v_cfg_1631_, 3);
v_srcDir_1638_ = lean_ctor_get(v_cfg_1631_, 4);
v_buildDir_1639_ = lean_ctor_get(v_cfg_1631_, 5);
v_leanLibDir_1640_ = lean_ctor_get(v_cfg_1631_, 6);
v_nativeLibDir_1641_ = lean_ctor_get(v_cfg_1631_, 7);
v_binDir_1642_ = lean_ctor_get(v_cfg_1631_, 8);
v_irDir_1643_ = lean_ctor_get(v_cfg_1631_, 9);
v_releaseRepo_1644_ = lean_ctor_get(v_cfg_1631_, 10);
v_buildArchive_1645_ = lean_ctor_get(v_cfg_1631_, 11);
v_testDriver_1646_ = lean_ctor_get(v_cfg_1631_, 12);
v_testDriverArgs_1647_ = lean_ctor_get(v_cfg_1631_, 13);
v_lintDriver_1648_ = lean_ctor_get(v_cfg_1631_, 14);
v_lintDriverArgs_1649_ = lean_ctor_get(v_cfg_1631_, 15);
v_version_1650_ = lean_ctor_get(v_cfg_1631_, 16);
v_versionTags_1651_ = lean_ctor_get(v_cfg_1631_, 17);
v_description_1652_ = lean_ctor_get(v_cfg_1631_, 18);
v_keywords_1653_ = lean_ctor_get(v_cfg_1631_, 19);
v_homepage_1654_ = lean_ctor_get(v_cfg_1631_, 20);
v_license_1655_ = lean_ctor_get(v_cfg_1631_, 21);
v_licenseFiles_1656_ = lean_ctor_get(v_cfg_1631_, 22);
v_readmeFile_1657_ = lean_ctor_get(v_cfg_1631_, 23);
v_reservoir_1658_ = lean_ctor_get_uint8(v_cfg_1631_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1659_ = lean_ctor_get(v_cfg_1631_, 24);
v_restoreAllArtifacts_x3f_1660_ = lean_ctor_get(v_cfg_1631_, 25);
v_libPrefixOnWindows_1661_ = lean_ctor_get_uint8(v_cfg_1631_, sizeof(void*)*28 + 4);
v_allowImportAll_1662_ = lean_ctor_get_uint8(v_cfg_1631_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1663_ = lean_ctor_get(v_cfg_1631_, 26);
v_checks_1664_ = lean_ctor_get(v_cfg_1631_, 27);
v_fixedToolchain_1665_ = lean_ctor_get_uint8(v_cfg_1631_, sizeof(void*)*28 + 6);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_cfg_1631_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v_cfg_1631_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_checks_1664_);
lean_inc(v_builtinLint_x3f_1663_);
lean_inc(v_restoreAllArtifacts_x3f_1660_);
lean_inc(v_enableArtifactCache_x3f_1659_);
lean_inc(v_readmeFile_1657_);
lean_inc(v_licenseFiles_1656_);
lean_inc(v_license_1655_);
lean_inc(v_homepage_1654_);
lean_inc(v_keywords_1653_);
lean_inc(v_description_1652_);
lean_inc(v_versionTags_1651_);
lean_inc(v_version_1650_);
lean_inc(v_lintDriverArgs_1649_);
lean_inc(v_lintDriver_1648_);
lean_inc(v_testDriverArgs_1647_);
lean_inc(v_testDriver_1646_);
lean_inc(v_buildArchive_1645_);
lean_inc(v_releaseRepo_1644_);
lean_inc(v_irDir_1643_);
lean_inc(v_binDir_1642_);
lean_inc(v_nativeLibDir_1641_);
lean_inc(v_leanLibDir_1640_);
lean_inc(v_buildDir_1639_);
lean_inc(v_srcDir_1638_);
lean_inc(v_moreGlobalServerArgs_1637_);
lean_inc(v_extraDepTargets_1635_);
lean_inc(v_toLeanConfig_1633_);
lean_inc(v_toWorkspaceConfig_1632_);
lean_dec(v_cfg_1631_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_toWorkspaceConfig_1632_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_toLeanConfig_1633_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_extraDepTargets_1635_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_moreGlobalServerArgs_1637_);
lean_ctor_set(v_reuseFailAlloc_1671_, 4, v_srcDir_1638_);
lean_ctor_set(v_reuseFailAlloc_1671_, 5, v_buildDir_1639_);
lean_ctor_set(v_reuseFailAlloc_1671_, 6, v_leanLibDir_1640_);
lean_ctor_set(v_reuseFailAlloc_1671_, 7, v_nativeLibDir_1641_);
lean_ctor_set(v_reuseFailAlloc_1671_, 8, v_binDir_1642_);
lean_ctor_set(v_reuseFailAlloc_1671_, 9, v_irDir_1643_);
lean_ctor_set(v_reuseFailAlloc_1671_, 10, v_releaseRepo_1644_);
lean_ctor_set(v_reuseFailAlloc_1671_, 11, v_buildArchive_1645_);
lean_ctor_set(v_reuseFailAlloc_1671_, 12, v_testDriver_1646_);
lean_ctor_set(v_reuseFailAlloc_1671_, 13, v_testDriverArgs_1647_);
lean_ctor_set(v_reuseFailAlloc_1671_, 14, v_lintDriver_1648_);
lean_ctor_set(v_reuseFailAlloc_1671_, 15, v_lintDriverArgs_1649_);
lean_ctor_set(v_reuseFailAlloc_1671_, 16, v_version_1650_);
lean_ctor_set(v_reuseFailAlloc_1671_, 17, v_versionTags_1651_);
lean_ctor_set(v_reuseFailAlloc_1671_, 18, v_description_1652_);
lean_ctor_set(v_reuseFailAlloc_1671_, 19, v_keywords_1653_);
lean_ctor_set(v_reuseFailAlloc_1671_, 20, v_homepage_1654_);
lean_ctor_set(v_reuseFailAlloc_1671_, 21, v_license_1655_);
lean_ctor_set(v_reuseFailAlloc_1671_, 22, v_licenseFiles_1656_);
lean_ctor_set(v_reuseFailAlloc_1671_, 23, v_readmeFile_1657_);
lean_ctor_set(v_reuseFailAlloc_1671_, 24, v_enableArtifactCache_x3f_1659_);
lean_ctor_set(v_reuseFailAlloc_1671_, 25, v_restoreAllArtifacts_x3f_1660_);
lean_ctor_set(v_reuseFailAlloc_1671_, 26, v_builtinLint_x3f_1663_);
lean_ctor_set(v_reuseFailAlloc_1671_, 27, v_checks_1664_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*28, v_bootstrap_1634_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*28 + 1, v_precompileModules_1636_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*28 + 3, v_reservoir_1658_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*28 + 5, v_allowImportAll_1662_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*28 + 6, v_fixedToolchain_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*28 + 2, v_val_1630_);
return v___x_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1___boxed(lean_object* v_val_1673_, lean_object* v_cfg_1674_){
_start:
{
uint8_t v_val_141__boxed_1675_; lean_object* v_res_1676_; 
v_val_141__boxed_1675_ = lean_unbox(v_val_1673_);
v_res_1676_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1(v_val_141__boxed_1675_, v_cfg_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__2(lean_object* v_f_1677_, lean_object* v_cfg_1678_){
_start:
{
lean_object* v_toWorkspaceConfig_1679_; lean_object* v_toLeanConfig_1680_; uint8_t v_bootstrap_1681_; lean_object* v_extraDepTargets_1682_; uint8_t v_precompileModules_1683_; lean_object* v_moreGlobalServerArgs_1684_; lean_object* v_srcDir_1685_; lean_object* v_buildDir_1686_; lean_object* v_leanLibDir_1687_; lean_object* v_nativeLibDir_1688_; lean_object* v_binDir_1689_; lean_object* v_irDir_1690_; lean_object* v_releaseRepo_1691_; lean_object* v_buildArchive_1692_; uint8_t v_preferReleaseBuild_1693_; lean_object* v_testDriver_1694_; lean_object* v_testDriverArgs_1695_; lean_object* v_lintDriver_1696_; lean_object* v_lintDriverArgs_1697_; lean_object* v_version_1698_; lean_object* v_versionTags_1699_; lean_object* v_description_1700_; lean_object* v_keywords_1701_; lean_object* v_homepage_1702_; lean_object* v_license_1703_; lean_object* v_licenseFiles_1704_; lean_object* v_readmeFile_1705_; uint8_t v_reservoir_1706_; lean_object* v_enableArtifactCache_x3f_1707_; lean_object* v_restoreAllArtifacts_x3f_1708_; uint8_t v_libPrefixOnWindows_1709_; uint8_t v_allowImportAll_1710_; lean_object* v_builtinLint_x3f_1711_; lean_object* v_checks_1712_; uint8_t v_fixedToolchain_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1723_; 
v_toWorkspaceConfig_1679_ = lean_ctor_get(v_cfg_1678_, 0);
v_toLeanConfig_1680_ = lean_ctor_get(v_cfg_1678_, 1);
v_bootstrap_1681_ = lean_ctor_get_uint8(v_cfg_1678_, sizeof(void*)*28);
v_extraDepTargets_1682_ = lean_ctor_get(v_cfg_1678_, 2);
v_precompileModules_1683_ = lean_ctor_get_uint8(v_cfg_1678_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1684_ = lean_ctor_get(v_cfg_1678_, 3);
v_srcDir_1685_ = lean_ctor_get(v_cfg_1678_, 4);
v_buildDir_1686_ = lean_ctor_get(v_cfg_1678_, 5);
v_leanLibDir_1687_ = lean_ctor_get(v_cfg_1678_, 6);
v_nativeLibDir_1688_ = lean_ctor_get(v_cfg_1678_, 7);
v_binDir_1689_ = lean_ctor_get(v_cfg_1678_, 8);
v_irDir_1690_ = lean_ctor_get(v_cfg_1678_, 9);
v_releaseRepo_1691_ = lean_ctor_get(v_cfg_1678_, 10);
v_buildArchive_1692_ = lean_ctor_get(v_cfg_1678_, 11);
v_preferReleaseBuild_1693_ = lean_ctor_get_uint8(v_cfg_1678_, sizeof(void*)*28 + 2);
v_testDriver_1694_ = lean_ctor_get(v_cfg_1678_, 12);
v_testDriverArgs_1695_ = lean_ctor_get(v_cfg_1678_, 13);
v_lintDriver_1696_ = lean_ctor_get(v_cfg_1678_, 14);
v_lintDriverArgs_1697_ = lean_ctor_get(v_cfg_1678_, 15);
v_version_1698_ = lean_ctor_get(v_cfg_1678_, 16);
v_versionTags_1699_ = lean_ctor_get(v_cfg_1678_, 17);
v_description_1700_ = lean_ctor_get(v_cfg_1678_, 18);
v_keywords_1701_ = lean_ctor_get(v_cfg_1678_, 19);
v_homepage_1702_ = lean_ctor_get(v_cfg_1678_, 20);
v_license_1703_ = lean_ctor_get(v_cfg_1678_, 21);
v_licenseFiles_1704_ = lean_ctor_get(v_cfg_1678_, 22);
v_readmeFile_1705_ = lean_ctor_get(v_cfg_1678_, 23);
v_reservoir_1706_ = lean_ctor_get_uint8(v_cfg_1678_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1707_ = lean_ctor_get(v_cfg_1678_, 24);
v_restoreAllArtifacts_x3f_1708_ = lean_ctor_get(v_cfg_1678_, 25);
v_libPrefixOnWindows_1709_ = lean_ctor_get_uint8(v_cfg_1678_, sizeof(void*)*28 + 4);
v_allowImportAll_1710_ = lean_ctor_get_uint8(v_cfg_1678_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1711_ = lean_ctor_get(v_cfg_1678_, 26);
v_checks_1712_ = lean_ctor_get(v_cfg_1678_, 27);
v_fixedToolchain_1713_ = lean_ctor_get_uint8(v_cfg_1678_, sizeof(void*)*28 + 6);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_cfg_1678_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1715_ = v_cfg_1678_;
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_checks_1712_);
lean_inc(v_builtinLint_x3f_1711_);
lean_inc(v_restoreAllArtifacts_x3f_1708_);
lean_inc(v_enableArtifactCache_x3f_1707_);
lean_inc(v_readmeFile_1705_);
lean_inc(v_licenseFiles_1704_);
lean_inc(v_license_1703_);
lean_inc(v_homepage_1702_);
lean_inc(v_keywords_1701_);
lean_inc(v_description_1700_);
lean_inc(v_versionTags_1699_);
lean_inc(v_version_1698_);
lean_inc(v_lintDriverArgs_1697_);
lean_inc(v_lintDriver_1696_);
lean_inc(v_testDriverArgs_1695_);
lean_inc(v_testDriver_1694_);
lean_inc(v_buildArchive_1692_);
lean_inc(v_releaseRepo_1691_);
lean_inc(v_irDir_1690_);
lean_inc(v_binDir_1689_);
lean_inc(v_nativeLibDir_1688_);
lean_inc(v_leanLibDir_1687_);
lean_inc(v_buildDir_1686_);
lean_inc(v_srcDir_1685_);
lean_inc(v_moreGlobalServerArgs_1684_);
lean_inc(v_extraDepTargets_1682_);
lean_inc(v_toLeanConfig_1680_);
lean_inc(v_toWorkspaceConfig_1679_);
lean_dec(v_cfg_1678_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1717_ = lean_box(v_preferReleaseBuild_1693_);
v___x_1718_ = lean_apply_1(v_f_1677_, v___x_1717_);
if (v_isShared_1716_ == 0)
{
v___x_1720_ = v___x_1715_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_toWorkspaceConfig_1679_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_toLeanConfig_1680_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_extraDepTargets_1682_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_moreGlobalServerArgs_1684_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_srcDir_1685_);
lean_ctor_set(v_reuseFailAlloc_1722_, 5, v_buildDir_1686_);
lean_ctor_set(v_reuseFailAlloc_1722_, 6, v_leanLibDir_1687_);
lean_ctor_set(v_reuseFailAlloc_1722_, 7, v_nativeLibDir_1688_);
lean_ctor_set(v_reuseFailAlloc_1722_, 8, v_binDir_1689_);
lean_ctor_set(v_reuseFailAlloc_1722_, 9, v_irDir_1690_);
lean_ctor_set(v_reuseFailAlloc_1722_, 10, v_releaseRepo_1691_);
lean_ctor_set(v_reuseFailAlloc_1722_, 11, v_buildArchive_1692_);
lean_ctor_set(v_reuseFailAlloc_1722_, 12, v_testDriver_1694_);
lean_ctor_set(v_reuseFailAlloc_1722_, 13, v_testDriverArgs_1695_);
lean_ctor_set(v_reuseFailAlloc_1722_, 14, v_lintDriver_1696_);
lean_ctor_set(v_reuseFailAlloc_1722_, 15, v_lintDriverArgs_1697_);
lean_ctor_set(v_reuseFailAlloc_1722_, 16, v_version_1698_);
lean_ctor_set(v_reuseFailAlloc_1722_, 17, v_versionTags_1699_);
lean_ctor_set(v_reuseFailAlloc_1722_, 18, v_description_1700_);
lean_ctor_set(v_reuseFailAlloc_1722_, 19, v_keywords_1701_);
lean_ctor_set(v_reuseFailAlloc_1722_, 20, v_homepage_1702_);
lean_ctor_set(v_reuseFailAlloc_1722_, 21, v_license_1703_);
lean_ctor_set(v_reuseFailAlloc_1722_, 22, v_licenseFiles_1704_);
lean_ctor_set(v_reuseFailAlloc_1722_, 23, v_readmeFile_1705_);
lean_ctor_set(v_reuseFailAlloc_1722_, 24, v_enableArtifactCache_x3f_1707_);
lean_ctor_set(v_reuseFailAlloc_1722_, 25, v_restoreAllArtifacts_x3f_1708_);
lean_ctor_set(v_reuseFailAlloc_1722_, 26, v_builtinLint_x3f_1711_);
lean_ctor_set(v_reuseFailAlloc_1722_, 27, v_checks_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*28, v_bootstrap_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*28 + 1, v_precompileModules_1683_);
v___x_1720_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
uint8_t v___x_1721_; 
v___x_1721_ = lean_unbox(v___x_1718_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*28 + 2, v___x_1721_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*28 + 3, v_reservoir_1706_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1709_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*28 + 5, v_allowImportAll_1710_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*28 + 6, v_fixedToolchain_1713_);
return v___x_1720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg(){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = ((lean_object*)(l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__3));
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___boxed(lean_object* v___dummy_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg();
return v_res_1735_;
}
}
static lean_object* _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0(void){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg();
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object* v_p_1737_, lean_object* v_n_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_obj_once(&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0, &l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_once, _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object* v_p_1740_, lean_object* v_n_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1740_, v_n_1741_);
lean_dec(v_n_1741_);
lean_dec(v_p_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg(){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_obj_once(&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0, &l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_once, _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg___boxed(lean_object* v___dummy_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg();
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object* v_p_1747_, lean_object* v_n_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_obj_once(&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0, &l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_once, _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object* v_p_1750_, lean_object* v_n_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField(v_p_1750_, v_n_1751_);
lean_dec(v_n_1751_);
lean_dec(v_p_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__0(lean_object* v_cfg_1753_){
_start:
{
lean_object* v_testDriver_1754_; 
v_testDriver_1754_ = lean_ctor_get(v_cfg_1753_, 12);
lean_inc_ref(v_testDriver_1754_);
return v_testDriver_1754_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__0___boxed(lean_object* v_cfg_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lake_PackageConfig_testDriver___proj___redArg___lam__0(v_cfg_1755_);
lean_dec_ref(v_cfg_1755_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__1(lean_object* v_val_1757_, lean_object* v_cfg_1758_){
_start:
{
lean_object* v_toWorkspaceConfig_1759_; lean_object* v_toLeanConfig_1760_; uint8_t v_bootstrap_1761_; lean_object* v_extraDepTargets_1762_; uint8_t v_precompileModules_1763_; lean_object* v_moreGlobalServerArgs_1764_; lean_object* v_srcDir_1765_; lean_object* v_buildDir_1766_; lean_object* v_leanLibDir_1767_; lean_object* v_nativeLibDir_1768_; lean_object* v_binDir_1769_; lean_object* v_irDir_1770_; lean_object* v_releaseRepo_1771_; lean_object* v_buildArchive_1772_; uint8_t v_preferReleaseBuild_1773_; lean_object* v_testDriverArgs_1774_; lean_object* v_lintDriver_1775_; lean_object* v_lintDriverArgs_1776_; lean_object* v_version_1777_; lean_object* v_versionTags_1778_; lean_object* v_description_1779_; lean_object* v_keywords_1780_; lean_object* v_homepage_1781_; lean_object* v_license_1782_; lean_object* v_licenseFiles_1783_; lean_object* v_readmeFile_1784_; uint8_t v_reservoir_1785_; lean_object* v_enableArtifactCache_x3f_1786_; lean_object* v_restoreAllArtifacts_x3f_1787_; uint8_t v_libPrefixOnWindows_1788_; uint8_t v_allowImportAll_1789_; lean_object* v_builtinLint_x3f_1790_; lean_object* v_checks_1791_; uint8_t v_fixedToolchain_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_toWorkspaceConfig_1759_ = lean_ctor_get(v_cfg_1758_, 0);
v_toLeanConfig_1760_ = lean_ctor_get(v_cfg_1758_, 1);
v_bootstrap_1761_ = lean_ctor_get_uint8(v_cfg_1758_, sizeof(void*)*28);
v_extraDepTargets_1762_ = lean_ctor_get(v_cfg_1758_, 2);
v_precompileModules_1763_ = lean_ctor_get_uint8(v_cfg_1758_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1764_ = lean_ctor_get(v_cfg_1758_, 3);
v_srcDir_1765_ = lean_ctor_get(v_cfg_1758_, 4);
v_buildDir_1766_ = lean_ctor_get(v_cfg_1758_, 5);
v_leanLibDir_1767_ = lean_ctor_get(v_cfg_1758_, 6);
v_nativeLibDir_1768_ = lean_ctor_get(v_cfg_1758_, 7);
v_binDir_1769_ = lean_ctor_get(v_cfg_1758_, 8);
v_irDir_1770_ = lean_ctor_get(v_cfg_1758_, 9);
v_releaseRepo_1771_ = lean_ctor_get(v_cfg_1758_, 10);
v_buildArchive_1772_ = lean_ctor_get(v_cfg_1758_, 11);
v_preferReleaseBuild_1773_ = lean_ctor_get_uint8(v_cfg_1758_, sizeof(void*)*28 + 2);
v_testDriverArgs_1774_ = lean_ctor_get(v_cfg_1758_, 13);
v_lintDriver_1775_ = lean_ctor_get(v_cfg_1758_, 14);
v_lintDriverArgs_1776_ = lean_ctor_get(v_cfg_1758_, 15);
v_version_1777_ = lean_ctor_get(v_cfg_1758_, 16);
v_versionTags_1778_ = lean_ctor_get(v_cfg_1758_, 17);
v_description_1779_ = lean_ctor_get(v_cfg_1758_, 18);
v_keywords_1780_ = lean_ctor_get(v_cfg_1758_, 19);
v_homepage_1781_ = lean_ctor_get(v_cfg_1758_, 20);
v_license_1782_ = lean_ctor_get(v_cfg_1758_, 21);
v_licenseFiles_1783_ = lean_ctor_get(v_cfg_1758_, 22);
v_readmeFile_1784_ = lean_ctor_get(v_cfg_1758_, 23);
v_reservoir_1785_ = lean_ctor_get_uint8(v_cfg_1758_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1786_ = lean_ctor_get(v_cfg_1758_, 24);
v_restoreAllArtifacts_x3f_1787_ = lean_ctor_get(v_cfg_1758_, 25);
v_libPrefixOnWindows_1788_ = lean_ctor_get_uint8(v_cfg_1758_, sizeof(void*)*28 + 4);
v_allowImportAll_1789_ = lean_ctor_get_uint8(v_cfg_1758_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1790_ = lean_ctor_get(v_cfg_1758_, 26);
v_checks_1791_ = lean_ctor_get(v_cfg_1758_, 27);
v_fixedToolchain_1792_ = lean_ctor_get_uint8(v_cfg_1758_, sizeof(void*)*28 + 6);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_cfg_1758_);
if (v_isSharedCheck_1799_ == 0)
{
lean_object* v_unused_1800_; 
v_unused_1800_ = lean_ctor_get(v_cfg_1758_, 12);
lean_dec(v_unused_1800_);
v___x_1794_ = v_cfg_1758_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_checks_1791_);
lean_inc(v_builtinLint_x3f_1790_);
lean_inc(v_restoreAllArtifacts_x3f_1787_);
lean_inc(v_enableArtifactCache_x3f_1786_);
lean_inc(v_readmeFile_1784_);
lean_inc(v_licenseFiles_1783_);
lean_inc(v_license_1782_);
lean_inc(v_homepage_1781_);
lean_inc(v_keywords_1780_);
lean_inc(v_description_1779_);
lean_inc(v_versionTags_1778_);
lean_inc(v_version_1777_);
lean_inc(v_lintDriverArgs_1776_);
lean_inc(v_lintDriver_1775_);
lean_inc(v_testDriverArgs_1774_);
lean_inc(v_buildArchive_1772_);
lean_inc(v_releaseRepo_1771_);
lean_inc(v_irDir_1770_);
lean_inc(v_binDir_1769_);
lean_inc(v_nativeLibDir_1768_);
lean_inc(v_leanLibDir_1767_);
lean_inc(v_buildDir_1766_);
lean_inc(v_srcDir_1765_);
lean_inc(v_moreGlobalServerArgs_1764_);
lean_inc(v_extraDepTargets_1762_);
lean_inc(v_toLeanConfig_1760_);
lean_inc(v_toWorkspaceConfig_1759_);
lean_dec(v_cfg_1758_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 12, v_val_1757_);
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_toWorkspaceConfig_1759_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_toLeanConfig_1760_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_extraDepTargets_1762_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v_moreGlobalServerArgs_1764_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v_srcDir_1765_);
lean_ctor_set(v_reuseFailAlloc_1798_, 5, v_buildDir_1766_);
lean_ctor_set(v_reuseFailAlloc_1798_, 6, v_leanLibDir_1767_);
lean_ctor_set(v_reuseFailAlloc_1798_, 7, v_nativeLibDir_1768_);
lean_ctor_set(v_reuseFailAlloc_1798_, 8, v_binDir_1769_);
lean_ctor_set(v_reuseFailAlloc_1798_, 9, v_irDir_1770_);
lean_ctor_set(v_reuseFailAlloc_1798_, 10, v_releaseRepo_1771_);
lean_ctor_set(v_reuseFailAlloc_1798_, 11, v_buildArchive_1772_);
lean_ctor_set(v_reuseFailAlloc_1798_, 12, v_val_1757_);
lean_ctor_set(v_reuseFailAlloc_1798_, 13, v_testDriverArgs_1774_);
lean_ctor_set(v_reuseFailAlloc_1798_, 14, v_lintDriver_1775_);
lean_ctor_set(v_reuseFailAlloc_1798_, 15, v_lintDriverArgs_1776_);
lean_ctor_set(v_reuseFailAlloc_1798_, 16, v_version_1777_);
lean_ctor_set(v_reuseFailAlloc_1798_, 17, v_versionTags_1778_);
lean_ctor_set(v_reuseFailAlloc_1798_, 18, v_description_1779_);
lean_ctor_set(v_reuseFailAlloc_1798_, 19, v_keywords_1780_);
lean_ctor_set(v_reuseFailAlloc_1798_, 20, v_homepage_1781_);
lean_ctor_set(v_reuseFailAlloc_1798_, 21, v_license_1782_);
lean_ctor_set(v_reuseFailAlloc_1798_, 22, v_licenseFiles_1783_);
lean_ctor_set(v_reuseFailAlloc_1798_, 23, v_readmeFile_1784_);
lean_ctor_set(v_reuseFailAlloc_1798_, 24, v_enableArtifactCache_x3f_1786_);
lean_ctor_set(v_reuseFailAlloc_1798_, 25, v_restoreAllArtifacts_x3f_1787_);
lean_ctor_set(v_reuseFailAlloc_1798_, 26, v_builtinLint_x3f_1790_);
lean_ctor_set(v_reuseFailAlloc_1798_, 27, v_checks_1791_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*28, v_bootstrap_1761_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*28 + 1, v_precompileModules_1763_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1773_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*28 + 3, v_reservoir_1785_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*28 + 5, v_allowImportAll_1789_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*28 + 6, v_fixedToolchain_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__2(lean_object* v_f_1801_, lean_object* v_cfg_1802_){
_start:
{
lean_object* v_toWorkspaceConfig_1803_; lean_object* v_toLeanConfig_1804_; uint8_t v_bootstrap_1805_; lean_object* v_extraDepTargets_1806_; uint8_t v_precompileModules_1807_; lean_object* v_moreGlobalServerArgs_1808_; lean_object* v_srcDir_1809_; lean_object* v_buildDir_1810_; lean_object* v_leanLibDir_1811_; lean_object* v_nativeLibDir_1812_; lean_object* v_binDir_1813_; lean_object* v_irDir_1814_; lean_object* v_releaseRepo_1815_; lean_object* v_buildArchive_1816_; uint8_t v_preferReleaseBuild_1817_; lean_object* v_testDriver_1818_; lean_object* v_testDriverArgs_1819_; lean_object* v_lintDriver_1820_; lean_object* v_lintDriverArgs_1821_; lean_object* v_version_1822_; lean_object* v_versionTags_1823_; lean_object* v_description_1824_; lean_object* v_keywords_1825_; lean_object* v_homepage_1826_; lean_object* v_license_1827_; lean_object* v_licenseFiles_1828_; lean_object* v_readmeFile_1829_; uint8_t v_reservoir_1830_; lean_object* v_enableArtifactCache_x3f_1831_; lean_object* v_restoreAllArtifacts_x3f_1832_; uint8_t v_libPrefixOnWindows_1833_; uint8_t v_allowImportAll_1834_; lean_object* v_builtinLint_x3f_1835_; lean_object* v_checks_1836_; uint8_t v_fixedToolchain_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1845_; 
v_toWorkspaceConfig_1803_ = lean_ctor_get(v_cfg_1802_, 0);
v_toLeanConfig_1804_ = lean_ctor_get(v_cfg_1802_, 1);
v_bootstrap_1805_ = lean_ctor_get_uint8(v_cfg_1802_, sizeof(void*)*28);
v_extraDepTargets_1806_ = lean_ctor_get(v_cfg_1802_, 2);
v_precompileModules_1807_ = lean_ctor_get_uint8(v_cfg_1802_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1808_ = lean_ctor_get(v_cfg_1802_, 3);
v_srcDir_1809_ = lean_ctor_get(v_cfg_1802_, 4);
v_buildDir_1810_ = lean_ctor_get(v_cfg_1802_, 5);
v_leanLibDir_1811_ = lean_ctor_get(v_cfg_1802_, 6);
v_nativeLibDir_1812_ = lean_ctor_get(v_cfg_1802_, 7);
v_binDir_1813_ = lean_ctor_get(v_cfg_1802_, 8);
v_irDir_1814_ = lean_ctor_get(v_cfg_1802_, 9);
v_releaseRepo_1815_ = lean_ctor_get(v_cfg_1802_, 10);
v_buildArchive_1816_ = lean_ctor_get(v_cfg_1802_, 11);
v_preferReleaseBuild_1817_ = lean_ctor_get_uint8(v_cfg_1802_, sizeof(void*)*28 + 2);
v_testDriver_1818_ = lean_ctor_get(v_cfg_1802_, 12);
v_testDriverArgs_1819_ = lean_ctor_get(v_cfg_1802_, 13);
v_lintDriver_1820_ = lean_ctor_get(v_cfg_1802_, 14);
v_lintDriverArgs_1821_ = lean_ctor_get(v_cfg_1802_, 15);
v_version_1822_ = lean_ctor_get(v_cfg_1802_, 16);
v_versionTags_1823_ = lean_ctor_get(v_cfg_1802_, 17);
v_description_1824_ = lean_ctor_get(v_cfg_1802_, 18);
v_keywords_1825_ = lean_ctor_get(v_cfg_1802_, 19);
v_homepage_1826_ = lean_ctor_get(v_cfg_1802_, 20);
v_license_1827_ = lean_ctor_get(v_cfg_1802_, 21);
v_licenseFiles_1828_ = lean_ctor_get(v_cfg_1802_, 22);
v_readmeFile_1829_ = lean_ctor_get(v_cfg_1802_, 23);
v_reservoir_1830_ = lean_ctor_get_uint8(v_cfg_1802_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1831_ = lean_ctor_get(v_cfg_1802_, 24);
v_restoreAllArtifacts_x3f_1832_ = lean_ctor_get(v_cfg_1802_, 25);
v_libPrefixOnWindows_1833_ = lean_ctor_get_uint8(v_cfg_1802_, sizeof(void*)*28 + 4);
v_allowImportAll_1834_ = lean_ctor_get_uint8(v_cfg_1802_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1835_ = lean_ctor_get(v_cfg_1802_, 26);
v_checks_1836_ = lean_ctor_get(v_cfg_1802_, 27);
v_fixedToolchain_1837_ = lean_ctor_get_uint8(v_cfg_1802_, sizeof(void*)*28 + 6);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_cfg_1802_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1839_ = v_cfg_1802_;
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_checks_1836_);
lean_inc(v_builtinLint_x3f_1835_);
lean_inc(v_restoreAllArtifacts_x3f_1832_);
lean_inc(v_enableArtifactCache_x3f_1831_);
lean_inc(v_readmeFile_1829_);
lean_inc(v_licenseFiles_1828_);
lean_inc(v_license_1827_);
lean_inc(v_homepage_1826_);
lean_inc(v_keywords_1825_);
lean_inc(v_description_1824_);
lean_inc(v_versionTags_1823_);
lean_inc(v_version_1822_);
lean_inc(v_lintDriverArgs_1821_);
lean_inc(v_lintDriver_1820_);
lean_inc(v_testDriverArgs_1819_);
lean_inc(v_testDriver_1818_);
lean_inc(v_buildArchive_1816_);
lean_inc(v_releaseRepo_1815_);
lean_inc(v_irDir_1814_);
lean_inc(v_binDir_1813_);
lean_inc(v_nativeLibDir_1812_);
lean_inc(v_leanLibDir_1811_);
lean_inc(v_buildDir_1810_);
lean_inc(v_srcDir_1809_);
lean_inc(v_moreGlobalServerArgs_1808_);
lean_inc(v_extraDepTargets_1806_);
lean_inc(v_toLeanConfig_1804_);
lean_inc(v_toWorkspaceConfig_1803_);
lean_dec(v_cfg_1802_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = lean_apply_1(v_f_1801_, v_testDriver_1818_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 12, v___x_1841_);
v___x_1843_ = v___x_1839_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_toWorkspaceConfig_1803_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_toLeanConfig_1804_);
lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_extraDepTargets_1806_);
lean_ctor_set(v_reuseFailAlloc_1844_, 3, v_moreGlobalServerArgs_1808_);
lean_ctor_set(v_reuseFailAlloc_1844_, 4, v_srcDir_1809_);
lean_ctor_set(v_reuseFailAlloc_1844_, 5, v_buildDir_1810_);
lean_ctor_set(v_reuseFailAlloc_1844_, 6, v_leanLibDir_1811_);
lean_ctor_set(v_reuseFailAlloc_1844_, 7, v_nativeLibDir_1812_);
lean_ctor_set(v_reuseFailAlloc_1844_, 8, v_binDir_1813_);
lean_ctor_set(v_reuseFailAlloc_1844_, 9, v_irDir_1814_);
lean_ctor_set(v_reuseFailAlloc_1844_, 10, v_releaseRepo_1815_);
lean_ctor_set(v_reuseFailAlloc_1844_, 11, v_buildArchive_1816_);
lean_ctor_set(v_reuseFailAlloc_1844_, 12, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1844_, 13, v_testDriverArgs_1819_);
lean_ctor_set(v_reuseFailAlloc_1844_, 14, v_lintDriver_1820_);
lean_ctor_set(v_reuseFailAlloc_1844_, 15, v_lintDriverArgs_1821_);
lean_ctor_set(v_reuseFailAlloc_1844_, 16, v_version_1822_);
lean_ctor_set(v_reuseFailAlloc_1844_, 17, v_versionTags_1823_);
lean_ctor_set(v_reuseFailAlloc_1844_, 18, v_description_1824_);
lean_ctor_set(v_reuseFailAlloc_1844_, 19, v_keywords_1825_);
lean_ctor_set(v_reuseFailAlloc_1844_, 20, v_homepage_1826_);
lean_ctor_set(v_reuseFailAlloc_1844_, 21, v_license_1827_);
lean_ctor_set(v_reuseFailAlloc_1844_, 22, v_licenseFiles_1828_);
lean_ctor_set(v_reuseFailAlloc_1844_, 23, v_readmeFile_1829_);
lean_ctor_set(v_reuseFailAlloc_1844_, 24, v_enableArtifactCache_x3f_1831_);
lean_ctor_set(v_reuseFailAlloc_1844_, 25, v_restoreAllArtifacts_x3f_1832_);
lean_ctor_set(v_reuseFailAlloc_1844_, 26, v_builtinLint_x3f_1835_);
lean_ctor_set(v_reuseFailAlloc_1844_, 27, v_checks_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*28, v_bootstrap_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*28 + 1, v_precompileModules_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*28 + 3, v_reservoir_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*28 + 5, v_allowImportAll_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*28 + 6, v_fixedToolchain_1837_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__3(lean_object* v_x_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__2));
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__3___boxed(lean_object* v_x_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lake_PackageConfig_testDriver___proj___redArg___lam__3(v_x_1848_);
lean_dec_ref(v_x_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg(){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = ((lean_object*)(l_Lake_PackageConfig_testDriver___proj___redArg___closed__4));
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___boxed(lean_object* v___dummy_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lake_PackageConfig_testDriver___proj___redArg();
return v_res_1862_;
}
}
static lean_object* _init_l_Lake_PackageConfig_testDriver___proj___closed__0(void){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lake_PackageConfig_testDriver___proj___redArg();
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object* v_p_1864_, lean_object* v_n_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object* v_p_1867_, lean_object* v_n_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lake_PackageConfig_testDriver___proj(v_p_1867_, v_n_1868_);
lean_dec(v_n_1868_);
lean_dec(v_p_1867_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___redArg(){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___redArg___boxed(lean_object* v___dummy_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lake_PackageConfig_testDriver_instConfigField___redArg();
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object* v_p_1874_, lean_object* v_n_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object* v_p_1877_, lean_object* v_n_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lake_PackageConfig_testDriver_instConfigField(v_p_1877_, v_n_1878_);
lean_dec(v_n_1878_);
lean_dec(v_p_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___redArg(){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___redArg___boxed(lean_object* v___dummy_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lake_PackageConfig_testRunner_instConfigField___redArg();
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object* v_p_1884_, lean_object* v_n_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object* v_p_1887_, lean_object* v_n_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lake_PackageConfig_testRunner_instConfigField(v_p_1887_, v_n_1888_);
lean_dec(v_n_1888_);
lean_dec(v_p_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0(lean_object* v_cfg_1890_){
_start:
{
lean_object* v_testDriverArgs_1891_; 
v_testDriverArgs_1891_ = lean_ctor_get(v_cfg_1890_, 13);
lean_inc_ref(v_testDriverArgs_1891_);
return v_testDriverArgs_1891_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0___boxed(lean_object* v_cfg_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0(v_cfg_1892_);
lean_dec_ref(v_cfg_1892_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__1(lean_object* v_val_1894_, lean_object* v_cfg_1895_){
_start:
{
lean_object* v_toWorkspaceConfig_1896_; lean_object* v_toLeanConfig_1897_; uint8_t v_bootstrap_1898_; lean_object* v_extraDepTargets_1899_; uint8_t v_precompileModules_1900_; lean_object* v_moreGlobalServerArgs_1901_; lean_object* v_srcDir_1902_; lean_object* v_buildDir_1903_; lean_object* v_leanLibDir_1904_; lean_object* v_nativeLibDir_1905_; lean_object* v_binDir_1906_; lean_object* v_irDir_1907_; lean_object* v_releaseRepo_1908_; lean_object* v_buildArchive_1909_; uint8_t v_preferReleaseBuild_1910_; lean_object* v_testDriver_1911_; lean_object* v_lintDriver_1912_; lean_object* v_lintDriverArgs_1913_; lean_object* v_version_1914_; lean_object* v_versionTags_1915_; lean_object* v_description_1916_; lean_object* v_keywords_1917_; lean_object* v_homepage_1918_; lean_object* v_license_1919_; lean_object* v_licenseFiles_1920_; lean_object* v_readmeFile_1921_; uint8_t v_reservoir_1922_; lean_object* v_enableArtifactCache_x3f_1923_; lean_object* v_restoreAllArtifacts_x3f_1924_; uint8_t v_libPrefixOnWindows_1925_; uint8_t v_allowImportAll_1926_; lean_object* v_builtinLint_x3f_1927_; lean_object* v_checks_1928_; uint8_t v_fixedToolchain_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v_toWorkspaceConfig_1896_ = lean_ctor_get(v_cfg_1895_, 0);
v_toLeanConfig_1897_ = lean_ctor_get(v_cfg_1895_, 1);
v_bootstrap_1898_ = lean_ctor_get_uint8(v_cfg_1895_, sizeof(void*)*28);
v_extraDepTargets_1899_ = lean_ctor_get(v_cfg_1895_, 2);
v_precompileModules_1900_ = lean_ctor_get_uint8(v_cfg_1895_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1901_ = lean_ctor_get(v_cfg_1895_, 3);
v_srcDir_1902_ = lean_ctor_get(v_cfg_1895_, 4);
v_buildDir_1903_ = lean_ctor_get(v_cfg_1895_, 5);
v_leanLibDir_1904_ = lean_ctor_get(v_cfg_1895_, 6);
v_nativeLibDir_1905_ = lean_ctor_get(v_cfg_1895_, 7);
v_binDir_1906_ = lean_ctor_get(v_cfg_1895_, 8);
v_irDir_1907_ = lean_ctor_get(v_cfg_1895_, 9);
v_releaseRepo_1908_ = lean_ctor_get(v_cfg_1895_, 10);
v_buildArchive_1909_ = lean_ctor_get(v_cfg_1895_, 11);
v_preferReleaseBuild_1910_ = lean_ctor_get_uint8(v_cfg_1895_, sizeof(void*)*28 + 2);
v_testDriver_1911_ = lean_ctor_get(v_cfg_1895_, 12);
v_lintDriver_1912_ = lean_ctor_get(v_cfg_1895_, 14);
v_lintDriverArgs_1913_ = lean_ctor_get(v_cfg_1895_, 15);
v_version_1914_ = lean_ctor_get(v_cfg_1895_, 16);
v_versionTags_1915_ = lean_ctor_get(v_cfg_1895_, 17);
v_description_1916_ = lean_ctor_get(v_cfg_1895_, 18);
v_keywords_1917_ = lean_ctor_get(v_cfg_1895_, 19);
v_homepage_1918_ = lean_ctor_get(v_cfg_1895_, 20);
v_license_1919_ = lean_ctor_get(v_cfg_1895_, 21);
v_licenseFiles_1920_ = lean_ctor_get(v_cfg_1895_, 22);
v_readmeFile_1921_ = lean_ctor_get(v_cfg_1895_, 23);
v_reservoir_1922_ = lean_ctor_get_uint8(v_cfg_1895_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1923_ = lean_ctor_get(v_cfg_1895_, 24);
v_restoreAllArtifacts_x3f_1924_ = lean_ctor_get(v_cfg_1895_, 25);
v_libPrefixOnWindows_1925_ = lean_ctor_get_uint8(v_cfg_1895_, sizeof(void*)*28 + 4);
v_allowImportAll_1926_ = lean_ctor_get_uint8(v_cfg_1895_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1927_ = lean_ctor_get(v_cfg_1895_, 26);
v_checks_1928_ = lean_ctor_get(v_cfg_1895_, 27);
v_fixedToolchain_1929_ = lean_ctor_get_uint8(v_cfg_1895_, sizeof(void*)*28 + 6);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_cfg_1895_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v_cfg_1895_, 13);
lean_dec(v_unused_1937_);
v___x_1931_ = v_cfg_1895_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_checks_1928_);
lean_inc(v_builtinLint_x3f_1927_);
lean_inc(v_restoreAllArtifacts_x3f_1924_);
lean_inc(v_enableArtifactCache_x3f_1923_);
lean_inc(v_readmeFile_1921_);
lean_inc(v_licenseFiles_1920_);
lean_inc(v_license_1919_);
lean_inc(v_homepage_1918_);
lean_inc(v_keywords_1917_);
lean_inc(v_description_1916_);
lean_inc(v_versionTags_1915_);
lean_inc(v_version_1914_);
lean_inc(v_lintDriverArgs_1913_);
lean_inc(v_lintDriver_1912_);
lean_inc(v_testDriver_1911_);
lean_inc(v_buildArchive_1909_);
lean_inc(v_releaseRepo_1908_);
lean_inc(v_irDir_1907_);
lean_inc(v_binDir_1906_);
lean_inc(v_nativeLibDir_1905_);
lean_inc(v_leanLibDir_1904_);
lean_inc(v_buildDir_1903_);
lean_inc(v_srcDir_1902_);
lean_inc(v_moreGlobalServerArgs_1901_);
lean_inc(v_extraDepTargets_1899_);
lean_inc(v_toLeanConfig_1897_);
lean_inc(v_toWorkspaceConfig_1896_);
lean_dec(v_cfg_1895_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 13, v_val_1894_);
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_toWorkspaceConfig_1896_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_toLeanConfig_1897_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_extraDepTargets_1899_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v_moreGlobalServerArgs_1901_);
lean_ctor_set(v_reuseFailAlloc_1935_, 4, v_srcDir_1902_);
lean_ctor_set(v_reuseFailAlloc_1935_, 5, v_buildDir_1903_);
lean_ctor_set(v_reuseFailAlloc_1935_, 6, v_leanLibDir_1904_);
lean_ctor_set(v_reuseFailAlloc_1935_, 7, v_nativeLibDir_1905_);
lean_ctor_set(v_reuseFailAlloc_1935_, 8, v_binDir_1906_);
lean_ctor_set(v_reuseFailAlloc_1935_, 9, v_irDir_1907_);
lean_ctor_set(v_reuseFailAlloc_1935_, 10, v_releaseRepo_1908_);
lean_ctor_set(v_reuseFailAlloc_1935_, 11, v_buildArchive_1909_);
lean_ctor_set(v_reuseFailAlloc_1935_, 12, v_testDriver_1911_);
lean_ctor_set(v_reuseFailAlloc_1935_, 13, v_val_1894_);
lean_ctor_set(v_reuseFailAlloc_1935_, 14, v_lintDriver_1912_);
lean_ctor_set(v_reuseFailAlloc_1935_, 15, v_lintDriverArgs_1913_);
lean_ctor_set(v_reuseFailAlloc_1935_, 16, v_version_1914_);
lean_ctor_set(v_reuseFailAlloc_1935_, 17, v_versionTags_1915_);
lean_ctor_set(v_reuseFailAlloc_1935_, 18, v_description_1916_);
lean_ctor_set(v_reuseFailAlloc_1935_, 19, v_keywords_1917_);
lean_ctor_set(v_reuseFailAlloc_1935_, 20, v_homepage_1918_);
lean_ctor_set(v_reuseFailAlloc_1935_, 21, v_license_1919_);
lean_ctor_set(v_reuseFailAlloc_1935_, 22, v_licenseFiles_1920_);
lean_ctor_set(v_reuseFailAlloc_1935_, 23, v_readmeFile_1921_);
lean_ctor_set(v_reuseFailAlloc_1935_, 24, v_enableArtifactCache_x3f_1923_);
lean_ctor_set(v_reuseFailAlloc_1935_, 25, v_restoreAllArtifacts_x3f_1924_);
lean_ctor_set(v_reuseFailAlloc_1935_, 26, v_builtinLint_x3f_1927_);
lean_ctor_set(v_reuseFailAlloc_1935_, 27, v_checks_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*28, v_bootstrap_1898_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*28 + 1, v_precompileModules_1900_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1910_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*28 + 3, v_reservoir_1922_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1925_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*28 + 5, v_allowImportAll_1926_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*28 + 6, v_fixedToolchain_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__2(lean_object* v_f_1938_, lean_object* v_cfg_1939_){
_start:
{
lean_object* v_toWorkspaceConfig_1940_; lean_object* v_toLeanConfig_1941_; uint8_t v_bootstrap_1942_; lean_object* v_extraDepTargets_1943_; uint8_t v_precompileModules_1944_; lean_object* v_moreGlobalServerArgs_1945_; lean_object* v_srcDir_1946_; lean_object* v_buildDir_1947_; lean_object* v_leanLibDir_1948_; lean_object* v_nativeLibDir_1949_; lean_object* v_binDir_1950_; lean_object* v_irDir_1951_; lean_object* v_releaseRepo_1952_; lean_object* v_buildArchive_1953_; uint8_t v_preferReleaseBuild_1954_; lean_object* v_testDriver_1955_; lean_object* v_testDriverArgs_1956_; lean_object* v_lintDriver_1957_; lean_object* v_lintDriverArgs_1958_; lean_object* v_version_1959_; lean_object* v_versionTags_1960_; lean_object* v_description_1961_; lean_object* v_keywords_1962_; lean_object* v_homepage_1963_; lean_object* v_license_1964_; lean_object* v_licenseFiles_1965_; lean_object* v_readmeFile_1966_; uint8_t v_reservoir_1967_; lean_object* v_enableArtifactCache_x3f_1968_; lean_object* v_restoreAllArtifacts_x3f_1969_; uint8_t v_libPrefixOnWindows_1970_; uint8_t v_allowImportAll_1971_; lean_object* v_builtinLint_x3f_1972_; lean_object* v_checks_1973_; uint8_t v_fixedToolchain_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1982_; 
v_toWorkspaceConfig_1940_ = lean_ctor_get(v_cfg_1939_, 0);
v_toLeanConfig_1941_ = lean_ctor_get(v_cfg_1939_, 1);
v_bootstrap_1942_ = lean_ctor_get_uint8(v_cfg_1939_, sizeof(void*)*28);
v_extraDepTargets_1943_ = lean_ctor_get(v_cfg_1939_, 2);
v_precompileModules_1944_ = lean_ctor_get_uint8(v_cfg_1939_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1945_ = lean_ctor_get(v_cfg_1939_, 3);
v_srcDir_1946_ = lean_ctor_get(v_cfg_1939_, 4);
v_buildDir_1947_ = lean_ctor_get(v_cfg_1939_, 5);
v_leanLibDir_1948_ = lean_ctor_get(v_cfg_1939_, 6);
v_nativeLibDir_1949_ = lean_ctor_get(v_cfg_1939_, 7);
v_binDir_1950_ = lean_ctor_get(v_cfg_1939_, 8);
v_irDir_1951_ = lean_ctor_get(v_cfg_1939_, 9);
v_releaseRepo_1952_ = lean_ctor_get(v_cfg_1939_, 10);
v_buildArchive_1953_ = lean_ctor_get(v_cfg_1939_, 11);
v_preferReleaseBuild_1954_ = lean_ctor_get_uint8(v_cfg_1939_, sizeof(void*)*28 + 2);
v_testDriver_1955_ = lean_ctor_get(v_cfg_1939_, 12);
v_testDriverArgs_1956_ = lean_ctor_get(v_cfg_1939_, 13);
v_lintDriver_1957_ = lean_ctor_get(v_cfg_1939_, 14);
v_lintDriverArgs_1958_ = lean_ctor_get(v_cfg_1939_, 15);
v_version_1959_ = lean_ctor_get(v_cfg_1939_, 16);
v_versionTags_1960_ = lean_ctor_get(v_cfg_1939_, 17);
v_description_1961_ = lean_ctor_get(v_cfg_1939_, 18);
v_keywords_1962_ = lean_ctor_get(v_cfg_1939_, 19);
v_homepage_1963_ = lean_ctor_get(v_cfg_1939_, 20);
v_license_1964_ = lean_ctor_get(v_cfg_1939_, 21);
v_licenseFiles_1965_ = lean_ctor_get(v_cfg_1939_, 22);
v_readmeFile_1966_ = lean_ctor_get(v_cfg_1939_, 23);
v_reservoir_1967_ = lean_ctor_get_uint8(v_cfg_1939_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1968_ = lean_ctor_get(v_cfg_1939_, 24);
v_restoreAllArtifacts_x3f_1969_ = lean_ctor_get(v_cfg_1939_, 25);
v_libPrefixOnWindows_1970_ = lean_ctor_get_uint8(v_cfg_1939_, sizeof(void*)*28 + 4);
v_allowImportAll_1971_ = lean_ctor_get_uint8(v_cfg_1939_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1972_ = lean_ctor_get(v_cfg_1939_, 26);
v_checks_1973_ = lean_ctor_get(v_cfg_1939_, 27);
v_fixedToolchain_1974_ = lean_ctor_get_uint8(v_cfg_1939_, sizeof(void*)*28 + 6);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_cfg_1939_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1976_ = v_cfg_1939_;
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_checks_1973_);
lean_inc(v_builtinLint_x3f_1972_);
lean_inc(v_restoreAllArtifacts_x3f_1969_);
lean_inc(v_enableArtifactCache_x3f_1968_);
lean_inc(v_readmeFile_1966_);
lean_inc(v_licenseFiles_1965_);
lean_inc(v_license_1964_);
lean_inc(v_homepage_1963_);
lean_inc(v_keywords_1962_);
lean_inc(v_description_1961_);
lean_inc(v_versionTags_1960_);
lean_inc(v_version_1959_);
lean_inc(v_lintDriverArgs_1958_);
lean_inc(v_lintDriver_1957_);
lean_inc(v_testDriverArgs_1956_);
lean_inc(v_testDriver_1955_);
lean_inc(v_buildArchive_1953_);
lean_inc(v_releaseRepo_1952_);
lean_inc(v_irDir_1951_);
lean_inc(v_binDir_1950_);
lean_inc(v_nativeLibDir_1949_);
lean_inc(v_leanLibDir_1948_);
lean_inc(v_buildDir_1947_);
lean_inc(v_srcDir_1946_);
lean_inc(v_moreGlobalServerArgs_1945_);
lean_inc(v_extraDepTargets_1943_);
lean_inc(v_toLeanConfig_1941_);
lean_inc(v_toWorkspaceConfig_1940_);
lean_dec(v_cfg_1939_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1978_ = lean_apply_1(v_f_1938_, v_testDriverArgs_1956_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 13, v___x_1978_);
v___x_1980_ = v___x_1976_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_toWorkspaceConfig_1940_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_toLeanConfig_1941_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_extraDepTargets_1943_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_moreGlobalServerArgs_1945_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v_srcDir_1946_);
lean_ctor_set(v_reuseFailAlloc_1981_, 5, v_buildDir_1947_);
lean_ctor_set(v_reuseFailAlloc_1981_, 6, v_leanLibDir_1948_);
lean_ctor_set(v_reuseFailAlloc_1981_, 7, v_nativeLibDir_1949_);
lean_ctor_set(v_reuseFailAlloc_1981_, 8, v_binDir_1950_);
lean_ctor_set(v_reuseFailAlloc_1981_, 9, v_irDir_1951_);
lean_ctor_set(v_reuseFailAlloc_1981_, 10, v_releaseRepo_1952_);
lean_ctor_set(v_reuseFailAlloc_1981_, 11, v_buildArchive_1953_);
lean_ctor_set(v_reuseFailAlloc_1981_, 12, v_testDriver_1955_);
lean_ctor_set(v_reuseFailAlloc_1981_, 13, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1981_, 14, v_lintDriver_1957_);
lean_ctor_set(v_reuseFailAlloc_1981_, 15, v_lintDriverArgs_1958_);
lean_ctor_set(v_reuseFailAlloc_1981_, 16, v_version_1959_);
lean_ctor_set(v_reuseFailAlloc_1981_, 17, v_versionTags_1960_);
lean_ctor_set(v_reuseFailAlloc_1981_, 18, v_description_1961_);
lean_ctor_set(v_reuseFailAlloc_1981_, 19, v_keywords_1962_);
lean_ctor_set(v_reuseFailAlloc_1981_, 20, v_homepage_1963_);
lean_ctor_set(v_reuseFailAlloc_1981_, 21, v_license_1964_);
lean_ctor_set(v_reuseFailAlloc_1981_, 22, v_licenseFiles_1965_);
lean_ctor_set(v_reuseFailAlloc_1981_, 23, v_readmeFile_1966_);
lean_ctor_set(v_reuseFailAlloc_1981_, 24, v_enableArtifactCache_x3f_1968_);
lean_ctor_set(v_reuseFailAlloc_1981_, 25, v_restoreAllArtifacts_x3f_1969_);
lean_ctor_set(v_reuseFailAlloc_1981_, 26, v_builtinLint_x3f_1972_);
lean_ctor_set(v_reuseFailAlloc_1981_, 27, v_checks_1973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*28, v_bootstrap_1942_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*28 + 1, v_precompileModules_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*28 + 3, v_reservoir_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*28 + 5, v_allowImportAll_1971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*28 + 6, v_fixedToolchain_1974_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg(){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = ((lean_object*)(l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__3));
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___boxed(lean_object* v___dummy_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lake_PackageConfig_testDriverArgs___proj___redArg();
return v_res_1994_;
}
}
static lean_object* _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0(void){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lake_PackageConfig_testDriverArgs___proj___redArg();
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object* v_p_1996_, lean_object* v_n_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_obj_once(&l_Lake_PackageConfig_testDriverArgs___proj___closed__0, &l_Lake_PackageConfig_testDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object* v_p_1999_, lean_object* v_n_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1999_, v_n_2000_);
lean_dec(v_n_2000_);
lean_dec(v_p_1999_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_obj_once(&l_Lake_PackageConfig_testDriverArgs___proj___closed__0, &l_Lake_PackageConfig_testDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg___boxed(lean_object* v___dummy_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg();
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object* v_p_2006_, lean_object* v_n_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_obj_once(&l_Lake_PackageConfig_testDriverArgs___proj___closed__0, &l_Lake_PackageConfig_testDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object* v_p_2009_, lean_object* v_n_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lake_PackageConfig_testDriverArgs_instConfigField(v_p_2009_, v_n_2010_);
lean_dec(v_n_2010_);
lean_dec(v_p_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0(lean_object* v_cfg_2012_){
_start:
{
lean_object* v_lintDriver_2013_; 
v_lintDriver_2013_ = lean_ctor_get(v_cfg_2012_, 14);
lean_inc_ref(v_lintDriver_2013_);
return v_lintDriver_2013_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0___boxed(lean_object* v_cfg_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0(v_cfg_2014_);
lean_dec_ref(v_cfg_2014_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__1(lean_object* v_val_2016_, lean_object* v_cfg_2017_){
_start:
{
lean_object* v_toWorkspaceConfig_2018_; lean_object* v_toLeanConfig_2019_; uint8_t v_bootstrap_2020_; lean_object* v_extraDepTargets_2021_; uint8_t v_precompileModules_2022_; lean_object* v_moreGlobalServerArgs_2023_; lean_object* v_srcDir_2024_; lean_object* v_buildDir_2025_; lean_object* v_leanLibDir_2026_; lean_object* v_nativeLibDir_2027_; lean_object* v_binDir_2028_; lean_object* v_irDir_2029_; lean_object* v_releaseRepo_2030_; lean_object* v_buildArchive_2031_; uint8_t v_preferReleaseBuild_2032_; lean_object* v_testDriver_2033_; lean_object* v_testDriverArgs_2034_; lean_object* v_lintDriverArgs_2035_; lean_object* v_version_2036_; lean_object* v_versionTags_2037_; lean_object* v_description_2038_; lean_object* v_keywords_2039_; lean_object* v_homepage_2040_; lean_object* v_license_2041_; lean_object* v_licenseFiles_2042_; lean_object* v_readmeFile_2043_; uint8_t v_reservoir_2044_; lean_object* v_enableArtifactCache_x3f_2045_; lean_object* v_restoreAllArtifacts_x3f_2046_; uint8_t v_libPrefixOnWindows_2047_; uint8_t v_allowImportAll_2048_; lean_object* v_builtinLint_x3f_2049_; lean_object* v_checks_2050_; uint8_t v_fixedToolchain_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_toWorkspaceConfig_2018_ = lean_ctor_get(v_cfg_2017_, 0);
v_toLeanConfig_2019_ = lean_ctor_get(v_cfg_2017_, 1);
v_bootstrap_2020_ = lean_ctor_get_uint8(v_cfg_2017_, sizeof(void*)*28);
v_extraDepTargets_2021_ = lean_ctor_get(v_cfg_2017_, 2);
v_precompileModules_2022_ = lean_ctor_get_uint8(v_cfg_2017_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2023_ = lean_ctor_get(v_cfg_2017_, 3);
v_srcDir_2024_ = lean_ctor_get(v_cfg_2017_, 4);
v_buildDir_2025_ = lean_ctor_get(v_cfg_2017_, 5);
v_leanLibDir_2026_ = lean_ctor_get(v_cfg_2017_, 6);
v_nativeLibDir_2027_ = lean_ctor_get(v_cfg_2017_, 7);
v_binDir_2028_ = lean_ctor_get(v_cfg_2017_, 8);
v_irDir_2029_ = lean_ctor_get(v_cfg_2017_, 9);
v_releaseRepo_2030_ = lean_ctor_get(v_cfg_2017_, 10);
v_buildArchive_2031_ = lean_ctor_get(v_cfg_2017_, 11);
v_preferReleaseBuild_2032_ = lean_ctor_get_uint8(v_cfg_2017_, sizeof(void*)*28 + 2);
v_testDriver_2033_ = lean_ctor_get(v_cfg_2017_, 12);
v_testDriverArgs_2034_ = lean_ctor_get(v_cfg_2017_, 13);
v_lintDriverArgs_2035_ = lean_ctor_get(v_cfg_2017_, 15);
v_version_2036_ = lean_ctor_get(v_cfg_2017_, 16);
v_versionTags_2037_ = lean_ctor_get(v_cfg_2017_, 17);
v_description_2038_ = lean_ctor_get(v_cfg_2017_, 18);
v_keywords_2039_ = lean_ctor_get(v_cfg_2017_, 19);
v_homepage_2040_ = lean_ctor_get(v_cfg_2017_, 20);
v_license_2041_ = lean_ctor_get(v_cfg_2017_, 21);
v_licenseFiles_2042_ = lean_ctor_get(v_cfg_2017_, 22);
v_readmeFile_2043_ = lean_ctor_get(v_cfg_2017_, 23);
v_reservoir_2044_ = lean_ctor_get_uint8(v_cfg_2017_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2045_ = lean_ctor_get(v_cfg_2017_, 24);
v_restoreAllArtifacts_x3f_2046_ = lean_ctor_get(v_cfg_2017_, 25);
v_libPrefixOnWindows_2047_ = lean_ctor_get_uint8(v_cfg_2017_, sizeof(void*)*28 + 4);
v_allowImportAll_2048_ = lean_ctor_get_uint8(v_cfg_2017_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2049_ = lean_ctor_get(v_cfg_2017_, 26);
v_checks_2050_ = lean_ctor_get(v_cfg_2017_, 27);
v_fixedToolchain_2051_ = lean_ctor_get_uint8(v_cfg_2017_, sizeof(void*)*28 + 6);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_cfg_2017_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v_cfg_2017_, 14);
lean_dec(v_unused_2059_);
v___x_2053_ = v_cfg_2017_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_checks_2050_);
lean_inc(v_builtinLint_x3f_2049_);
lean_inc(v_restoreAllArtifacts_x3f_2046_);
lean_inc(v_enableArtifactCache_x3f_2045_);
lean_inc(v_readmeFile_2043_);
lean_inc(v_licenseFiles_2042_);
lean_inc(v_license_2041_);
lean_inc(v_homepage_2040_);
lean_inc(v_keywords_2039_);
lean_inc(v_description_2038_);
lean_inc(v_versionTags_2037_);
lean_inc(v_version_2036_);
lean_inc(v_lintDriverArgs_2035_);
lean_inc(v_testDriverArgs_2034_);
lean_inc(v_testDriver_2033_);
lean_inc(v_buildArchive_2031_);
lean_inc(v_releaseRepo_2030_);
lean_inc(v_irDir_2029_);
lean_inc(v_binDir_2028_);
lean_inc(v_nativeLibDir_2027_);
lean_inc(v_leanLibDir_2026_);
lean_inc(v_buildDir_2025_);
lean_inc(v_srcDir_2024_);
lean_inc(v_moreGlobalServerArgs_2023_);
lean_inc(v_extraDepTargets_2021_);
lean_inc(v_toLeanConfig_2019_);
lean_inc(v_toWorkspaceConfig_2018_);
lean_dec(v_cfg_2017_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 14, v_val_2016_);
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_toWorkspaceConfig_2018_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_toLeanConfig_2019_);
lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_extraDepTargets_2021_);
lean_ctor_set(v_reuseFailAlloc_2057_, 3, v_moreGlobalServerArgs_2023_);
lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_srcDir_2024_);
lean_ctor_set(v_reuseFailAlloc_2057_, 5, v_buildDir_2025_);
lean_ctor_set(v_reuseFailAlloc_2057_, 6, v_leanLibDir_2026_);
lean_ctor_set(v_reuseFailAlloc_2057_, 7, v_nativeLibDir_2027_);
lean_ctor_set(v_reuseFailAlloc_2057_, 8, v_binDir_2028_);
lean_ctor_set(v_reuseFailAlloc_2057_, 9, v_irDir_2029_);
lean_ctor_set(v_reuseFailAlloc_2057_, 10, v_releaseRepo_2030_);
lean_ctor_set(v_reuseFailAlloc_2057_, 11, v_buildArchive_2031_);
lean_ctor_set(v_reuseFailAlloc_2057_, 12, v_testDriver_2033_);
lean_ctor_set(v_reuseFailAlloc_2057_, 13, v_testDriverArgs_2034_);
lean_ctor_set(v_reuseFailAlloc_2057_, 14, v_val_2016_);
lean_ctor_set(v_reuseFailAlloc_2057_, 15, v_lintDriverArgs_2035_);
lean_ctor_set(v_reuseFailAlloc_2057_, 16, v_version_2036_);
lean_ctor_set(v_reuseFailAlloc_2057_, 17, v_versionTags_2037_);
lean_ctor_set(v_reuseFailAlloc_2057_, 18, v_description_2038_);
lean_ctor_set(v_reuseFailAlloc_2057_, 19, v_keywords_2039_);
lean_ctor_set(v_reuseFailAlloc_2057_, 20, v_homepage_2040_);
lean_ctor_set(v_reuseFailAlloc_2057_, 21, v_license_2041_);
lean_ctor_set(v_reuseFailAlloc_2057_, 22, v_licenseFiles_2042_);
lean_ctor_set(v_reuseFailAlloc_2057_, 23, v_readmeFile_2043_);
lean_ctor_set(v_reuseFailAlloc_2057_, 24, v_enableArtifactCache_x3f_2045_);
lean_ctor_set(v_reuseFailAlloc_2057_, 25, v_restoreAllArtifacts_x3f_2046_);
lean_ctor_set(v_reuseFailAlloc_2057_, 26, v_builtinLint_x3f_2049_);
lean_ctor_set(v_reuseFailAlloc_2057_, 27, v_checks_2050_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*28, v_bootstrap_2020_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*28 + 1, v_precompileModules_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2032_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*28 + 3, v_reservoir_2044_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*28 + 5, v_allowImportAll_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*28 + 6, v_fixedToolchain_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__2(lean_object* v_f_2060_, lean_object* v_cfg_2061_){
_start:
{
lean_object* v_toWorkspaceConfig_2062_; lean_object* v_toLeanConfig_2063_; uint8_t v_bootstrap_2064_; lean_object* v_extraDepTargets_2065_; uint8_t v_precompileModules_2066_; lean_object* v_moreGlobalServerArgs_2067_; lean_object* v_srcDir_2068_; lean_object* v_buildDir_2069_; lean_object* v_leanLibDir_2070_; lean_object* v_nativeLibDir_2071_; lean_object* v_binDir_2072_; lean_object* v_irDir_2073_; lean_object* v_releaseRepo_2074_; lean_object* v_buildArchive_2075_; uint8_t v_preferReleaseBuild_2076_; lean_object* v_testDriver_2077_; lean_object* v_testDriverArgs_2078_; lean_object* v_lintDriver_2079_; lean_object* v_lintDriverArgs_2080_; lean_object* v_version_2081_; lean_object* v_versionTags_2082_; lean_object* v_description_2083_; lean_object* v_keywords_2084_; lean_object* v_homepage_2085_; lean_object* v_license_2086_; lean_object* v_licenseFiles_2087_; lean_object* v_readmeFile_2088_; uint8_t v_reservoir_2089_; lean_object* v_enableArtifactCache_x3f_2090_; lean_object* v_restoreAllArtifacts_x3f_2091_; uint8_t v_libPrefixOnWindows_2092_; uint8_t v_allowImportAll_2093_; lean_object* v_builtinLint_x3f_2094_; lean_object* v_checks_2095_; uint8_t v_fixedToolchain_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2104_; 
v_toWorkspaceConfig_2062_ = lean_ctor_get(v_cfg_2061_, 0);
v_toLeanConfig_2063_ = lean_ctor_get(v_cfg_2061_, 1);
v_bootstrap_2064_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*28);
v_extraDepTargets_2065_ = lean_ctor_get(v_cfg_2061_, 2);
v_precompileModules_2066_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2067_ = lean_ctor_get(v_cfg_2061_, 3);
v_srcDir_2068_ = lean_ctor_get(v_cfg_2061_, 4);
v_buildDir_2069_ = lean_ctor_get(v_cfg_2061_, 5);
v_leanLibDir_2070_ = lean_ctor_get(v_cfg_2061_, 6);
v_nativeLibDir_2071_ = lean_ctor_get(v_cfg_2061_, 7);
v_binDir_2072_ = lean_ctor_get(v_cfg_2061_, 8);
v_irDir_2073_ = lean_ctor_get(v_cfg_2061_, 9);
v_releaseRepo_2074_ = lean_ctor_get(v_cfg_2061_, 10);
v_buildArchive_2075_ = lean_ctor_get(v_cfg_2061_, 11);
v_preferReleaseBuild_2076_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*28 + 2);
v_testDriver_2077_ = lean_ctor_get(v_cfg_2061_, 12);
v_testDriverArgs_2078_ = lean_ctor_get(v_cfg_2061_, 13);
v_lintDriver_2079_ = lean_ctor_get(v_cfg_2061_, 14);
v_lintDriverArgs_2080_ = lean_ctor_get(v_cfg_2061_, 15);
v_version_2081_ = lean_ctor_get(v_cfg_2061_, 16);
v_versionTags_2082_ = lean_ctor_get(v_cfg_2061_, 17);
v_description_2083_ = lean_ctor_get(v_cfg_2061_, 18);
v_keywords_2084_ = lean_ctor_get(v_cfg_2061_, 19);
v_homepage_2085_ = lean_ctor_get(v_cfg_2061_, 20);
v_license_2086_ = lean_ctor_get(v_cfg_2061_, 21);
v_licenseFiles_2087_ = lean_ctor_get(v_cfg_2061_, 22);
v_readmeFile_2088_ = lean_ctor_get(v_cfg_2061_, 23);
v_reservoir_2089_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2090_ = lean_ctor_get(v_cfg_2061_, 24);
v_restoreAllArtifacts_x3f_2091_ = lean_ctor_get(v_cfg_2061_, 25);
v_libPrefixOnWindows_2092_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*28 + 4);
v_allowImportAll_2093_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2094_ = lean_ctor_get(v_cfg_2061_, 26);
v_checks_2095_ = lean_ctor_get(v_cfg_2061_, 27);
v_fixedToolchain_2096_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*28 + 6);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_cfg_2061_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2098_ = v_cfg_2061_;
v_isShared_2099_ = v_isSharedCheck_2104_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_checks_2095_);
lean_inc(v_builtinLint_x3f_2094_);
lean_inc(v_restoreAllArtifacts_x3f_2091_);
lean_inc(v_enableArtifactCache_x3f_2090_);
lean_inc(v_readmeFile_2088_);
lean_inc(v_licenseFiles_2087_);
lean_inc(v_license_2086_);
lean_inc(v_homepage_2085_);
lean_inc(v_keywords_2084_);
lean_inc(v_description_2083_);
lean_inc(v_versionTags_2082_);
lean_inc(v_version_2081_);
lean_inc(v_lintDriverArgs_2080_);
lean_inc(v_lintDriver_2079_);
lean_inc(v_testDriverArgs_2078_);
lean_inc(v_testDriver_2077_);
lean_inc(v_buildArchive_2075_);
lean_inc(v_releaseRepo_2074_);
lean_inc(v_irDir_2073_);
lean_inc(v_binDir_2072_);
lean_inc(v_nativeLibDir_2071_);
lean_inc(v_leanLibDir_2070_);
lean_inc(v_buildDir_2069_);
lean_inc(v_srcDir_2068_);
lean_inc(v_moreGlobalServerArgs_2067_);
lean_inc(v_extraDepTargets_2065_);
lean_inc(v_toLeanConfig_2063_);
lean_inc(v_toWorkspaceConfig_2062_);
lean_dec(v_cfg_2061_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2104_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2100_ = lean_apply_1(v_f_2060_, v_lintDriver_2079_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 14, v___x_2100_);
v___x_2102_ = v___x_2098_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_toWorkspaceConfig_2062_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_toLeanConfig_2063_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_extraDepTargets_2065_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_moreGlobalServerArgs_2067_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_srcDir_2068_);
lean_ctor_set(v_reuseFailAlloc_2103_, 5, v_buildDir_2069_);
lean_ctor_set(v_reuseFailAlloc_2103_, 6, v_leanLibDir_2070_);
lean_ctor_set(v_reuseFailAlloc_2103_, 7, v_nativeLibDir_2071_);
lean_ctor_set(v_reuseFailAlloc_2103_, 8, v_binDir_2072_);
lean_ctor_set(v_reuseFailAlloc_2103_, 9, v_irDir_2073_);
lean_ctor_set(v_reuseFailAlloc_2103_, 10, v_releaseRepo_2074_);
lean_ctor_set(v_reuseFailAlloc_2103_, 11, v_buildArchive_2075_);
lean_ctor_set(v_reuseFailAlloc_2103_, 12, v_testDriver_2077_);
lean_ctor_set(v_reuseFailAlloc_2103_, 13, v_testDriverArgs_2078_);
lean_ctor_set(v_reuseFailAlloc_2103_, 14, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2103_, 15, v_lintDriverArgs_2080_);
lean_ctor_set(v_reuseFailAlloc_2103_, 16, v_version_2081_);
lean_ctor_set(v_reuseFailAlloc_2103_, 17, v_versionTags_2082_);
lean_ctor_set(v_reuseFailAlloc_2103_, 18, v_description_2083_);
lean_ctor_set(v_reuseFailAlloc_2103_, 19, v_keywords_2084_);
lean_ctor_set(v_reuseFailAlloc_2103_, 20, v_homepage_2085_);
lean_ctor_set(v_reuseFailAlloc_2103_, 21, v_license_2086_);
lean_ctor_set(v_reuseFailAlloc_2103_, 22, v_licenseFiles_2087_);
lean_ctor_set(v_reuseFailAlloc_2103_, 23, v_readmeFile_2088_);
lean_ctor_set(v_reuseFailAlloc_2103_, 24, v_enableArtifactCache_x3f_2090_);
lean_ctor_set(v_reuseFailAlloc_2103_, 25, v_restoreAllArtifacts_x3f_2091_);
lean_ctor_set(v_reuseFailAlloc_2103_, 26, v_builtinLint_x3f_2094_);
lean_ctor_set(v_reuseFailAlloc_2103_, 27, v_checks_2095_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*28, v_bootstrap_2064_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*28 + 1, v_precompileModules_2066_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*28 + 3, v_reservoir_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*28 + 5, v_allowImportAll_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*28 + 6, v_fixedToolchain_2096_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg(){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = ((lean_object*)(l_Lake_PackageConfig_lintDriver___proj___redArg___closed__3));
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___boxed(lean_object* v___dummy_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lake_PackageConfig_lintDriver___proj___redArg();
return v_res_2116_;
}
}
static lean_object* _init_l_Lake_PackageConfig_lintDriver___proj___closed__0(void){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lake_PackageConfig_lintDriver___proj___redArg();
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object* v_p_2118_, lean_object* v_n_2119_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_obj_once(&l_Lake_PackageConfig_lintDriver___proj___closed__0, &l_Lake_PackageConfig_lintDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriver___proj___closed__0);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object* v_p_2121_, lean_object* v_n_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lake_PackageConfig_lintDriver___proj(v_p_2121_, v_n_2122_);
lean_dec(v_n_2122_);
lean_dec(v_p_2121_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___redArg(){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_obj_once(&l_Lake_PackageConfig_lintDriver___proj___closed__0, &l_Lake_PackageConfig_lintDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriver___proj___closed__0);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___redArg___boxed(lean_object* v___dummy_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lake_PackageConfig_lintDriver_instConfigField___redArg();
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object* v_p_2128_, lean_object* v_n_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_obj_once(&l_Lake_PackageConfig_lintDriver___proj___closed__0, &l_Lake_PackageConfig_lintDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriver___proj___closed__0);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object* v_p_2131_, lean_object* v_n_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lake_PackageConfig_lintDriver_instConfigField(v_p_2131_, v_n_2132_);
lean_dec(v_n_2132_);
lean_dec(v_p_2131_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0(lean_object* v_cfg_2134_){
_start:
{
lean_object* v_lintDriverArgs_2135_; 
v_lintDriverArgs_2135_ = lean_ctor_get(v_cfg_2134_, 15);
lean_inc_ref(v_lintDriverArgs_2135_);
return v_lintDriverArgs_2135_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0___boxed(lean_object* v_cfg_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0(v_cfg_2136_);
lean_dec_ref(v_cfg_2136_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__1(lean_object* v_val_2138_, lean_object* v_cfg_2139_){
_start:
{
lean_object* v_toWorkspaceConfig_2140_; lean_object* v_toLeanConfig_2141_; uint8_t v_bootstrap_2142_; lean_object* v_extraDepTargets_2143_; uint8_t v_precompileModules_2144_; lean_object* v_moreGlobalServerArgs_2145_; lean_object* v_srcDir_2146_; lean_object* v_buildDir_2147_; lean_object* v_leanLibDir_2148_; lean_object* v_nativeLibDir_2149_; lean_object* v_binDir_2150_; lean_object* v_irDir_2151_; lean_object* v_releaseRepo_2152_; lean_object* v_buildArchive_2153_; uint8_t v_preferReleaseBuild_2154_; lean_object* v_testDriver_2155_; lean_object* v_testDriverArgs_2156_; lean_object* v_lintDriver_2157_; lean_object* v_version_2158_; lean_object* v_versionTags_2159_; lean_object* v_description_2160_; lean_object* v_keywords_2161_; lean_object* v_homepage_2162_; lean_object* v_license_2163_; lean_object* v_licenseFiles_2164_; lean_object* v_readmeFile_2165_; uint8_t v_reservoir_2166_; lean_object* v_enableArtifactCache_x3f_2167_; lean_object* v_restoreAllArtifacts_x3f_2168_; uint8_t v_libPrefixOnWindows_2169_; uint8_t v_allowImportAll_2170_; lean_object* v_builtinLint_x3f_2171_; lean_object* v_checks_2172_; uint8_t v_fixedToolchain_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
v_toWorkspaceConfig_2140_ = lean_ctor_get(v_cfg_2139_, 0);
v_toLeanConfig_2141_ = lean_ctor_get(v_cfg_2139_, 1);
v_bootstrap_2142_ = lean_ctor_get_uint8(v_cfg_2139_, sizeof(void*)*28);
v_extraDepTargets_2143_ = lean_ctor_get(v_cfg_2139_, 2);
v_precompileModules_2144_ = lean_ctor_get_uint8(v_cfg_2139_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2145_ = lean_ctor_get(v_cfg_2139_, 3);
v_srcDir_2146_ = lean_ctor_get(v_cfg_2139_, 4);
v_buildDir_2147_ = lean_ctor_get(v_cfg_2139_, 5);
v_leanLibDir_2148_ = lean_ctor_get(v_cfg_2139_, 6);
v_nativeLibDir_2149_ = lean_ctor_get(v_cfg_2139_, 7);
v_binDir_2150_ = lean_ctor_get(v_cfg_2139_, 8);
v_irDir_2151_ = lean_ctor_get(v_cfg_2139_, 9);
v_releaseRepo_2152_ = lean_ctor_get(v_cfg_2139_, 10);
v_buildArchive_2153_ = lean_ctor_get(v_cfg_2139_, 11);
v_preferReleaseBuild_2154_ = lean_ctor_get_uint8(v_cfg_2139_, sizeof(void*)*28 + 2);
v_testDriver_2155_ = lean_ctor_get(v_cfg_2139_, 12);
v_testDriverArgs_2156_ = lean_ctor_get(v_cfg_2139_, 13);
v_lintDriver_2157_ = lean_ctor_get(v_cfg_2139_, 14);
v_version_2158_ = lean_ctor_get(v_cfg_2139_, 16);
v_versionTags_2159_ = lean_ctor_get(v_cfg_2139_, 17);
v_description_2160_ = lean_ctor_get(v_cfg_2139_, 18);
v_keywords_2161_ = lean_ctor_get(v_cfg_2139_, 19);
v_homepage_2162_ = lean_ctor_get(v_cfg_2139_, 20);
v_license_2163_ = lean_ctor_get(v_cfg_2139_, 21);
v_licenseFiles_2164_ = lean_ctor_get(v_cfg_2139_, 22);
v_readmeFile_2165_ = lean_ctor_get(v_cfg_2139_, 23);
v_reservoir_2166_ = lean_ctor_get_uint8(v_cfg_2139_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2167_ = lean_ctor_get(v_cfg_2139_, 24);
v_restoreAllArtifacts_x3f_2168_ = lean_ctor_get(v_cfg_2139_, 25);
v_libPrefixOnWindows_2169_ = lean_ctor_get_uint8(v_cfg_2139_, sizeof(void*)*28 + 4);
v_allowImportAll_2170_ = lean_ctor_get_uint8(v_cfg_2139_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2171_ = lean_ctor_get(v_cfg_2139_, 26);
v_checks_2172_ = lean_ctor_get(v_cfg_2139_, 27);
v_fixedToolchain_2173_ = lean_ctor_get_uint8(v_cfg_2139_, sizeof(void*)*28 + 6);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_cfg_2139_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v_cfg_2139_, 15);
lean_dec(v_unused_2181_);
v___x_2175_ = v_cfg_2139_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_checks_2172_);
lean_inc(v_builtinLint_x3f_2171_);
lean_inc(v_restoreAllArtifacts_x3f_2168_);
lean_inc(v_enableArtifactCache_x3f_2167_);
lean_inc(v_readmeFile_2165_);
lean_inc(v_licenseFiles_2164_);
lean_inc(v_license_2163_);
lean_inc(v_homepage_2162_);
lean_inc(v_keywords_2161_);
lean_inc(v_description_2160_);
lean_inc(v_versionTags_2159_);
lean_inc(v_version_2158_);
lean_inc(v_lintDriver_2157_);
lean_inc(v_testDriverArgs_2156_);
lean_inc(v_testDriver_2155_);
lean_inc(v_buildArchive_2153_);
lean_inc(v_releaseRepo_2152_);
lean_inc(v_irDir_2151_);
lean_inc(v_binDir_2150_);
lean_inc(v_nativeLibDir_2149_);
lean_inc(v_leanLibDir_2148_);
lean_inc(v_buildDir_2147_);
lean_inc(v_srcDir_2146_);
lean_inc(v_moreGlobalServerArgs_2145_);
lean_inc(v_extraDepTargets_2143_);
lean_inc(v_toLeanConfig_2141_);
lean_inc(v_toWorkspaceConfig_2140_);
lean_dec(v_cfg_2139_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 15, v_val_2138_);
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_toWorkspaceConfig_2140_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_toLeanConfig_2141_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_extraDepTargets_2143_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v_moreGlobalServerArgs_2145_);
lean_ctor_set(v_reuseFailAlloc_2179_, 4, v_srcDir_2146_);
lean_ctor_set(v_reuseFailAlloc_2179_, 5, v_buildDir_2147_);
lean_ctor_set(v_reuseFailAlloc_2179_, 6, v_leanLibDir_2148_);
lean_ctor_set(v_reuseFailAlloc_2179_, 7, v_nativeLibDir_2149_);
lean_ctor_set(v_reuseFailAlloc_2179_, 8, v_binDir_2150_);
lean_ctor_set(v_reuseFailAlloc_2179_, 9, v_irDir_2151_);
lean_ctor_set(v_reuseFailAlloc_2179_, 10, v_releaseRepo_2152_);
lean_ctor_set(v_reuseFailAlloc_2179_, 11, v_buildArchive_2153_);
lean_ctor_set(v_reuseFailAlloc_2179_, 12, v_testDriver_2155_);
lean_ctor_set(v_reuseFailAlloc_2179_, 13, v_testDriverArgs_2156_);
lean_ctor_set(v_reuseFailAlloc_2179_, 14, v_lintDriver_2157_);
lean_ctor_set(v_reuseFailAlloc_2179_, 15, v_val_2138_);
lean_ctor_set(v_reuseFailAlloc_2179_, 16, v_version_2158_);
lean_ctor_set(v_reuseFailAlloc_2179_, 17, v_versionTags_2159_);
lean_ctor_set(v_reuseFailAlloc_2179_, 18, v_description_2160_);
lean_ctor_set(v_reuseFailAlloc_2179_, 19, v_keywords_2161_);
lean_ctor_set(v_reuseFailAlloc_2179_, 20, v_homepage_2162_);
lean_ctor_set(v_reuseFailAlloc_2179_, 21, v_license_2163_);
lean_ctor_set(v_reuseFailAlloc_2179_, 22, v_licenseFiles_2164_);
lean_ctor_set(v_reuseFailAlloc_2179_, 23, v_readmeFile_2165_);
lean_ctor_set(v_reuseFailAlloc_2179_, 24, v_enableArtifactCache_x3f_2167_);
lean_ctor_set(v_reuseFailAlloc_2179_, 25, v_restoreAllArtifacts_x3f_2168_);
lean_ctor_set(v_reuseFailAlloc_2179_, 26, v_builtinLint_x3f_2171_);
lean_ctor_set(v_reuseFailAlloc_2179_, 27, v_checks_2172_);
lean_ctor_set_uint8(v_reuseFailAlloc_2179_, sizeof(void*)*28, v_bootstrap_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2179_, sizeof(void*)*28 + 1, v_precompileModules_2144_);
lean_ctor_set_uint8(v_reuseFailAlloc_2179_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2179_, sizeof(void*)*28 + 3, v_reservoir_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2179_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2169_);
lean_ctor_set_uint8(v_reuseFailAlloc_2179_, sizeof(void*)*28 + 5, v_allowImportAll_2170_);
lean_ctor_set_uint8(v_reuseFailAlloc_2179_, sizeof(void*)*28 + 6, v_fixedToolchain_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__2(lean_object* v_f_2182_, lean_object* v_cfg_2183_){
_start:
{
lean_object* v_toWorkspaceConfig_2184_; lean_object* v_toLeanConfig_2185_; uint8_t v_bootstrap_2186_; lean_object* v_extraDepTargets_2187_; uint8_t v_precompileModules_2188_; lean_object* v_moreGlobalServerArgs_2189_; lean_object* v_srcDir_2190_; lean_object* v_buildDir_2191_; lean_object* v_leanLibDir_2192_; lean_object* v_nativeLibDir_2193_; lean_object* v_binDir_2194_; lean_object* v_irDir_2195_; lean_object* v_releaseRepo_2196_; lean_object* v_buildArchive_2197_; uint8_t v_preferReleaseBuild_2198_; lean_object* v_testDriver_2199_; lean_object* v_testDriverArgs_2200_; lean_object* v_lintDriver_2201_; lean_object* v_lintDriverArgs_2202_; lean_object* v_version_2203_; lean_object* v_versionTags_2204_; lean_object* v_description_2205_; lean_object* v_keywords_2206_; lean_object* v_homepage_2207_; lean_object* v_license_2208_; lean_object* v_licenseFiles_2209_; lean_object* v_readmeFile_2210_; uint8_t v_reservoir_2211_; lean_object* v_enableArtifactCache_x3f_2212_; lean_object* v_restoreAllArtifacts_x3f_2213_; uint8_t v_libPrefixOnWindows_2214_; uint8_t v_allowImportAll_2215_; lean_object* v_builtinLint_x3f_2216_; lean_object* v_checks_2217_; uint8_t v_fixedToolchain_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2226_; 
v_toWorkspaceConfig_2184_ = lean_ctor_get(v_cfg_2183_, 0);
v_toLeanConfig_2185_ = lean_ctor_get(v_cfg_2183_, 1);
v_bootstrap_2186_ = lean_ctor_get_uint8(v_cfg_2183_, sizeof(void*)*28);
v_extraDepTargets_2187_ = lean_ctor_get(v_cfg_2183_, 2);
v_precompileModules_2188_ = lean_ctor_get_uint8(v_cfg_2183_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2189_ = lean_ctor_get(v_cfg_2183_, 3);
v_srcDir_2190_ = lean_ctor_get(v_cfg_2183_, 4);
v_buildDir_2191_ = lean_ctor_get(v_cfg_2183_, 5);
v_leanLibDir_2192_ = lean_ctor_get(v_cfg_2183_, 6);
v_nativeLibDir_2193_ = lean_ctor_get(v_cfg_2183_, 7);
v_binDir_2194_ = lean_ctor_get(v_cfg_2183_, 8);
v_irDir_2195_ = lean_ctor_get(v_cfg_2183_, 9);
v_releaseRepo_2196_ = lean_ctor_get(v_cfg_2183_, 10);
v_buildArchive_2197_ = lean_ctor_get(v_cfg_2183_, 11);
v_preferReleaseBuild_2198_ = lean_ctor_get_uint8(v_cfg_2183_, sizeof(void*)*28 + 2);
v_testDriver_2199_ = lean_ctor_get(v_cfg_2183_, 12);
v_testDriverArgs_2200_ = lean_ctor_get(v_cfg_2183_, 13);
v_lintDriver_2201_ = lean_ctor_get(v_cfg_2183_, 14);
v_lintDriverArgs_2202_ = lean_ctor_get(v_cfg_2183_, 15);
v_version_2203_ = lean_ctor_get(v_cfg_2183_, 16);
v_versionTags_2204_ = lean_ctor_get(v_cfg_2183_, 17);
v_description_2205_ = lean_ctor_get(v_cfg_2183_, 18);
v_keywords_2206_ = lean_ctor_get(v_cfg_2183_, 19);
v_homepage_2207_ = lean_ctor_get(v_cfg_2183_, 20);
v_license_2208_ = lean_ctor_get(v_cfg_2183_, 21);
v_licenseFiles_2209_ = lean_ctor_get(v_cfg_2183_, 22);
v_readmeFile_2210_ = lean_ctor_get(v_cfg_2183_, 23);
v_reservoir_2211_ = lean_ctor_get_uint8(v_cfg_2183_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2212_ = lean_ctor_get(v_cfg_2183_, 24);
v_restoreAllArtifacts_x3f_2213_ = lean_ctor_get(v_cfg_2183_, 25);
v_libPrefixOnWindows_2214_ = lean_ctor_get_uint8(v_cfg_2183_, sizeof(void*)*28 + 4);
v_allowImportAll_2215_ = lean_ctor_get_uint8(v_cfg_2183_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2216_ = lean_ctor_get(v_cfg_2183_, 26);
v_checks_2217_ = lean_ctor_get(v_cfg_2183_, 27);
v_fixedToolchain_2218_ = lean_ctor_get_uint8(v_cfg_2183_, sizeof(void*)*28 + 6);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_cfg_2183_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2220_ = v_cfg_2183_;
v_isShared_2221_ = v_isSharedCheck_2226_;
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
lean_inc(v_lintDriverArgs_2202_);
lean_inc(v_lintDriver_2201_);
lean_inc(v_testDriverArgs_2200_);
lean_inc(v_testDriver_2199_);
lean_inc(v_buildArchive_2197_);
lean_inc(v_releaseRepo_2196_);
lean_inc(v_irDir_2195_);
lean_inc(v_binDir_2194_);
lean_inc(v_nativeLibDir_2193_);
lean_inc(v_leanLibDir_2192_);
lean_inc(v_buildDir_2191_);
lean_inc(v_srcDir_2190_);
lean_inc(v_moreGlobalServerArgs_2189_);
lean_inc(v_extraDepTargets_2187_);
lean_inc(v_toLeanConfig_2185_);
lean_inc(v_toWorkspaceConfig_2184_);
lean_dec(v_cfg_2183_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2226_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2222_ = lean_apply_1(v_f_2182_, v_lintDriverArgs_2202_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 15, v___x_2222_);
v___x_2224_ = v___x_2220_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_toWorkspaceConfig_2184_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_toLeanConfig_2185_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_extraDepTargets_2187_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_moreGlobalServerArgs_2189_);
lean_ctor_set(v_reuseFailAlloc_2225_, 4, v_srcDir_2190_);
lean_ctor_set(v_reuseFailAlloc_2225_, 5, v_buildDir_2191_);
lean_ctor_set(v_reuseFailAlloc_2225_, 6, v_leanLibDir_2192_);
lean_ctor_set(v_reuseFailAlloc_2225_, 7, v_nativeLibDir_2193_);
lean_ctor_set(v_reuseFailAlloc_2225_, 8, v_binDir_2194_);
lean_ctor_set(v_reuseFailAlloc_2225_, 9, v_irDir_2195_);
lean_ctor_set(v_reuseFailAlloc_2225_, 10, v_releaseRepo_2196_);
lean_ctor_set(v_reuseFailAlloc_2225_, 11, v_buildArchive_2197_);
lean_ctor_set(v_reuseFailAlloc_2225_, 12, v_testDriver_2199_);
lean_ctor_set(v_reuseFailAlloc_2225_, 13, v_testDriverArgs_2200_);
lean_ctor_set(v_reuseFailAlloc_2225_, 14, v_lintDriver_2201_);
lean_ctor_set(v_reuseFailAlloc_2225_, 15, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2225_, 16, v_version_2203_);
lean_ctor_set(v_reuseFailAlloc_2225_, 17, v_versionTags_2204_);
lean_ctor_set(v_reuseFailAlloc_2225_, 18, v_description_2205_);
lean_ctor_set(v_reuseFailAlloc_2225_, 19, v_keywords_2206_);
lean_ctor_set(v_reuseFailAlloc_2225_, 20, v_homepage_2207_);
lean_ctor_set(v_reuseFailAlloc_2225_, 21, v_license_2208_);
lean_ctor_set(v_reuseFailAlloc_2225_, 22, v_licenseFiles_2209_);
lean_ctor_set(v_reuseFailAlloc_2225_, 23, v_readmeFile_2210_);
lean_ctor_set(v_reuseFailAlloc_2225_, 24, v_enableArtifactCache_x3f_2212_);
lean_ctor_set(v_reuseFailAlloc_2225_, 25, v_restoreAllArtifacts_x3f_2213_);
lean_ctor_set(v_reuseFailAlloc_2225_, 26, v_builtinLint_x3f_2216_);
lean_ctor_set(v_reuseFailAlloc_2225_, 27, v_checks_2217_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*28, v_bootstrap_2186_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*28 + 1, v_precompileModules_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2198_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*28 + 3, v_reservoir_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*28 + 5, v_allowImportAll_2215_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*28 + 6, v_fixedToolchain_2218_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg(){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = ((lean_object*)(l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__3));
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___boxed(lean_object* v___dummy_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lake_PackageConfig_lintDriverArgs___proj___redArg();
return v_res_2238_;
}
}
static lean_object* _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0(void){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lake_PackageConfig_lintDriverArgs___proj___redArg();
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object* v_p_2240_, lean_object* v_n_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_obj_once(&l_Lake_PackageConfig_lintDriverArgs___proj___closed__0, &l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object* v_p_2243_, lean_object* v_n_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2243_, v_n_2244_);
lean_dec(v_n_2244_);
lean_dec(v_p_2243_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_obj_once(&l_Lake_PackageConfig_lintDriverArgs___proj___closed__0, &l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg___boxed(lean_object* v___dummy_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg();
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object* v_p_2250_, lean_object* v_n_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_obj_once(&l_Lake_PackageConfig_lintDriverArgs___proj___closed__0, &l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object* v_p_2253_, lean_object* v_n_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField(v_p_2253_, v_n_2254_);
lean_dec(v_n_2254_);
lean_dec(v_p_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__0(lean_object* v_cfg_2256_){
_start:
{
lean_object* v_version_2257_; 
v_version_2257_ = lean_ctor_get(v_cfg_2256_, 16);
lean_inc_ref(v_version_2257_);
return v_version_2257_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__0___boxed(lean_object* v_cfg_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lake_PackageConfig_version___proj___redArg___lam__0(v_cfg_2258_);
lean_dec_ref(v_cfg_2258_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__1(lean_object* v_val_2260_, lean_object* v_cfg_2261_){
_start:
{
lean_object* v_toWorkspaceConfig_2262_; lean_object* v_toLeanConfig_2263_; uint8_t v_bootstrap_2264_; lean_object* v_extraDepTargets_2265_; uint8_t v_precompileModules_2266_; lean_object* v_moreGlobalServerArgs_2267_; lean_object* v_srcDir_2268_; lean_object* v_buildDir_2269_; lean_object* v_leanLibDir_2270_; lean_object* v_nativeLibDir_2271_; lean_object* v_binDir_2272_; lean_object* v_irDir_2273_; lean_object* v_releaseRepo_2274_; lean_object* v_buildArchive_2275_; uint8_t v_preferReleaseBuild_2276_; lean_object* v_testDriver_2277_; lean_object* v_testDriverArgs_2278_; lean_object* v_lintDriver_2279_; lean_object* v_lintDriverArgs_2280_; lean_object* v_versionTags_2281_; lean_object* v_description_2282_; lean_object* v_keywords_2283_; lean_object* v_homepage_2284_; lean_object* v_license_2285_; lean_object* v_licenseFiles_2286_; lean_object* v_readmeFile_2287_; uint8_t v_reservoir_2288_; lean_object* v_enableArtifactCache_x3f_2289_; lean_object* v_restoreAllArtifacts_x3f_2290_; uint8_t v_libPrefixOnWindows_2291_; uint8_t v_allowImportAll_2292_; lean_object* v_builtinLint_x3f_2293_; lean_object* v_checks_2294_; uint8_t v_fixedToolchain_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
v_toWorkspaceConfig_2262_ = lean_ctor_get(v_cfg_2261_, 0);
v_toLeanConfig_2263_ = lean_ctor_get(v_cfg_2261_, 1);
v_bootstrap_2264_ = lean_ctor_get_uint8(v_cfg_2261_, sizeof(void*)*28);
v_extraDepTargets_2265_ = lean_ctor_get(v_cfg_2261_, 2);
v_precompileModules_2266_ = lean_ctor_get_uint8(v_cfg_2261_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2267_ = lean_ctor_get(v_cfg_2261_, 3);
v_srcDir_2268_ = lean_ctor_get(v_cfg_2261_, 4);
v_buildDir_2269_ = lean_ctor_get(v_cfg_2261_, 5);
v_leanLibDir_2270_ = lean_ctor_get(v_cfg_2261_, 6);
v_nativeLibDir_2271_ = lean_ctor_get(v_cfg_2261_, 7);
v_binDir_2272_ = lean_ctor_get(v_cfg_2261_, 8);
v_irDir_2273_ = lean_ctor_get(v_cfg_2261_, 9);
v_releaseRepo_2274_ = lean_ctor_get(v_cfg_2261_, 10);
v_buildArchive_2275_ = lean_ctor_get(v_cfg_2261_, 11);
v_preferReleaseBuild_2276_ = lean_ctor_get_uint8(v_cfg_2261_, sizeof(void*)*28 + 2);
v_testDriver_2277_ = lean_ctor_get(v_cfg_2261_, 12);
v_testDriverArgs_2278_ = lean_ctor_get(v_cfg_2261_, 13);
v_lintDriver_2279_ = lean_ctor_get(v_cfg_2261_, 14);
v_lintDriverArgs_2280_ = lean_ctor_get(v_cfg_2261_, 15);
v_versionTags_2281_ = lean_ctor_get(v_cfg_2261_, 17);
v_description_2282_ = lean_ctor_get(v_cfg_2261_, 18);
v_keywords_2283_ = lean_ctor_get(v_cfg_2261_, 19);
v_homepage_2284_ = lean_ctor_get(v_cfg_2261_, 20);
v_license_2285_ = lean_ctor_get(v_cfg_2261_, 21);
v_licenseFiles_2286_ = lean_ctor_get(v_cfg_2261_, 22);
v_readmeFile_2287_ = lean_ctor_get(v_cfg_2261_, 23);
v_reservoir_2288_ = lean_ctor_get_uint8(v_cfg_2261_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2289_ = lean_ctor_get(v_cfg_2261_, 24);
v_restoreAllArtifacts_x3f_2290_ = lean_ctor_get(v_cfg_2261_, 25);
v_libPrefixOnWindows_2291_ = lean_ctor_get_uint8(v_cfg_2261_, sizeof(void*)*28 + 4);
v_allowImportAll_2292_ = lean_ctor_get_uint8(v_cfg_2261_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2293_ = lean_ctor_get(v_cfg_2261_, 26);
v_checks_2294_ = lean_ctor_get(v_cfg_2261_, 27);
v_fixedToolchain_2295_ = lean_ctor_get_uint8(v_cfg_2261_, sizeof(void*)*28 + 6);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_cfg_2261_);
if (v_isSharedCheck_2302_ == 0)
{
lean_object* v_unused_2303_; 
v_unused_2303_ = lean_ctor_get(v_cfg_2261_, 16);
lean_dec(v_unused_2303_);
v___x_2297_ = v_cfg_2261_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_checks_2294_);
lean_inc(v_builtinLint_x3f_2293_);
lean_inc(v_restoreAllArtifacts_x3f_2290_);
lean_inc(v_enableArtifactCache_x3f_2289_);
lean_inc(v_readmeFile_2287_);
lean_inc(v_licenseFiles_2286_);
lean_inc(v_license_2285_);
lean_inc(v_homepage_2284_);
lean_inc(v_keywords_2283_);
lean_inc(v_description_2282_);
lean_inc(v_versionTags_2281_);
lean_inc(v_lintDriverArgs_2280_);
lean_inc(v_lintDriver_2279_);
lean_inc(v_testDriverArgs_2278_);
lean_inc(v_testDriver_2277_);
lean_inc(v_buildArchive_2275_);
lean_inc(v_releaseRepo_2274_);
lean_inc(v_irDir_2273_);
lean_inc(v_binDir_2272_);
lean_inc(v_nativeLibDir_2271_);
lean_inc(v_leanLibDir_2270_);
lean_inc(v_buildDir_2269_);
lean_inc(v_srcDir_2268_);
lean_inc(v_moreGlobalServerArgs_2267_);
lean_inc(v_extraDepTargets_2265_);
lean_inc(v_toLeanConfig_2263_);
lean_inc(v_toWorkspaceConfig_2262_);
lean_dec(v_cfg_2261_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 16, v_val_2260_);
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_toWorkspaceConfig_2262_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_toLeanConfig_2263_);
lean_ctor_set(v_reuseFailAlloc_2301_, 2, v_extraDepTargets_2265_);
lean_ctor_set(v_reuseFailAlloc_2301_, 3, v_moreGlobalServerArgs_2267_);
lean_ctor_set(v_reuseFailAlloc_2301_, 4, v_srcDir_2268_);
lean_ctor_set(v_reuseFailAlloc_2301_, 5, v_buildDir_2269_);
lean_ctor_set(v_reuseFailAlloc_2301_, 6, v_leanLibDir_2270_);
lean_ctor_set(v_reuseFailAlloc_2301_, 7, v_nativeLibDir_2271_);
lean_ctor_set(v_reuseFailAlloc_2301_, 8, v_binDir_2272_);
lean_ctor_set(v_reuseFailAlloc_2301_, 9, v_irDir_2273_);
lean_ctor_set(v_reuseFailAlloc_2301_, 10, v_releaseRepo_2274_);
lean_ctor_set(v_reuseFailAlloc_2301_, 11, v_buildArchive_2275_);
lean_ctor_set(v_reuseFailAlloc_2301_, 12, v_testDriver_2277_);
lean_ctor_set(v_reuseFailAlloc_2301_, 13, v_testDriverArgs_2278_);
lean_ctor_set(v_reuseFailAlloc_2301_, 14, v_lintDriver_2279_);
lean_ctor_set(v_reuseFailAlloc_2301_, 15, v_lintDriverArgs_2280_);
lean_ctor_set(v_reuseFailAlloc_2301_, 16, v_val_2260_);
lean_ctor_set(v_reuseFailAlloc_2301_, 17, v_versionTags_2281_);
lean_ctor_set(v_reuseFailAlloc_2301_, 18, v_description_2282_);
lean_ctor_set(v_reuseFailAlloc_2301_, 19, v_keywords_2283_);
lean_ctor_set(v_reuseFailAlloc_2301_, 20, v_homepage_2284_);
lean_ctor_set(v_reuseFailAlloc_2301_, 21, v_license_2285_);
lean_ctor_set(v_reuseFailAlloc_2301_, 22, v_licenseFiles_2286_);
lean_ctor_set(v_reuseFailAlloc_2301_, 23, v_readmeFile_2287_);
lean_ctor_set(v_reuseFailAlloc_2301_, 24, v_enableArtifactCache_x3f_2289_);
lean_ctor_set(v_reuseFailAlloc_2301_, 25, v_restoreAllArtifacts_x3f_2290_);
lean_ctor_set(v_reuseFailAlloc_2301_, 26, v_builtinLint_x3f_2293_);
lean_ctor_set(v_reuseFailAlloc_2301_, 27, v_checks_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, sizeof(void*)*28, v_bootstrap_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, sizeof(void*)*28 + 1, v_precompileModules_2266_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2276_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, sizeof(void*)*28 + 3, v_reservoir_2288_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2291_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, sizeof(void*)*28 + 5, v_allowImportAll_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, sizeof(void*)*28 + 6, v_fixedToolchain_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__2(lean_object* v_f_2304_, lean_object* v_cfg_2305_){
_start:
{
lean_object* v_toWorkspaceConfig_2306_; lean_object* v_toLeanConfig_2307_; uint8_t v_bootstrap_2308_; lean_object* v_extraDepTargets_2309_; uint8_t v_precompileModules_2310_; lean_object* v_moreGlobalServerArgs_2311_; lean_object* v_srcDir_2312_; lean_object* v_buildDir_2313_; lean_object* v_leanLibDir_2314_; lean_object* v_nativeLibDir_2315_; lean_object* v_binDir_2316_; lean_object* v_irDir_2317_; lean_object* v_releaseRepo_2318_; lean_object* v_buildArchive_2319_; uint8_t v_preferReleaseBuild_2320_; lean_object* v_testDriver_2321_; lean_object* v_testDriverArgs_2322_; lean_object* v_lintDriver_2323_; lean_object* v_lintDriverArgs_2324_; lean_object* v_version_2325_; lean_object* v_versionTags_2326_; lean_object* v_description_2327_; lean_object* v_keywords_2328_; lean_object* v_homepage_2329_; lean_object* v_license_2330_; lean_object* v_licenseFiles_2331_; lean_object* v_readmeFile_2332_; uint8_t v_reservoir_2333_; lean_object* v_enableArtifactCache_x3f_2334_; lean_object* v_restoreAllArtifacts_x3f_2335_; uint8_t v_libPrefixOnWindows_2336_; uint8_t v_allowImportAll_2337_; lean_object* v_builtinLint_x3f_2338_; lean_object* v_checks_2339_; uint8_t v_fixedToolchain_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2348_; 
v_toWorkspaceConfig_2306_ = lean_ctor_get(v_cfg_2305_, 0);
v_toLeanConfig_2307_ = lean_ctor_get(v_cfg_2305_, 1);
v_bootstrap_2308_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*28);
v_extraDepTargets_2309_ = lean_ctor_get(v_cfg_2305_, 2);
v_precompileModules_2310_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2311_ = lean_ctor_get(v_cfg_2305_, 3);
v_srcDir_2312_ = lean_ctor_get(v_cfg_2305_, 4);
v_buildDir_2313_ = lean_ctor_get(v_cfg_2305_, 5);
v_leanLibDir_2314_ = lean_ctor_get(v_cfg_2305_, 6);
v_nativeLibDir_2315_ = lean_ctor_get(v_cfg_2305_, 7);
v_binDir_2316_ = lean_ctor_get(v_cfg_2305_, 8);
v_irDir_2317_ = lean_ctor_get(v_cfg_2305_, 9);
v_releaseRepo_2318_ = lean_ctor_get(v_cfg_2305_, 10);
v_buildArchive_2319_ = lean_ctor_get(v_cfg_2305_, 11);
v_preferReleaseBuild_2320_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*28 + 2);
v_testDriver_2321_ = lean_ctor_get(v_cfg_2305_, 12);
v_testDriverArgs_2322_ = lean_ctor_get(v_cfg_2305_, 13);
v_lintDriver_2323_ = lean_ctor_get(v_cfg_2305_, 14);
v_lintDriverArgs_2324_ = lean_ctor_get(v_cfg_2305_, 15);
v_version_2325_ = lean_ctor_get(v_cfg_2305_, 16);
v_versionTags_2326_ = lean_ctor_get(v_cfg_2305_, 17);
v_description_2327_ = lean_ctor_get(v_cfg_2305_, 18);
v_keywords_2328_ = lean_ctor_get(v_cfg_2305_, 19);
v_homepage_2329_ = lean_ctor_get(v_cfg_2305_, 20);
v_license_2330_ = lean_ctor_get(v_cfg_2305_, 21);
v_licenseFiles_2331_ = lean_ctor_get(v_cfg_2305_, 22);
v_readmeFile_2332_ = lean_ctor_get(v_cfg_2305_, 23);
v_reservoir_2333_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2334_ = lean_ctor_get(v_cfg_2305_, 24);
v_restoreAllArtifacts_x3f_2335_ = lean_ctor_get(v_cfg_2305_, 25);
v_libPrefixOnWindows_2336_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*28 + 4);
v_allowImportAll_2337_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2338_ = lean_ctor_get(v_cfg_2305_, 26);
v_checks_2339_ = lean_ctor_get(v_cfg_2305_, 27);
v_fixedToolchain_2340_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*28 + 6);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_cfg_2305_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2342_ = v_cfg_2305_;
v_isShared_2343_ = v_isSharedCheck_2348_;
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
lean_inc(v_lintDriverArgs_2324_);
lean_inc(v_lintDriver_2323_);
lean_inc(v_testDriverArgs_2322_);
lean_inc(v_testDriver_2321_);
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
v_isShared_2343_ = v_isSharedCheck_2348_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2344_ = lean_apply_1(v_f_2304_, v_version_2325_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 16, v___x_2344_);
v___x_2346_ = v___x_2342_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_toWorkspaceConfig_2306_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_toLeanConfig_2307_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_extraDepTargets_2309_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_moreGlobalServerArgs_2311_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_srcDir_2312_);
lean_ctor_set(v_reuseFailAlloc_2347_, 5, v_buildDir_2313_);
lean_ctor_set(v_reuseFailAlloc_2347_, 6, v_leanLibDir_2314_);
lean_ctor_set(v_reuseFailAlloc_2347_, 7, v_nativeLibDir_2315_);
lean_ctor_set(v_reuseFailAlloc_2347_, 8, v_binDir_2316_);
lean_ctor_set(v_reuseFailAlloc_2347_, 9, v_irDir_2317_);
lean_ctor_set(v_reuseFailAlloc_2347_, 10, v_releaseRepo_2318_);
lean_ctor_set(v_reuseFailAlloc_2347_, 11, v_buildArchive_2319_);
lean_ctor_set(v_reuseFailAlloc_2347_, 12, v_testDriver_2321_);
lean_ctor_set(v_reuseFailAlloc_2347_, 13, v_testDriverArgs_2322_);
lean_ctor_set(v_reuseFailAlloc_2347_, 14, v_lintDriver_2323_);
lean_ctor_set(v_reuseFailAlloc_2347_, 15, v_lintDriverArgs_2324_);
lean_ctor_set(v_reuseFailAlloc_2347_, 16, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2347_, 17, v_versionTags_2326_);
lean_ctor_set(v_reuseFailAlloc_2347_, 18, v_description_2327_);
lean_ctor_set(v_reuseFailAlloc_2347_, 19, v_keywords_2328_);
lean_ctor_set(v_reuseFailAlloc_2347_, 20, v_homepage_2329_);
lean_ctor_set(v_reuseFailAlloc_2347_, 21, v_license_2330_);
lean_ctor_set(v_reuseFailAlloc_2347_, 22, v_licenseFiles_2331_);
lean_ctor_set(v_reuseFailAlloc_2347_, 23, v_readmeFile_2332_);
lean_ctor_set(v_reuseFailAlloc_2347_, 24, v_enableArtifactCache_x3f_2334_);
lean_ctor_set(v_reuseFailAlloc_2347_, 25, v_restoreAllArtifacts_x3f_2335_);
lean_ctor_set(v_reuseFailAlloc_2347_, 26, v_builtinLint_x3f_2338_);
lean_ctor_set(v_reuseFailAlloc_2347_, 27, v_checks_2339_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*28, v_bootstrap_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*28 + 1, v_precompileModules_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2320_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*28 + 3, v_reservoir_2333_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2336_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*28 + 5, v_allowImportAll_2337_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*28 + 6, v_fixedToolchain_2340_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__3(lean_object* v_x_2349_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__4));
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__3___boxed(lean_object* v_x_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lake_PackageConfig_version___proj___redArg___lam__3(v_x_2351_);
lean_dec_ref(v_x_2351_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg(){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___redArg___closed__4));
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___boxed(lean_object* v___dummy_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lake_PackageConfig_version___proj___redArg();
return v_res_2365_;
}
}
static lean_object* _init_l_Lake_PackageConfig_version___proj___closed__0(void){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lake_PackageConfig_version___proj___redArg();
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object* v_p_2367_, lean_object* v_n_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_obj_once(&l_Lake_PackageConfig_version___proj___closed__0, &l_Lake_PackageConfig_version___proj___closed__0_once, _init_l_Lake_PackageConfig_version___proj___closed__0);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object* v_p_2370_, lean_object* v_n_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lake_PackageConfig_version___proj(v_p_2370_, v_n_2371_);
lean_dec(v_n_2371_);
lean_dec(v_p_2370_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___redArg(){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_obj_once(&l_Lake_PackageConfig_version___proj___closed__0, &l_Lake_PackageConfig_version___proj___closed__0_once, _init_l_Lake_PackageConfig_version___proj___closed__0);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___redArg___boxed(lean_object* v___dummy_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lake_PackageConfig_version_instConfigField___redArg();
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object* v_p_2377_, lean_object* v_n_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_obj_once(&l_Lake_PackageConfig_version___proj___closed__0, &l_Lake_PackageConfig_version___proj___closed__0_once, _init_l_Lake_PackageConfig_version___proj___closed__0);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object* v_p_2380_, lean_object* v_n_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lake_PackageConfig_version_instConfigField(v_p_2380_, v_n_2381_);
lean_dec(v_n_2381_);
lean_dec(v_p_2380_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__0(lean_object* v_cfg_2383_){
_start:
{
lean_object* v_versionTags_2384_; 
v_versionTags_2384_ = lean_ctor_get(v_cfg_2383_, 17);
lean_inc_ref(v_versionTags_2384_);
return v_versionTags_2384_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__0___boxed(lean_object* v_cfg_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lake_PackageConfig_versionTags___proj___redArg___lam__0(v_cfg_2385_);
lean_dec_ref(v_cfg_2385_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__1(lean_object* v_val_2387_, lean_object* v_cfg_2388_){
_start:
{
lean_object* v_toWorkspaceConfig_2389_; lean_object* v_toLeanConfig_2390_; uint8_t v_bootstrap_2391_; lean_object* v_extraDepTargets_2392_; uint8_t v_precompileModules_2393_; lean_object* v_moreGlobalServerArgs_2394_; lean_object* v_srcDir_2395_; lean_object* v_buildDir_2396_; lean_object* v_leanLibDir_2397_; lean_object* v_nativeLibDir_2398_; lean_object* v_binDir_2399_; lean_object* v_irDir_2400_; lean_object* v_releaseRepo_2401_; lean_object* v_buildArchive_2402_; uint8_t v_preferReleaseBuild_2403_; lean_object* v_testDriver_2404_; lean_object* v_testDriverArgs_2405_; lean_object* v_lintDriver_2406_; lean_object* v_lintDriverArgs_2407_; lean_object* v_version_2408_; lean_object* v_description_2409_; lean_object* v_keywords_2410_; lean_object* v_homepage_2411_; lean_object* v_license_2412_; lean_object* v_licenseFiles_2413_; lean_object* v_readmeFile_2414_; uint8_t v_reservoir_2415_; lean_object* v_enableArtifactCache_x3f_2416_; lean_object* v_restoreAllArtifacts_x3f_2417_; uint8_t v_libPrefixOnWindows_2418_; uint8_t v_allowImportAll_2419_; lean_object* v_builtinLint_x3f_2420_; lean_object* v_checks_2421_; uint8_t v_fixedToolchain_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
v_toWorkspaceConfig_2389_ = lean_ctor_get(v_cfg_2388_, 0);
v_toLeanConfig_2390_ = lean_ctor_get(v_cfg_2388_, 1);
v_bootstrap_2391_ = lean_ctor_get_uint8(v_cfg_2388_, sizeof(void*)*28);
v_extraDepTargets_2392_ = lean_ctor_get(v_cfg_2388_, 2);
v_precompileModules_2393_ = lean_ctor_get_uint8(v_cfg_2388_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2394_ = lean_ctor_get(v_cfg_2388_, 3);
v_srcDir_2395_ = lean_ctor_get(v_cfg_2388_, 4);
v_buildDir_2396_ = lean_ctor_get(v_cfg_2388_, 5);
v_leanLibDir_2397_ = lean_ctor_get(v_cfg_2388_, 6);
v_nativeLibDir_2398_ = lean_ctor_get(v_cfg_2388_, 7);
v_binDir_2399_ = lean_ctor_get(v_cfg_2388_, 8);
v_irDir_2400_ = lean_ctor_get(v_cfg_2388_, 9);
v_releaseRepo_2401_ = lean_ctor_get(v_cfg_2388_, 10);
v_buildArchive_2402_ = lean_ctor_get(v_cfg_2388_, 11);
v_preferReleaseBuild_2403_ = lean_ctor_get_uint8(v_cfg_2388_, sizeof(void*)*28 + 2);
v_testDriver_2404_ = lean_ctor_get(v_cfg_2388_, 12);
v_testDriverArgs_2405_ = lean_ctor_get(v_cfg_2388_, 13);
v_lintDriver_2406_ = lean_ctor_get(v_cfg_2388_, 14);
v_lintDriverArgs_2407_ = lean_ctor_get(v_cfg_2388_, 15);
v_version_2408_ = lean_ctor_get(v_cfg_2388_, 16);
v_description_2409_ = lean_ctor_get(v_cfg_2388_, 18);
v_keywords_2410_ = lean_ctor_get(v_cfg_2388_, 19);
v_homepage_2411_ = lean_ctor_get(v_cfg_2388_, 20);
v_license_2412_ = lean_ctor_get(v_cfg_2388_, 21);
v_licenseFiles_2413_ = lean_ctor_get(v_cfg_2388_, 22);
v_readmeFile_2414_ = lean_ctor_get(v_cfg_2388_, 23);
v_reservoir_2415_ = lean_ctor_get_uint8(v_cfg_2388_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2416_ = lean_ctor_get(v_cfg_2388_, 24);
v_restoreAllArtifacts_x3f_2417_ = lean_ctor_get(v_cfg_2388_, 25);
v_libPrefixOnWindows_2418_ = lean_ctor_get_uint8(v_cfg_2388_, sizeof(void*)*28 + 4);
v_allowImportAll_2419_ = lean_ctor_get_uint8(v_cfg_2388_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2420_ = lean_ctor_get(v_cfg_2388_, 26);
v_checks_2421_ = lean_ctor_get(v_cfg_2388_, 27);
v_fixedToolchain_2422_ = lean_ctor_get_uint8(v_cfg_2388_, sizeof(void*)*28 + 6);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_cfg_2388_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; 
v_unused_2430_ = lean_ctor_get(v_cfg_2388_, 17);
lean_dec(v_unused_2430_);
v___x_2424_ = v_cfg_2388_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_checks_2421_);
lean_inc(v_builtinLint_x3f_2420_);
lean_inc(v_restoreAllArtifacts_x3f_2417_);
lean_inc(v_enableArtifactCache_x3f_2416_);
lean_inc(v_readmeFile_2414_);
lean_inc(v_licenseFiles_2413_);
lean_inc(v_license_2412_);
lean_inc(v_homepage_2411_);
lean_inc(v_keywords_2410_);
lean_inc(v_description_2409_);
lean_inc(v_version_2408_);
lean_inc(v_lintDriverArgs_2407_);
lean_inc(v_lintDriver_2406_);
lean_inc(v_testDriverArgs_2405_);
lean_inc(v_testDriver_2404_);
lean_inc(v_buildArchive_2402_);
lean_inc(v_releaseRepo_2401_);
lean_inc(v_irDir_2400_);
lean_inc(v_binDir_2399_);
lean_inc(v_nativeLibDir_2398_);
lean_inc(v_leanLibDir_2397_);
lean_inc(v_buildDir_2396_);
lean_inc(v_srcDir_2395_);
lean_inc(v_moreGlobalServerArgs_2394_);
lean_inc(v_extraDepTargets_2392_);
lean_inc(v_toLeanConfig_2390_);
lean_inc(v_toWorkspaceConfig_2389_);
lean_dec(v_cfg_2388_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 17, v_val_2387_);
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_toWorkspaceConfig_2389_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_toLeanConfig_2390_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v_extraDepTargets_2392_);
lean_ctor_set(v_reuseFailAlloc_2428_, 3, v_moreGlobalServerArgs_2394_);
lean_ctor_set(v_reuseFailAlloc_2428_, 4, v_srcDir_2395_);
lean_ctor_set(v_reuseFailAlloc_2428_, 5, v_buildDir_2396_);
lean_ctor_set(v_reuseFailAlloc_2428_, 6, v_leanLibDir_2397_);
lean_ctor_set(v_reuseFailAlloc_2428_, 7, v_nativeLibDir_2398_);
lean_ctor_set(v_reuseFailAlloc_2428_, 8, v_binDir_2399_);
lean_ctor_set(v_reuseFailAlloc_2428_, 9, v_irDir_2400_);
lean_ctor_set(v_reuseFailAlloc_2428_, 10, v_releaseRepo_2401_);
lean_ctor_set(v_reuseFailAlloc_2428_, 11, v_buildArchive_2402_);
lean_ctor_set(v_reuseFailAlloc_2428_, 12, v_testDriver_2404_);
lean_ctor_set(v_reuseFailAlloc_2428_, 13, v_testDriverArgs_2405_);
lean_ctor_set(v_reuseFailAlloc_2428_, 14, v_lintDriver_2406_);
lean_ctor_set(v_reuseFailAlloc_2428_, 15, v_lintDriverArgs_2407_);
lean_ctor_set(v_reuseFailAlloc_2428_, 16, v_version_2408_);
lean_ctor_set(v_reuseFailAlloc_2428_, 17, v_val_2387_);
lean_ctor_set(v_reuseFailAlloc_2428_, 18, v_description_2409_);
lean_ctor_set(v_reuseFailAlloc_2428_, 19, v_keywords_2410_);
lean_ctor_set(v_reuseFailAlloc_2428_, 20, v_homepage_2411_);
lean_ctor_set(v_reuseFailAlloc_2428_, 21, v_license_2412_);
lean_ctor_set(v_reuseFailAlloc_2428_, 22, v_licenseFiles_2413_);
lean_ctor_set(v_reuseFailAlloc_2428_, 23, v_readmeFile_2414_);
lean_ctor_set(v_reuseFailAlloc_2428_, 24, v_enableArtifactCache_x3f_2416_);
lean_ctor_set(v_reuseFailAlloc_2428_, 25, v_restoreAllArtifacts_x3f_2417_);
lean_ctor_set(v_reuseFailAlloc_2428_, 26, v_builtinLint_x3f_2420_);
lean_ctor_set(v_reuseFailAlloc_2428_, 27, v_checks_2421_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*28, v_bootstrap_2391_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*28 + 1, v_precompileModules_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2403_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*28 + 3, v_reservoir_2415_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2418_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*28 + 5, v_allowImportAll_2419_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*28 + 6, v_fixedToolchain_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__2(lean_object* v_f_2431_, lean_object* v_cfg_2432_){
_start:
{
lean_object* v_toWorkspaceConfig_2433_; lean_object* v_toLeanConfig_2434_; uint8_t v_bootstrap_2435_; lean_object* v_extraDepTargets_2436_; uint8_t v_precompileModules_2437_; lean_object* v_moreGlobalServerArgs_2438_; lean_object* v_srcDir_2439_; lean_object* v_buildDir_2440_; lean_object* v_leanLibDir_2441_; lean_object* v_nativeLibDir_2442_; lean_object* v_binDir_2443_; lean_object* v_irDir_2444_; lean_object* v_releaseRepo_2445_; lean_object* v_buildArchive_2446_; uint8_t v_preferReleaseBuild_2447_; lean_object* v_testDriver_2448_; lean_object* v_testDriverArgs_2449_; lean_object* v_lintDriver_2450_; lean_object* v_lintDriverArgs_2451_; lean_object* v_version_2452_; lean_object* v_versionTags_2453_; lean_object* v_description_2454_; lean_object* v_keywords_2455_; lean_object* v_homepage_2456_; lean_object* v_license_2457_; lean_object* v_licenseFiles_2458_; lean_object* v_readmeFile_2459_; uint8_t v_reservoir_2460_; lean_object* v_enableArtifactCache_x3f_2461_; lean_object* v_restoreAllArtifacts_x3f_2462_; uint8_t v_libPrefixOnWindows_2463_; uint8_t v_allowImportAll_2464_; lean_object* v_builtinLint_x3f_2465_; lean_object* v_checks_2466_; uint8_t v_fixedToolchain_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2475_; 
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
v_keywords_2455_ = lean_ctor_get(v_cfg_2432_, 19);
v_homepage_2456_ = lean_ctor_get(v_cfg_2432_, 20);
v_license_2457_ = lean_ctor_get(v_cfg_2432_, 21);
v_licenseFiles_2458_ = lean_ctor_get(v_cfg_2432_, 22);
v_readmeFile_2459_ = lean_ctor_get(v_cfg_2432_, 23);
v_reservoir_2460_ = lean_ctor_get_uint8(v_cfg_2432_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2461_ = lean_ctor_get(v_cfg_2432_, 24);
v_restoreAllArtifacts_x3f_2462_ = lean_ctor_get(v_cfg_2432_, 25);
v_libPrefixOnWindows_2463_ = lean_ctor_get_uint8(v_cfg_2432_, sizeof(void*)*28 + 4);
v_allowImportAll_2464_ = lean_ctor_get_uint8(v_cfg_2432_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2465_ = lean_ctor_get(v_cfg_2432_, 26);
v_checks_2466_ = lean_ctor_get(v_cfg_2432_, 27);
v_fixedToolchain_2467_ = lean_ctor_get_uint8(v_cfg_2432_, sizeof(void*)*28 + 6);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_cfg_2432_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2469_ = v_cfg_2432_;
v_isShared_2470_ = v_isSharedCheck_2475_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_checks_2466_);
lean_inc(v_builtinLint_x3f_2465_);
lean_inc(v_restoreAllArtifacts_x3f_2462_);
lean_inc(v_enableArtifactCache_x3f_2461_);
lean_inc(v_readmeFile_2459_);
lean_inc(v_licenseFiles_2458_);
lean_inc(v_license_2457_);
lean_inc(v_homepage_2456_);
lean_inc(v_keywords_2455_);
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
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2475_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2471_ = lean_apply_1(v_f_2431_, v_versionTags_2453_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 17, v___x_2471_);
v___x_2473_ = v___x_2469_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_toWorkspaceConfig_2433_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_toLeanConfig_2434_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_extraDepTargets_2436_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v_moreGlobalServerArgs_2438_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v_srcDir_2439_);
lean_ctor_set(v_reuseFailAlloc_2474_, 5, v_buildDir_2440_);
lean_ctor_set(v_reuseFailAlloc_2474_, 6, v_leanLibDir_2441_);
lean_ctor_set(v_reuseFailAlloc_2474_, 7, v_nativeLibDir_2442_);
lean_ctor_set(v_reuseFailAlloc_2474_, 8, v_binDir_2443_);
lean_ctor_set(v_reuseFailAlloc_2474_, 9, v_irDir_2444_);
lean_ctor_set(v_reuseFailAlloc_2474_, 10, v_releaseRepo_2445_);
lean_ctor_set(v_reuseFailAlloc_2474_, 11, v_buildArchive_2446_);
lean_ctor_set(v_reuseFailAlloc_2474_, 12, v_testDriver_2448_);
lean_ctor_set(v_reuseFailAlloc_2474_, 13, v_testDriverArgs_2449_);
lean_ctor_set(v_reuseFailAlloc_2474_, 14, v_lintDriver_2450_);
lean_ctor_set(v_reuseFailAlloc_2474_, 15, v_lintDriverArgs_2451_);
lean_ctor_set(v_reuseFailAlloc_2474_, 16, v_version_2452_);
lean_ctor_set(v_reuseFailAlloc_2474_, 17, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2474_, 18, v_description_2454_);
lean_ctor_set(v_reuseFailAlloc_2474_, 19, v_keywords_2455_);
lean_ctor_set(v_reuseFailAlloc_2474_, 20, v_homepage_2456_);
lean_ctor_set(v_reuseFailAlloc_2474_, 21, v_license_2457_);
lean_ctor_set(v_reuseFailAlloc_2474_, 22, v_licenseFiles_2458_);
lean_ctor_set(v_reuseFailAlloc_2474_, 23, v_readmeFile_2459_);
lean_ctor_set(v_reuseFailAlloc_2474_, 24, v_enableArtifactCache_x3f_2461_);
lean_ctor_set(v_reuseFailAlloc_2474_, 25, v_restoreAllArtifacts_x3f_2462_);
lean_ctor_set(v_reuseFailAlloc_2474_, 26, v_builtinLint_x3f_2465_);
lean_ctor_set(v_reuseFailAlloc_2474_, 27, v_checks_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2474_, sizeof(void*)*28, v_bootstrap_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2474_, sizeof(void*)*28 + 1, v_precompileModules_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2474_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2474_, sizeof(void*)*28 + 3, v_reservoir_2460_);
lean_ctor_set_uint8(v_reuseFailAlloc_2474_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2463_);
lean_ctor_set_uint8(v_reuseFailAlloc_2474_, sizeof(void*)*28 + 5, v_allowImportAll_2464_);
lean_ctor_set_uint8(v_reuseFailAlloc_2474_, sizeof(void*)*28 + 6, v_fixedToolchain_2467_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__3(lean_object* v_x_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lake_defaultVersionTags;
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__3___boxed(lean_object* v_x_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lake_PackageConfig_versionTags___proj___redArg___lam__3(v_x_2478_);
lean_dec_ref(v_x_2478_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg(){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = ((lean_object*)(l_Lake_PackageConfig_versionTags___proj___redArg___closed__4));
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___boxed(lean_object* v___dummy_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lake_PackageConfig_versionTags___proj___redArg();
return v_res_2492_;
}
}
static lean_object* _init_l_Lake_PackageConfig_versionTags___proj___closed__0(void){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lake_PackageConfig_versionTags___proj___redArg();
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object* v_p_2494_, lean_object* v_n_2495_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = lean_obj_once(&l_Lake_PackageConfig_versionTags___proj___closed__0, &l_Lake_PackageConfig_versionTags___proj___closed__0_once, _init_l_Lake_PackageConfig_versionTags___proj___closed__0);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object* v_p_2497_, lean_object* v_n_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lake_PackageConfig_versionTags___proj(v_p_2497_, v_n_2498_);
lean_dec(v_n_2498_);
lean_dec(v_p_2497_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___redArg(){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_obj_once(&l_Lake_PackageConfig_versionTags___proj___closed__0, &l_Lake_PackageConfig_versionTags___proj___closed__0_once, _init_l_Lake_PackageConfig_versionTags___proj___closed__0);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___redArg___boxed(lean_object* v___dummy_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lake_PackageConfig_versionTags_instConfigField___redArg();
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object* v_p_2504_, lean_object* v_n_2505_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_obj_once(&l_Lake_PackageConfig_versionTags___proj___closed__0, &l_Lake_PackageConfig_versionTags___proj___closed__0_once, _init_l_Lake_PackageConfig_versionTags___proj___closed__0);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object* v_p_2507_, lean_object* v_n_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lake_PackageConfig_versionTags_instConfigField(v_p_2507_, v_n_2508_);
lean_dec(v_n_2508_);
lean_dec(v_p_2507_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__0(lean_object* v_cfg_2510_){
_start:
{
lean_object* v_description_2511_; 
v_description_2511_ = lean_ctor_get(v_cfg_2510_, 18);
lean_inc_ref(v_description_2511_);
return v_description_2511_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__0___boxed(lean_object* v_cfg_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lake_PackageConfig_description___proj___redArg___lam__0(v_cfg_2512_);
lean_dec_ref(v_cfg_2512_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__1(lean_object* v_val_2514_, lean_object* v_cfg_2515_){
_start:
{
lean_object* v_toWorkspaceConfig_2516_; lean_object* v_toLeanConfig_2517_; uint8_t v_bootstrap_2518_; lean_object* v_extraDepTargets_2519_; uint8_t v_precompileModules_2520_; lean_object* v_moreGlobalServerArgs_2521_; lean_object* v_srcDir_2522_; lean_object* v_buildDir_2523_; lean_object* v_leanLibDir_2524_; lean_object* v_nativeLibDir_2525_; lean_object* v_binDir_2526_; lean_object* v_irDir_2527_; lean_object* v_releaseRepo_2528_; lean_object* v_buildArchive_2529_; uint8_t v_preferReleaseBuild_2530_; lean_object* v_testDriver_2531_; lean_object* v_testDriverArgs_2532_; lean_object* v_lintDriver_2533_; lean_object* v_lintDriverArgs_2534_; lean_object* v_version_2535_; lean_object* v_versionTags_2536_; lean_object* v_keywords_2537_; lean_object* v_homepage_2538_; lean_object* v_license_2539_; lean_object* v_licenseFiles_2540_; lean_object* v_readmeFile_2541_; uint8_t v_reservoir_2542_; lean_object* v_enableArtifactCache_x3f_2543_; lean_object* v_restoreAllArtifacts_x3f_2544_; uint8_t v_libPrefixOnWindows_2545_; uint8_t v_allowImportAll_2546_; lean_object* v_builtinLint_x3f_2547_; lean_object* v_checks_2548_; uint8_t v_fixedToolchain_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_toWorkspaceConfig_2516_ = lean_ctor_get(v_cfg_2515_, 0);
v_toLeanConfig_2517_ = lean_ctor_get(v_cfg_2515_, 1);
v_bootstrap_2518_ = lean_ctor_get_uint8(v_cfg_2515_, sizeof(void*)*28);
v_extraDepTargets_2519_ = lean_ctor_get(v_cfg_2515_, 2);
v_precompileModules_2520_ = lean_ctor_get_uint8(v_cfg_2515_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2521_ = lean_ctor_get(v_cfg_2515_, 3);
v_srcDir_2522_ = lean_ctor_get(v_cfg_2515_, 4);
v_buildDir_2523_ = lean_ctor_get(v_cfg_2515_, 5);
v_leanLibDir_2524_ = lean_ctor_get(v_cfg_2515_, 6);
v_nativeLibDir_2525_ = lean_ctor_get(v_cfg_2515_, 7);
v_binDir_2526_ = lean_ctor_get(v_cfg_2515_, 8);
v_irDir_2527_ = lean_ctor_get(v_cfg_2515_, 9);
v_releaseRepo_2528_ = lean_ctor_get(v_cfg_2515_, 10);
v_buildArchive_2529_ = lean_ctor_get(v_cfg_2515_, 11);
v_preferReleaseBuild_2530_ = lean_ctor_get_uint8(v_cfg_2515_, sizeof(void*)*28 + 2);
v_testDriver_2531_ = lean_ctor_get(v_cfg_2515_, 12);
v_testDriverArgs_2532_ = lean_ctor_get(v_cfg_2515_, 13);
v_lintDriver_2533_ = lean_ctor_get(v_cfg_2515_, 14);
v_lintDriverArgs_2534_ = lean_ctor_get(v_cfg_2515_, 15);
v_version_2535_ = lean_ctor_get(v_cfg_2515_, 16);
v_versionTags_2536_ = lean_ctor_get(v_cfg_2515_, 17);
v_keywords_2537_ = lean_ctor_get(v_cfg_2515_, 19);
v_homepage_2538_ = lean_ctor_get(v_cfg_2515_, 20);
v_license_2539_ = lean_ctor_get(v_cfg_2515_, 21);
v_licenseFiles_2540_ = lean_ctor_get(v_cfg_2515_, 22);
v_readmeFile_2541_ = lean_ctor_get(v_cfg_2515_, 23);
v_reservoir_2542_ = lean_ctor_get_uint8(v_cfg_2515_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2543_ = lean_ctor_get(v_cfg_2515_, 24);
v_restoreAllArtifacts_x3f_2544_ = lean_ctor_get(v_cfg_2515_, 25);
v_libPrefixOnWindows_2545_ = lean_ctor_get_uint8(v_cfg_2515_, sizeof(void*)*28 + 4);
v_allowImportAll_2546_ = lean_ctor_get_uint8(v_cfg_2515_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2547_ = lean_ctor_get(v_cfg_2515_, 26);
v_checks_2548_ = lean_ctor_get(v_cfg_2515_, 27);
v_fixedToolchain_2549_ = lean_ctor_get_uint8(v_cfg_2515_, sizeof(void*)*28 + 6);
v_isSharedCheck_2556_ = !lean_is_exclusive(v_cfg_2515_);
if (v_isSharedCheck_2556_ == 0)
{
lean_object* v_unused_2557_; 
v_unused_2557_ = lean_ctor_get(v_cfg_2515_, 18);
lean_dec(v_unused_2557_);
v___x_2551_ = v_cfg_2515_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_checks_2548_);
lean_inc(v_builtinLint_x3f_2547_);
lean_inc(v_restoreAllArtifacts_x3f_2544_);
lean_inc(v_enableArtifactCache_x3f_2543_);
lean_inc(v_readmeFile_2541_);
lean_inc(v_licenseFiles_2540_);
lean_inc(v_license_2539_);
lean_inc(v_homepage_2538_);
lean_inc(v_keywords_2537_);
lean_inc(v_versionTags_2536_);
lean_inc(v_version_2535_);
lean_inc(v_lintDriverArgs_2534_);
lean_inc(v_lintDriver_2533_);
lean_inc(v_testDriverArgs_2532_);
lean_inc(v_testDriver_2531_);
lean_inc(v_buildArchive_2529_);
lean_inc(v_releaseRepo_2528_);
lean_inc(v_irDir_2527_);
lean_inc(v_binDir_2526_);
lean_inc(v_nativeLibDir_2525_);
lean_inc(v_leanLibDir_2524_);
lean_inc(v_buildDir_2523_);
lean_inc(v_srcDir_2522_);
lean_inc(v_moreGlobalServerArgs_2521_);
lean_inc(v_extraDepTargets_2519_);
lean_inc(v_toLeanConfig_2517_);
lean_inc(v_toWorkspaceConfig_2516_);
lean_dec(v_cfg_2515_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 18, v_val_2514_);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_toWorkspaceConfig_2516_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_toLeanConfig_2517_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_extraDepTargets_2519_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_moreGlobalServerArgs_2521_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v_srcDir_2522_);
lean_ctor_set(v_reuseFailAlloc_2555_, 5, v_buildDir_2523_);
lean_ctor_set(v_reuseFailAlloc_2555_, 6, v_leanLibDir_2524_);
lean_ctor_set(v_reuseFailAlloc_2555_, 7, v_nativeLibDir_2525_);
lean_ctor_set(v_reuseFailAlloc_2555_, 8, v_binDir_2526_);
lean_ctor_set(v_reuseFailAlloc_2555_, 9, v_irDir_2527_);
lean_ctor_set(v_reuseFailAlloc_2555_, 10, v_releaseRepo_2528_);
lean_ctor_set(v_reuseFailAlloc_2555_, 11, v_buildArchive_2529_);
lean_ctor_set(v_reuseFailAlloc_2555_, 12, v_testDriver_2531_);
lean_ctor_set(v_reuseFailAlloc_2555_, 13, v_testDriverArgs_2532_);
lean_ctor_set(v_reuseFailAlloc_2555_, 14, v_lintDriver_2533_);
lean_ctor_set(v_reuseFailAlloc_2555_, 15, v_lintDriverArgs_2534_);
lean_ctor_set(v_reuseFailAlloc_2555_, 16, v_version_2535_);
lean_ctor_set(v_reuseFailAlloc_2555_, 17, v_versionTags_2536_);
lean_ctor_set(v_reuseFailAlloc_2555_, 18, v_val_2514_);
lean_ctor_set(v_reuseFailAlloc_2555_, 19, v_keywords_2537_);
lean_ctor_set(v_reuseFailAlloc_2555_, 20, v_homepage_2538_);
lean_ctor_set(v_reuseFailAlloc_2555_, 21, v_license_2539_);
lean_ctor_set(v_reuseFailAlloc_2555_, 22, v_licenseFiles_2540_);
lean_ctor_set(v_reuseFailAlloc_2555_, 23, v_readmeFile_2541_);
lean_ctor_set(v_reuseFailAlloc_2555_, 24, v_enableArtifactCache_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2555_, 25, v_restoreAllArtifacts_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2555_, 26, v_builtinLint_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2555_, 27, v_checks_2548_);
lean_ctor_set_uint8(v_reuseFailAlloc_2555_, sizeof(void*)*28, v_bootstrap_2518_);
lean_ctor_set_uint8(v_reuseFailAlloc_2555_, sizeof(void*)*28 + 1, v_precompileModules_2520_);
lean_ctor_set_uint8(v_reuseFailAlloc_2555_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2530_);
lean_ctor_set_uint8(v_reuseFailAlloc_2555_, sizeof(void*)*28 + 3, v_reservoir_2542_);
lean_ctor_set_uint8(v_reuseFailAlloc_2555_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2545_);
lean_ctor_set_uint8(v_reuseFailAlloc_2555_, sizeof(void*)*28 + 5, v_allowImportAll_2546_);
lean_ctor_set_uint8(v_reuseFailAlloc_2555_, sizeof(void*)*28 + 6, v_fixedToolchain_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__2(lean_object* v_f_2558_, lean_object* v_cfg_2559_){
_start:
{
lean_object* v_toWorkspaceConfig_2560_; lean_object* v_toLeanConfig_2561_; uint8_t v_bootstrap_2562_; lean_object* v_extraDepTargets_2563_; uint8_t v_precompileModules_2564_; lean_object* v_moreGlobalServerArgs_2565_; lean_object* v_srcDir_2566_; lean_object* v_buildDir_2567_; lean_object* v_leanLibDir_2568_; lean_object* v_nativeLibDir_2569_; lean_object* v_binDir_2570_; lean_object* v_irDir_2571_; lean_object* v_releaseRepo_2572_; lean_object* v_buildArchive_2573_; uint8_t v_preferReleaseBuild_2574_; lean_object* v_testDriver_2575_; lean_object* v_testDriverArgs_2576_; lean_object* v_lintDriver_2577_; lean_object* v_lintDriverArgs_2578_; lean_object* v_version_2579_; lean_object* v_versionTags_2580_; lean_object* v_description_2581_; lean_object* v_keywords_2582_; lean_object* v_homepage_2583_; lean_object* v_license_2584_; lean_object* v_licenseFiles_2585_; lean_object* v_readmeFile_2586_; uint8_t v_reservoir_2587_; lean_object* v_enableArtifactCache_x3f_2588_; lean_object* v_restoreAllArtifacts_x3f_2589_; uint8_t v_libPrefixOnWindows_2590_; uint8_t v_allowImportAll_2591_; lean_object* v_builtinLint_x3f_2592_; lean_object* v_checks_2593_; uint8_t v_fixedToolchain_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2602_; 
v_toWorkspaceConfig_2560_ = lean_ctor_get(v_cfg_2559_, 0);
v_toLeanConfig_2561_ = lean_ctor_get(v_cfg_2559_, 1);
v_bootstrap_2562_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*28);
v_extraDepTargets_2563_ = lean_ctor_get(v_cfg_2559_, 2);
v_precompileModules_2564_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2565_ = lean_ctor_get(v_cfg_2559_, 3);
v_srcDir_2566_ = lean_ctor_get(v_cfg_2559_, 4);
v_buildDir_2567_ = lean_ctor_get(v_cfg_2559_, 5);
v_leanLibDir_2568_ = lean_ctor_get(v_cfg_2559_, 6);
v_nativeLibDir_2569_ = lean_ctor_get(v_cfg_2559_, 7);
v_binDir_2570_ = lean_ctor_get(v_cfg_2559_, 8);
v_irDir_2571_ = lean_ctor_get(v_cfg_2559_, 9);
v_releaseRepo_2572_ = lean_ctor_get(v_cfg_2559_, 10);
v_buildArchive_2573_ = lean_ctor_get(v_cfg_2559_, 11);
v_preferReleaseBuild_2574_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*28 + 2);
v_testDriver_2575_ = lean_ctor_get(v_cfg_2559_, 12);
v_testDriverArgs_2576_ = lean_ctor_get(v_cfg_2559_, 13);
v_lintDriver_2577_ = lean_ctor_get(v_cfg_2559_, 14);
v_lintDriverArgs_2578_ = lean_ctor_get(v_cfg_2559_, 15);
v_version_2579_ = lean_ctor_get(v_cfg_2559_, 16);
v_versionTags_2580_ = lean_ctor_get(v_cfg_2559_, 17);
v_description_2581_ = lean_ctor_get(v_cfg_2559_, 18);
v_keywords_2582_ = lean_ctor_get(v_cfg_2559_, 19);
v_homepage_2583_ = lean_ctor_get(v_cfg_2559_, 20);
v_license_2584_ = lean_ctor_get(v_cfg_2559_, 21);
v_licenseFiles_2585_ = lean_ctor_get(v_cfg_2559_, 22);
v_readmeFile_2586_ = lean_ctor_get(v_cfg_2559_, 23);
v_reservoir_2587_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2588_ = lean_ctor_get(v_cfg_2559_, 24);
v_restoreAllArtifacts_x3f_2589_ = lean_ctor_get(v_cfg_2559_, 25);
v_libPrefixOnWindows_2590_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*28 + 4);
v_allowImportAll_2591_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2592_ = lean_ctor_get(v_cfg_2559_, 26);
v_checks_2593_ = lean_ctor_get(v_cfg_2559_, 27);
v_fixedToolchain_2594_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*28 + 6);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_cfg_2559_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2596_ = v_cfg_2559_;
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_checks_2593_);
lean_inc(v_builtinLint_x3f_2592_);
lean_inc(v_restoreAllArtifacts_x3f_2589_);
lean_inc(v_enableArtifactCache_x3f_2588_);
lean_inc(v_readmeFile_2586_);
lean_inc(v_licenseFiles_2585_);
lean_inc(v_license_2584_);
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
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2598_ = lean_apply_1(v_f_2558_, v_description_2581_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 18, v___x_2598_);
v___x_2600_ = v___x_2596_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_toWorkspaceConfig_2560_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_toLeanConfig_2561_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_extraDepTargets_2563_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_moreGlobalServerArgs_2565_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_srcDir_2566_);
lean_ctor_set(v_reuseFailAlloc_2601_, 5, v_buildDir_2567_);
lean_ctor_set(v_reuseFailAlloc_2601_, 6, v_leanLibDir_2568_);
lean_ctor_set(v_reuseFailAlloc_2601_, 7, v_nativeLibDir_2569_);
lean_ctor_set(v_reuseFailAlloc_2601_, 8, v_binDir_2570_);
lean_ctor_set(v_reuseFailAlloc_2601_, 9, v_irDir_2571_);
lean_ctor_set(v_reuseFailAlloc_2601_, 10, v_releaseRepo_2572_);
lean_ctor_set(v_reuseFailAlloc_2601_, 11, v_buildArchive_2573_);
lean_ctor_set(v_reuseFailAlloc_2601_, 12, v_testDriver_2575_);
lean_ctor_set(v_reuseFailAlloc_2601_, 13, v_testDriverArgs_2576_);
lean_ctor_set(v_reuseFailAlloc_2601_, 14, v_lintDriver_2577_);
lean_ctor_set(v_reuseFailAlloc_2601_, 15, v_lintDriverArgs_2578_);
lean_ctor_set(v_reuseFailAlloc_2601_, 16, v_version_2579_);
lean_ctor_set(v_reuseFailAlloc_2601_, 17, v_versionTags_2580_);
lean_ctor_set(v_reuseFailAlloc_2601_, 18, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2601_, 19, v_keywords_2582_);
lean_ctor_set(v_reuseFailAlloc_2601_, 20, v_homepage_2583_);
lean_ctor_set(v_reuseFailAlloc_2601_, 21, v_license_2584_);
lean_ctor_set(v_reuseFailAlloc_2601_, 22, v_licenseFiles_2585_);
lean_ctor_set(v_reuseFailAlloc_2601_, 23, v_readmeFile_2586_);
lean_ctor_set(v_reuseFailAlloc_2601_, 24, v_enableArtifactCache_x3f_2588_);
lean_ctor_set(v_reuseFailAlloc_2601_, 25, v_restoreAllArtifacts_x3f_2589_);
lean_ctor_set(v_reuseFailAlloc_2601_, 26, v_builtinLint_x3f_2592_);
lean_ctor_set(v_reuseFailAlloc_2601_, 27, v_checks_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*28, v_bootstrap_2562_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*28 + 1, v_precompileModules_2564_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2574_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*28 + 3, v_reservoir_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*28 + 5, v_allowImportAll_2591_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*28 + 6, v_fixedToolchain_2594_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg(){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = ((lean_object*)(l_Lake_PackageConfig_description___proj___redArg___closed__3));
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___boxed(lean_object* v___dummy_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lake_PackageConfig_description___proj___redArg();
return v_res_2614_;
}
}
static lean_object* _init_l_Lake_PackageConfig_description___proj___closed__0(void){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lake_PackageConfig_description___proj___redArg();
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object* v_p_2616_, lean_object* v_n_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_obj_once(&l_Lake_PackageConfig_description___proj___closed__0, &l_Lake_PackageConfig_description___proj___closed__0_once, _init_l_Lake_PackageConfig_description___proj___closed__0);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object* v_p_2619_, lean_object* v_n_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lake_PackageConfig_description___proj(v_p_2619_, v_n_2620_);
lean_dec(v_n_2620_);
lean_dec(v_p_2619_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___redArg(){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = lean_obj_once(&l_Lake_PackageConfig_description___proj___closed__0, &l_Lake_PackageConfig_description___proj___closed__0_once, _init_l_Lake_PackageConfig_description___proj___closed__0);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___redArg___boxed(lean_object* v___dummy_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lake_PackageConfig_description_instConfigField___redArg();
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object* v_p_2626_, lean_object* v_n_2627_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = lean_obj_once(&l_Lake_PackageConfig_description___proj___closed__0, &l_Lake_PackageConfig_description___proj___closed__0_once, _init_l_Lake_PackageConfig_description___proj___closed__0);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object* v_p_2629_, lean_object* v_n_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lake_PackageConfig_description_instConfigField(v_p_2629_, v_n_2630_);
lean_dec(v_n_2630_);
lean_dec(v_p_2629_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__0(lean_object* v_cfg_2632_){
_start:
{
lean_object* v_keywords_2633_; 
v_keywords_2633_ = lean_ctor_get(v_cfg_2632_, 19);
lean_inc_ref(v_keywords_2633_);
return v_keywords_2633_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__0___boxed(lean_object* v_cfg_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lake_PackageConfig_keywords___proj___redArg___lam__0(v_cfg_2634_);
lean_dec_ref(v_cfg_2634_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__1(lean_object* v_val_2636_, lean_object* v_cfg_2637_){
_start:
{
lean_object* v_toWorkspaceConfig_2638_; lean_object* v_toLeanConfig_2639_; uint8_t v_bootstrap_2640_; lean_object* v_extraDepTargets_2641_; uint8_t v_precompileModules_2642_; lean_object* v_moreGlobalServerArgs_2643_; lean_object* v_srcDir_2644_; lean_object* v_buildDir_2645_; lean_object* v_leanLibDir_2646_; lean_object* v_nativeLibDir_2647_; lean_object* v_binDir_2648_; lean_object* v_irDir_2649_; lean_object* v_releaseRepo_2650_; lean_object* v_buildArchive_2651_; uint8_t v_preferReleaseBuild_2652_; lean_object* v_testDriver_2653_; lean_object* v_testDriverArgs_2654_; lean_object* v_lintDriver_2655_; lean_object* v_lintDriverArgs_2656_; lean_object* v_version_2657_; lean_object* v_versionTags_2658_; lean_object* v_description_2659_; lean_object* v_homepage_2660_; lean_object* v_license_2661_; lean_object* v_licenseFiles_2662_; lean_object* v_readmeFile_2663_; uint8_t v_reservoir_2664_; lean_object* v_enableArtifactCache_x3f_2665_; lean_object* v_restoreAllArtifacts_x3f_2666_; uint8_t v_libPrefixOnWindows_2667_; uint8_t v_allowImportAll_2668_; lean_object* v_builtinLint_x3f_2669_; lean_object* v_checks_2670_; uint8_t v_fixedToolchain_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
v_toWorkspaceConfig_2638_ = lean_ctor_get(v_cfg_2637_, 0);
v_toLeanConfig_2639_ = lean_ctor_get(v_cfg_2637_, 1);
v_bootstrap_2640_ = lean_ctor_get_uint8(v_cfg_2637_, sizeof(void*)*28);
v_extraDepTargets_2641_ = lean_ctor_get(v_cfg_2637_, 2);
v_precompileModules_2642_ = lean_ctor_get_uint8(v_cfg_2637_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2643_ = lean_ctor_get(v_cfg_2637_, 3);
v_srcDir_2644_ = lean_ctor_get(v_cfg_2637_, 4);
v_buildDir_2645_ = lean_ctor_get(v_cfg_2637_, 5);
v_leanLibDir_2646_ = lean_ctor_get(v_cfg_2637_, 6);
v_nativeLibDir_2647_ = lean_ctor_get(v_cfg_2637_, 7);
v_binDir_2648_ = lean_ctor_get(v_cfg_2637_, 8);
v_irDir_2649_ = lean_ctor_get(v_cfg_2637_, 9);
v_releaseRepo_2650_ = lean_ctor_get(v_cfg_2637_, 10);
v_buildArchive_2651_ = lean_ctor_get(v_cfg_2637_, 11);
v_preferReleaseBuild_2652_ = lean_ctor_get_uint8(v_cfg_2637_, sizeof(void*)*28 + 2);
v_testDriver_2653_ = lean_ctor_get(v_cfg_2637_, 12);
v_testDriverArgs_2654_ = lean_ctor_get(v_cfg_2637_, 13);
v_lintDriver_2655_ = lean_ctor_get(v_cfg_2637_, 14);
v_lintDriverArgs_2656_ = lean_ctor_get(v_cfg_2637_, 15);
v_version_2657_ = lean_ctor_get(v_cfg_2637_, 16);
v_versionTags_2658_ = lean_ctor_get(v_cfg_2637_, 17);
v_description_2659_ = lean_ctor_get(v_cfg_2637_, 18);
v_homepage_2660_ = lean_ctor_get(v_cfg_2637_, 20);
v_license_2661_ = lean_ctor_get(v_cfg_2637_, 21);
v_licenseFiles_2662_ = lean_ctor_get(v_cfg_2637_, 22);
v_readmeFile_2663_ = lean_ctor_get(v_cfg_2637_, 23);
v_reservoir_2664_ = lean_ctor_get_uint8(v_cfg_2637_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2665_ = lean_ctor_get(v_cfg_2637_, 24);
v_restoreAllArtifacts_x3f_2666_ = lean_ctor_get(v_cfg_2637_, 25);
v_libPrefixOnWindows_2667_ = lean_ctor_get_uint8(v_cfg_2637_, sizeof(void*)*28 + 4);
v_allowImportAll_2668_ = lean_ctor_get_uint8(v_cfg_2637_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2669_ = lean_ctor_get(v_cfg_2637_, 26);
v_checks_2670_ = lean_ctor_get(v_cfg_2637_, 27);
v_fixedToolchain_2671_ = lean_ctor_get_uint8(v_cfg_2637_, sizeof(void*)*28 + 6);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_cfg_2637_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v_cfg_2637_, 19);
lean_dec(v_unused_2679_);
v___x_2673_ = v_cfg_2637_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_checks_2670_);
lean_inc(v_builtinLint_x3f_2669_);
lean_inc(v_restoreAllArtifacts_x3f_2666_);
lean_inc(v_enableArtifactCache_x3f_2665_);
lean_inc(v_readmeFile_2663_);
lean_inc(v_licenseFiles_2662_);
lean_inc(v_license_2661_);
lean_inc(v_homepage_2660_);
lean_inc(v_description_2659_);
lean_inc(v_versionTags_2658_);
lean_inc(v_version_2657_);
lean_inc(v_lintDriverArgs_2656_);
lean_inc(v_lintDriver_2655_);
lean_inc(v_testDriverArgs_2654_);
lean_inc(v_testDriver_2653_);
lean_inc(v_buildArchive_2651_);
lean_inc(v_releaseRepo_2650_);
lean_inc(v_irDir_2649_);
lean_inc(v_binDir_2648_);
lean_inc(v_nativeLibDir_2647_);
lean_inc(v_leanLibDir_2646_);
lean_inc(v_buildDir_2645_);
lean_inc(v_srcDir_2644_);
lean_inc(v_moreGlobalServerArgs_2643_);
lean_inc(v_extraDepTargets_2641_);
lean_inc(v_toLeanConfig_2639_);
lean_inc(v_toWorkspaceConfig_2638_);
lean_dec(v_cfg_2637_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 19, v_val_2636_);
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_toWorkspaceConfig_2638_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_toLeanConfig_2639_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_extraDepTargets_2641_);
lean_ctor_set(v_reuseFailAlloc_2677_, 3, v_moreGlobalServerArgs_2643_);
lean_ctor_set(v_reuseFailAlloc_2677_, 4, v_srcDir_2644_);
lean_ctor_set(v_reuseFailAlloc_2677_, 5, v_buildDir_2645_);
lean_ctor_set(v_reuseFailAlloc_2677_, 6, v_leanLibDir_2646_);
lean_ctor_set(v_reuseFailAlloc_2677_, 7, v_nativeLibDir_2647_);
lean_ctor_set(v_reuseFailAlloc_2677_, 8, v_binDir_2648_);
lean_ctor_set(v_reuseFailAlloc_2677_, 9, v_irDir_2649_);
lean_ctor_set(v_reuseFailAlloc_2677_, 10, v_releaseRepo_2650_);
lean_ctor_set(v_reuseFailAlloc_2677_, 11, v_buildArchive_2651_);
lean_ctor_set(v_reuseFailAlloc_2677_, 12, v_testDriver_2653_);
lean_ctor_set(v_reuseFailAlloc_2677_, 13, v_testDriverArgs_2654_);
lean_ctor_set(v_reuseFailAlloc_2677_, 14, v_lintDriver_2655_);
lean_ctor_set(v_reuseFailAlloc_2677_, 15, v_lintDriverArgs_2656_);
lean_ctor_set(v_reuseFailAlloc_2677_, 16, v_version_2657_);
lean_ctor_set(v_reuseFailAlloc_2677_, 17, v_versionTags_2658_);
lean_ctor_set(v_reuseFailAlloc_2677_, 18, v_description_2659_);
lean_ctor_set(v_reuseFailAlloc_2677_, 19, v_val_2636_);
lean_ctor_set(v_reuseFailAlloc_2677_, 20, v_homepage_2660_);
lean_ctor_set(v_reuseFailAlloc_2677_, 21, v_license_2661_);
lean_ctor_set(v_reuseFailAlloc_2677_, 22, v_licenseFiles_2662_);
lean_ctor_set(v_reuseFailAlloc_2677_, 23, v_readmeFile_2663_);
lean_ctor_set(v_reuseFailAlloc_2677_, 24, v_enableArtifactCache_x3f_2665_);
lean_ctor_set(v_reuseFailAlloc_2677_, 25, v_restoreAllArtifacts_x3f_2666_);
lean_ctor_set(v_reuseFailAlloc_2677_, 26, v_builtinLint_x3f_2669_);
lean_ctor_set(v_reuseFailAlloc_2677_, 27, v_checks_2670_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, sizeof(void*)*28, v_bootstrap_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, sizeof(void*)*28 + 1, v_precompileModules_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, sizeof(void*)*28 + 3, v_reservoir_2664_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2667_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, sizeof(void*)*28 + 5, v_allowImportAll_2668_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, sizeof(void*)*28 + 6, v_fixedToolchain_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__2(lean_object* v_f_2680_, lean_object* v_cfg_2681_){
_start:
{
lean_object* v_toWorkspaceConfig_2682_; lean_object* v_toLeanConfig_2683_; uint8_t v_bootstrap_2684_; lean_object* v_extraDepTargets_2685_; uint8_t v_precompileModules_2686_; lean_object* v_moreGlobalServerArgs_2687_; lean_object* v_srcDir_2688_; lean_object* v_buildDir_2689_; lean_object* v_leanLibDir_2690_; lean_object* v_nativeLibDir_2691_; lean_object* v_binDir_2692_; lean_object* v_irDir_2693_; lean_object* v_releaseRepo_2694_; lean_object* v_buildArchive_2695_; uint8_t v_preferReleaseBuild_2696_; lean_object* v_testDriver_2697_; lean_object* v_testDriverArgs_2698_; lean_object* v_lintDriver_2699_; lean_object* v_lintDriverArgs_2700_; lean_object* v_version_2701_; lean_object* v_versionTags_2702_; lean_object* v_description_2703_; lean_object* v_keywords_2704_; lean_object* v_homepage_2705_; lean_object* v_license_2706_; lean_object* v_licenseFiles_2707_; lean_object* v_readmeFile_2708_; uint8_t v_reservoir_2709_; lean_object* v_enableArtifactCache_x3f_2710_; lean_object* v_restoreAllArtifacts_x3f_2711_; uint8_t v_libPrefixOnWindows_2712_; uint8_t v_allowImportAll_2713_; lean_object* v_builtinLint_x3f_2714_; lean_object* v_checks_2715_; uint8_t v_fixedToolchain_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2724_; 
v_toWorkspaceConfig_2682_ = lean_ctor_get(v_cfg_2681_, 0);
v_toLeanConfig_2683_ = lean_ctor_get(v_cfg_2681_, 1);
v_bootstrap_2684_ = lean_ctor_get_uint8(v_cfg_2681_, sizeof(void*)*28);
v_extraDepTargets_2685_ = lean_ctor_get(v_cfg_2681_, 2);
v_precompileModules_2686_ = lean_ctor_get_uint8(v_cfg_2681_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2687_ = lean_ctor_get(v_cfg_2681_, 3);
v_srcDir_2688_ = lean_ctor_get(v_cfg_2681_, 4);
v_buildDir_2689_ = lean_ctor_get(v_cfg_2681_, 5);
v_leanLibDir_2690_ = lean_ctor_get(v_cfg_2681_, 6);
v_nativeLibDir_2691_ = lean_ctor_get(v_cfg_2681_, 7);
v_binDir_2692_ = lean_ctor_get(v_cfg_2681_, 8);
v_irDir_2693_ = lean_ctor_get(v_cfg_2681_, 9);
v_releaseRepo_2694_ = lean_ctor_get(v_cfg_2681_, 10);
v_buildArchive_2695_ = lean_ctor_get(v_cfg_2681_, 11);
v_preferReleaseBuild_2696_ = lean_ctor_get_uint8(v_cfg_2681_, sizeof(void*)*28 + 2);
v_testDriver_2697_ = lean_ctor_get(v_cfg_2681_, 12);
v_testDriverArgs_2698_ = lean_ctor_get(v_cfg_2681_, 13);
v_lintDriver_2699_ = lean_ctor_get(v_cfg_2681_, 14);
v_lintDriverArgs_2700_ = lean_ctor_get(v_cfg_2681_, 15);
v_version_2701_ = lean_ctor_get(v_cfg_2681_, 16);
v_versionTags_2702_ = lean_ctor_get(v_cfg_2681_, 17);
v_description_2703_ = lean_ctor_get(v_cfg_2681_, 18);
v_keywords_2704_ = lean_ctor_get(v_cfg_2681_, 19);
v_homepage_2705_ = lean_ctor_get(v_cfg_2681_, 20);
v_license_2706_ = lean_ctor_get(v_cfg_2681_, 21);
v_licenseFiles_2707_ = lean_ctor_get(v_cfg_2681_, 22);
v_readmeFile_2708_ = lean_ctor_get(v_cfg_2681_, 23);
v_reservoir_2709_ = lean_ctor_get_uint8(v_cfg_2681_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2710_ = lean_ctor_get(v_cfg_2681_, 24);
v_restoreAllArtifacts_x3f_2711_ = lean_ctor_get(v_cfg_2681_, 25);
v_libPrefixOnWindows_2712_ = lean_ctor_get_uint8(v_cfg_2681_, sizeof(void*)*28 + 4);
v_allowImportAll_2713_ = lean_ctor_get_uint8(v_cfg_2681_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2714_ = lean_ctor_get(v_cfg_2681_, 26);
v_checks_2715_ = lean_ctor_get(v_cfg_2681_, 27);
v_fixedToolchain_2716_ = lean_ctor_get_uint8(v_cfg_2681_, sizeof(void*)*28 + 6);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_cfg_2681_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2718_ = v_cfg_2681_;
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_checks_2715_);
lean_inc(v_builtinLint_x3f_2714_);
lean_inc(v_restoreAllArtifacts_x3f_2711_);
lean_inc(v_enableArtifactCache_x3f_2710_);
lean_inc(v_readmeFile_2708_);
lean_inc(v_licenseFiles_2707_);
lean_inc(v_license_2706_);
lean_inc(v_homepage_2705_);
lean_inc(v_keywords_2704_);
lean_inc(v_description_2703_);
lean_inc(v_versionTags_2702_);
lean_inc(v_version_2701_);
lean_inc(v_lintDriverArgs_2700_);
lean_inc(v_lintDriver_2699_);
lean_inc(v_testDriverArgs_2698_);
lean_inc(v_testDriver_2697_);
lean_inc(v_buildArchive_2695_);
lean_inc(v_releaseRepo_2694_);
lean_inc(v_irDir_2693_);
lean_inc(v_binDir_2692_);
lean_inc(v_nativeLibDir_2691_);
lean_inc(v_leanLibDir_2690_);
lean_inc(v_buildDir_2689_);
lean_inc(v_srcDir_2688_);
lean_inc(v_moreGlobalServerArgs_2687_);
lean_inc(v_extraDepTargets_2685_);
lean_inc(v_toLeanConfig_2683_);
lean_inc(v_toWorkspaceConfig_2682_);
lean_dec(v_cfg_2681_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2720_ = lean_apply_1(v_f_2680_, v_keywords_2704_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 19, v___x_2720_);
v___x_2722_ = v___x_2718_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_toWorkspaceConfig_2682_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v_toLeanConfig_2683_);
lean_ctor_set(v_reuseFailAlloc_2723_, 2, v_extraDepTargets_2685_);
lean_ctor_set(v_reuseFailAlloc_2723_, 3, v_moreGlobalServerArgs_2687_);
lean_ctor_set(v_reuseFailAlloc_2723_, 4, v_srcDir_2688_);
lean_ctor_set(v_reuseFailAlloc_2723_, 5, v_buildDir_2689_);
lean_ctor_set(v_reuseFailAlloc_2723_, 6, v_leanLibDir_2690_);
lean_ctor_set(v_reuseFailAlloc_2723_, 7, v_nativeLibDir_2691_);
lean_ctor_set(v_reuseFailAlloc_2723_, 8, v_binDir_2692_);
lean_ctor_set(v_reuseFailAlloc_2723_, 9, v_irDir_2693_);
lean_ctor_set(v_reuseFailAlloc_2723_, 10, v_releaseRepo_2694_);
lean_ctor_set(v_reuseFailAlloc_2723_, 11, v_buildArchive_2695_);
lean_ctor_set(v_reuseFailAlloc_2723_, 12, v_testDriver_2697_);
lean_ctor_set(v_reuseFailAlloc_2723_, 13, v_testDriverArgs_2698_);
lean_ctor_set(v_reuseFailAlloc_2723_, 14, v_lintDriver_2699_);
lean_ctor_set(v_reuseFailAlloc_2723_, 15, v_lintDriverArgs_2700_);
lean_ctor_set(v_reuseFailAlloc_2723_, 16, v_version_2701_);
lean_ctor_set(v_reuseFailAlloc_2723_, 17, v_versionTags_2702_);
lean_ctor_set(v_reuseFailAlloc_2723_, 18, v_description_2703_);
lean_ctor_set(v_reuseFailAlloc_2723_, 19, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2723_, 20, v_homepage_2705_);
lean_ctor_set(v_reuseFailAlloc_2723_, 21, v_license_2706_);
lean_ctor_set(v_reuseFailAlloc_2723_, 22, v_licenseFiles_2707_);
lean_ctor_set(v_reuseFailAlloc_2723_, 23, v_readmeFile_2708_);
lean_ctor_set(v_reuseFailAlloc_2723_, 24, v_enableArtifactCache_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2723_, 25, v_restoreAllArtifacts_x3f_2711_);
lean_ctor_set(v_reuseFailAlloc_2723_, 26, v_builtinLint_x3f_2714_);
lean_ctor_set(v_reuseFailAlloc_2723_, 27, v_checks_2715_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, sizeof(void*)*28, v_bootstrap_2684_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, sizeof(void*)*28 + 1, v_precompileModules_2686_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, sizeof(void*)*28 + 3, v_reservoir_2709_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2712_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, sizeof(void*)*28 + 5, v_allowImportAll_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, sizeof(void*)*28 + 6, v_fixedToolchain_2716_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg(){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = ((lean_object*)(l_Lake_PackageConfig_keywords___proj___redArg___closed__3));
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___boxed(lean_object* v___dummy_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lake_PackageConfig_keywords___proj___redArg();
return v_res_2736_;
}
}
static lean_object* _init_l_Lake_PackageConfig_keywords___proj___closed__0(void){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lake_PackageConfig_keywords___proj___redArg();
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object* v_p_2738_, lean_object* v_n_2739_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = lean_obj_once(&l_Lake_PackageConfig_keywords___proj___closed__0, &l_Lake_PackageConfig_keywords___proj___closed__0_once, _init_l_Lake_PackageConfig_keywords___proj___closed__0);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object* v_p_2741_, lean_object* v_n_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lake_PackageConfig_keywords___proj(v_p_2741_, v_n_2742_);
lean_dec(v_n_2742_);
lean_dec(v_p_2741_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___redArg(){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_obj_once(&l_Lake_PackageConfig_keywords___proj___closed__0, &l_Lake_PackageConfig_keywords___proj___closed__0_once, _init_l_Lake_PackageConfig_keywords___proj___closed__0);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___redArg___boxed(lean_object* v___dummy_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lake_PackageConfig_keywords_instConfigField___redArg();
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object* v_p_2748_, lean_object* v_n_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_obj_once(&l_Lake_PackageConfig_keywords___proj___closed__0, &l_Lake_PackageConfig_keywords___proj___closed__0_once, _init_l_Lake_PackageConfig_keywords___proj___closed__0);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object* v_p_2751_, lean_object* v_n_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lake_PackageConfig_keywords_instConfigField(v_p_2751_, v_n_2752_);
lean_dec(v_n_2752_);
lean_dec(v_p_2751_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__0(lean_object* v_cfg_2754_){
_start:
{
lean_object* v_homepage_2755_; 
v_homepage_2755_ = lean_ctor_get(v_cfg_2754_, 20);
lean_inc_ref(v_homepage_2755_);
return v_homepage_2755_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__0___boxed(lean_object* v_cfg_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lake_PackageConfig_homepage___proj___redArg___lam__0(v_cfg_2756_);
lean_dec_ref(v_cfg_2756_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__1(lean_object* v_val_2758_, lean_object* v_cfg_2759_){
_start:
{
lean_object* v_toWorkspaceConfig_2760_; lean_object* v_toLeanConfig_2761_; uint8_t v_bootstrap_2762_; lean_object* v_extraDepTargets_2763_; uint8_t v_precompileModules_2764_; lean_object* v_moreGlobalServerArgs_2765_; lean_object* v_srcDir_2766_; lean_object* v_buildDir_2767_; lean_object* v_leanLibDir_2768_; lean_object* v_nativeLibDir_2769_; lean_object* v_binDir_2770_; lean_object* v_irDir_2771_; lean_object* v_releaseRepo_2772_; lean_object* v_buildArchive_2773_; uint8_t v_preferReleaseBuild_2774_; lean_object* v_testDriver_2775_; lean_object* v_testDriverArgs_2776_; lean_object* v_lintDriver_2777_; lean_object* v_lintDriverArgs_2778_; lean_object* v_version_2779_; lean_object* v_versionTags_2780_; lean_object* v_description_2781_; lean_object* v_keywords_2782_; lean_object* v_license_2783_; lean_object* v_licenseFiles_2784_; lean_object* v_readmeFile_2785_; uint8_t v_reservoir_2786_; lean_object* v_enableArtifactCache_x3f_2787_; lean_object* v_restoreAllArtifacts_x3f_2788_; uint8_t v_libPrefixOnWindows_2789_; uint8_t v_allowImportAll_2790_; lean_object* v_builtinLint_x3f_2791_; lean_object* v_checks_2792_; uint8_t v_fixedToolchain_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_toWorkspaceConfig_2760_ = lean_ctor_get(v_cfg_2759_, 0);
v_toLeanConfig_2761_ = lean_ctor_get(v_cfg_2759_, 1);
v_bootstrap_2762_ = lean_ctor_get_uint8(v_cfg_2759_, sizeof(void*)*28);
v_extraDepTargets_2763_ = lean_ctor_get(v_cfg_2759_, 2);
v_precompileModules_2764_ = lean_ctor_get_uint8(v_cfg_2759_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2765_ = lean_ctor_get(v_cfg_2759_, 3);
v_srcDir_2766_ = lean_ctor_get(v_cfg_2759_, 4);
v_buildDir_2767_ = lean_ctor_get(v_cfg_2759_, 5);
v_leanLibDir_2768_ = lean_ctor_get(v_cfg_2759_, 6);
v_nativeLibDir_2769_ = lean_ctor_get(v_cfg_2759_, 7);
v_binDir_2770_ = lean_ctor_get(v_cfg_2759_, 8);
v_irDir_2771_ = lean_ctor_get(v_cfg_2759_, 9);
v_releaseRepo_2772_ = lean_ctor_get(v_cfg_2759_, 10);
v_buildArchive_2773_ = lean_ctor_get(v_cfg_2759_, 11);
v_preferReleaseBuild_2774_ = lean_ctor_get_uint8(v_cfg_2759_, sizeof(void*)*28 + 2);
v_testDriver_2775_ = lean_ctor_get(v_cfg_2759_, 12);
v_testDriverArgs_2776_ = lean_ctor_get(v_cfg_2759_, 13);
v_lintDriver_2777_ = lean_ctor_get(v_cfg_2759_, 14);
v_lintDriverArgs_2778_ = lean_ctor_get(v_cfg_2759_, 15);
v_version_2779_ = lean_ctor_get(v_cfg_2759_, 16);
v_versionTags_2780_ = lean_ctor_get(v_cfg_2759_, 17);
v_description_2781_ = lean_ctor_get(v_cfg_2759_, 18);
v_keywords_2782_ = lean_ctor_get(v_cfg_2759_, 19);
v_license_2783_ = lean_ctor_get(v_cfg_2759_, 21);
v_licenseFiles_2784_ = lean_ctor_get(v_cfg_2759_, 22);
v_readmeFile_2785_ = lean_ctor_get(v_cfg_2759_, 23);
v_reservoir_2786_ = lean_ctor_get_uint8(v_cfg_2759_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2787_ = lean_ctor_get(v_cfg_2759_, 24);
v_restoreAllArtifacts_x3f_2788_ = lean_ctor_get(v_cfg_2759_, 25);
v_libPrefixOnWindows_2789_ = lean_ctor_get_uint8(v_cfg_2759_, sizeof(void*)*28 + 4);
v_allowImportAll_2790_ = lean_ctor_get_uint8(v_cfg_2759_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2791_ = lean_ctor_get(v_cfg_2759_, 26);
v_checks_2792_ = lean_ctor_get(v_cfg_2759_, 27);
v_fixedToolchain_2793_ = lean_ctor_get_uint8(v_cfg_2759_, sizeof(void*)*28 + 6);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_cfg_2759_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; 
v_unused_2801_ = lean_ctor_get(v_cfg_2759_, 20);
lean_dec(v_unused_2801_);
v___x_2795_ = v_cfg_2759_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_checks_2792_);
lean_inc(v_builtinLint_x3f_2791_);
lean_inc(v_restoreAllArtifacts_x3f_2788_);
lean_inc(v_enableArtifactCache_x3f_2787_);
lean_inc(v_readmeFile_2785_);
lean_inc(v_licenseFiles_2784_);
lean_inc(v_license_2783_);
lean_inc(v_keywords_2782_);
lean_inc(v_description_2781_);
lean_inc(v_versionTags_2780_);
lean_inc(v_version_2779_);
lean_inc(v_lintDriverArgs_2778_);
lean_inc(v_lintDriver_2777_);
lean_inc(v_testDriverArgs_2776_);
lean_inc(v_testDriver_2775_);
lean_inc(v_buildArchive_2773_);
lean_inc(v_releaseRepo_2772_);
lean_inc(v_irDir_2771_);
lean_inc(v_binDir_2770_);
lean_inc(v_nativeLibDir_2769_);
lean_inc(v_leanLibDir_2768_);
lean_inc(v_buildDir_2767_);
lean_inc(v_srcDir_2766_);
lean_inc(v_moreGlobalServerArgs_2765_);
lean_inc(v_extraDepTargets_2763_);
lean_inc(v_toLeanConfig_2761_);
lean_inc(v_toWorkspaceConfig_2760_);
lean_dec(v_cfg_2759_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 20, v_val_2758_);
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_toWorkspaceConfig_2760_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_toLeanConfig_2761_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_extraDepTargets_2763_);
lean_ctor_set(v_reuseFailAlloc_2799_, 3, v_moreGlobalServerArgs_2765_);
lean_ctor_set(v_reuseFailAlloc_2799_, 4, v_srcDir_2766_);
lean_ctor_set(v_reuseFailAlloc_2799_, 5, v_buildDir_2767_);
lean_ctor_set(v_reuseFailAlloc_2799_, 6, v_leanLibDir_2768_);
lean_ctor_set(v_reuseFailAlloc_2799_, 7, v_nativeLibDir_2769_);
lean_ctor_set(v_reuseFailAlloc_2799_, 8, v_binDir_2770_);
lean_ctor_set(v_reuseFailAlloc_2799_, 9, v_irDir_2771_);
lean_ctor_set(v_reuseFailAlloc_2799_, 10, v_releaseRepo_2772_);
lean_ctor_set(v_reuseFailAlloc_2799_, 11, v_buildArchive_2773_);
lean_ctor_set(v_reuseFailAlloc_2799_, 12, v_testDriver_2775_);
lean_ctor_set(v_reuseFailAlloc_2799_, 13, v_testDriverArgs_2776_);
lean_ctor_set(v_reuseFailAlloc_2799_, 14, v_lintDriver_2777_);
lean_ctor_set(v_reuseFailAlloc_2799_, 15, v_lintDriverArgs_2778_);
lean_ctor_set(v_reuseFailAlloc_2799_, 16, v_version_2779_);
lean_ctor_set(v_reuseFailAlloc_2799_, 17, v_versionTags_2780_);
lean_ctor_set(v_reuseFailAlloc_2799_, 18, v_description_2781_);
lean_ctor_set(v_reuseFailAlloc_2799_, 19, v_keywords_2782_);
lean_ctor_set(v_reuseFailAlloc_2799_, 20, v_val_2758_);
lean_ctor_set(v_reuseFailAlloc_2799_, 21, v_license_2783_);
lean_ctor_set(v_reuseFailAlloc_2799_, 22, v_licenseFiles_2784_);
lean_ctor_set(v_reuseFailAlloc_2799_, 23, v_readmeFile_2785_);
lean_ctor_set(v_reuseFailAlloc_2799_, 24, v_enableArtifactCache_x3f_2787_);
lean_ctor_set(v_reuseFailAlloc_2799_, 25, v_restoreAllArtifacts_x3f_2788_);
lean_ctor_set(v_reuseFailAlloc_2799_, 26, v_builtinLint_x3f_2791_);
lean_ctor_set(v_reuseFailAlloc_2799_, 27, v_checks_2792_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*28, v_bootstrap_2762_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*28 + 1, v_precompileModules_2764_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2774_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*28 + 3, v_reservoir_2786_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2789_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*28 + 5, v_allowImportAll_2790_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*28 + 6, v_fixedToolchain_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__2(lean_object* v_f_2802_, lean_object* v_cfg_2803_){
_start:
{
lean_object* v_toWorkspaceConfig_2804_; lean_object* v_toLeanConfig_2805_; uint8_t v_bootstrap_2806_; lean_object* v_extraDepTargets_2807_; uint8_t v_precompileModules_2808_; lean_object* v_moreGlobalServerArgs_2809_; lean_object* v_srcDir_2810_; lean_object* v_buildDir_2811_; lean_object* v_leanLibDir_2812_; lean_object* v_nativeLibDir_2813_; lean_object* v_binDir_2814_; lean_object* v_irDir_2815_; lean_object* v_releaseRepo_2816_; lean_object* v_buildArchive_2817_; uint8_t v_preferReleaseBuild_2818_; lean_object* v_testDriver_2819_; lean_object* v_testDriverArgs_2820_; lean_object* v_lintDriver_2821_; lean_object* v_lintDriverArgs_2822_; lean_object* v_version_2823_; lean_object* v_versionTags_2824_; lean_object* v_description_2825_; lean_object* v_keywords_2826_; lean_object* v_homepage_2827_; lean_object* v_license_2828_; lean_object* v_licenseFiles_2829_; lean_object* v_readmeFile_2830_; uint8_t v_reservoir_2831_; lean_object* v_enableArtifactCache_x3f_2832_; lean_object* v_restoreAllArtifacts_x3f_2833_; uint8_t v_libPrefixOnWindows_2834_; uint8_t v_allowImportAll_2835_; lean_object* v_builtinLint_x3f_2836_; lean_object* v_checks_2837_; uint8_t v_fixedToolchain_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2846_; 
v_toWorkspaceConfig_2804_ = lean_ctor_get(v_cfg_2803_, 0);
v_toLeanConfig_2805_ = lean_ctor_get(v_cfg_2803_, 1);
v_bootstrap_2806_ = lean_ctor_get_uint8(v_cfg_2803_, sizeof(void*)*28);
v_extraDepTargets_2807_ = lean_ctor_get(v_cfg_2803_, 2);
v_precompileModules_2808_ = lean_ctor_get_uint8(v_cfg_2803_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2809_ = lean_ctor_get(v_cfg_2803_, 3);
v_srcDir_2810_ = lean_ctor_get(v_cfg_2803_, 4);
v_buildDir_2811_ = lean_ctor_get(v_cfg_2803_, 5);
v_leanLibDir_2812_ = lean_ctor_get(v_cfg_2803_, 6);
v_nativeLibDir_2813_ = lean_ctor_get(v_cfg_2803_, 7);
v_binDir_2814_ = lean_ctor_get(v_cfg_2803_, 8);
v_irDir_2815_ = lean_ctor_get(v_cfg_2803_, 9);
v_releaseRepo_2816_ = lean_ctor_get(v_cfg_2803_, 10);
v_buildArchive_2817_ = lean_ctor_get(v_cfg_2803_, 11);
v_preferReleaseBuild_2818_ = lean_ctor_get_uint8(v_cfg_2803_, sizeof(void*)*28 + 2);
v_testDriver_2819_ = lean_ctor_get(v_cfg_2803_, 12);
v_testDriverArgs_2820_ = lean_ctor_get(v_cfg_2803_, 13);
v_lintDriver_2821_ = lean_ctor_get(v_cfg_2803_, 14);
v_lintDriverArgs_2822_ = lean_ctor_get(v_cfg_2803_, 15);
v_version_2823_ = lean_ctor_get(v_cfg_2803_, 16);
v_versionTags_2824_ = lean_ctor_get(v_cfg_2803_, 17);
v_description_2825_ = lean_ctor_get(v_cfg_2803_, 18);
v_keywords_2826_ = lean_ctor_get(v_cfg_2803_, 19);
v_homepage_2827_ = lean_ctor_get(v_cfg_2803_, 20);
v_license_2828_ = lean_ctor_get(v_cfg_2803_, 21);
v_licenseFiles_2829_ = lean_ctor_get(v_cfg_2803_, 22);
v_readmeFile_2830_ = lean_ctor_get(v_cfg_2803_, 23);
v_reservoir_2831_ = lean_ctor_get_uint8(v_cfg_2803_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2832_ = lean_ctor_get(v_cfg_2803_, 24);
v_restoreAllArtifacts_x3f_2833_ = lean_ctor_get(v_cfg_2803_, 25);
v_libPrefixOnWindows_2834_ = lean_ctor_get_uint8(v_cfg_2803_, sizeof(void*)*28 + 4);
v_allowImportAll_2835_ = lean_ctor_get_uint8(v_cfg_2803_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2836_ = lean_ctor_get(v_cfg_2803_, 26);
v_checks_2837_ = lean_ctor_get(v_cfg_2803_, 27);
v_fixedToolchain_2838_ = lean_ctor_get_uint8(v_cfg_2803_, sizeof(void*)*28 + 6);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_cfg_2803_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2840_ = v_cfg_2803_;
v_isShared_2841_ = v_isSharedCheck_2846_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_checks_2837_);
lean_inc(v_builtinLint_x3f_2836_);
lean_inc(v_restoreAllArtifacts_x3f_2833_);
lean_inc(v_enableArtifactCache_x3f_2832_);
lean_inc(v_readmeFile_2830_);
lean_inc(v_licenseFiles_2829_);
lean_inc(v_license_2828_);
lean_inc(v_homepage_2827_);
lean_inc(v_keywords_2826_);
lean_inc(v_description_2825_);
lean_inc(v_versionTags_2824_);
lean_inc(v_version_2823_);
lean_inc(v_lintDriverArgs_2822_);
lean_inc(v_lintDriver_2821_);
lean_inc(v_testDriverArgs_2820_);
lean_inc(v_testDriver_2819_);
lean_inc(v_buildArchive_2817_);
lean_inc(v_releaseRepo_2816_);
lean_inc(v_irDir_2815_);
lean_inc(v_binDir_2814_);
lean_inc(v_nativeLibDir_2813_);
lean_inc(v_leanLibDir_2812_);
lean_inc(v_buildDir_2811_);
lean_inc(v_srcDir_2810_);
lean_inc(v_moreGlobalServerArgs_2809_);
lean_inc(v_extraDepTargets_2807_);
lean_inc(v_toLeanConfig_2805_);
lean_inc(v_toWorkspaceConfig_2804_);
lean_dec(v_cfg_2803_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2846_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2842_ = lean_apply_1(v_f_2802_, v_homepage_2827_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 20, v___x_2842_);
v___x_2844_ = v___x_2840_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_toWorkspaceConfig_2804_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_toLeanConfig_2805_);
lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_extraDepTargets_2807_);
lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_moreGlobalServerArgs_2809_);
lean_ctor_set(v_reuseFailAlloc_2845_, 4, v_srcDir_2810_);
lean_ctor_set(v_reuseFailAlloc_2845_, 5, v_buildDir_2811_);
lean_ctor_set(v_reuseFailAlloc_2845_, 6, v_leanLibDir_2812_);
lean_ctor_set(v_reuseFailAlloc_2845_, 7, v_nativeLibDir_2813_);
lean_ctor_set(v_reuseFailAlloc_2845_, 8, v_binDir_2814_);
lean_ctor_set(v_reuseFailAlloc_2845_, 9, v_irDir_2815_);
lean_ctor_set(v_reuseFailAlloc_2845_, 10, v_releaseRepo_2816_);
lean_ctor_set(v_reuseFailAlloc_2845_, 11, v_buildArchive_2817_);
lean_ctor_set(v_reuseFailAlloc_2845_, 12, v_testDriver_2819_);
lean_ctor_set(v_reuseFailAlloc_2845_, 13, v_testDriverArgs_2820_);
lean_ctor_set(v_reuseFailAlloc_2845_, 14, v_lintDriver_2821_);
lean_ctor_set(v_reuseFailAlloc_2845_, 15, v_lintDriverArgs_2822_);
lean_ctor_set(v_reuseFailAlloc_2845_, 16, v_version_2823_);
lean_ctor_set(v_reuseFailAlloc_2845_, 17, v_versionTags_2824_);
lean_ctor_set(v_reuseFailAlloc_2845_, 18, v_description_2825_);
lean_ctor_set(v_reuseFailAlloc_2845_, 19, v_keywords_2826_);
lean_ctor_set(v_reuseFailAlloc_2845_, 20, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2845_, 21, v_license_2828_);
lean_ctor_set(v_reuseFailAlloc_2845_, 22, v_licenseFiles_2829_);
lean_ctor_set(v_reuseFailAlloc_2845_, 23, v_readmeFile_2830_);
lean_ctor_set(v_reuseFailAlloc_2845_, 24, v_enableArtifactCache_x3f_2832_);
lean_ctor_set(v_reuseFailAlloc_2845_, 25, v_restoreAllArtifacts_x3f_2833_);
lean_ctor_set(v_reuseFailAlloc_2845_, 26, v_builtinLint_x3f_2836_);
lean_ctor_set(v_reuseFailAlloc_2845_, 27, v_checks_2837_);
lean_ctor_set_uint8(v_reuseFailAlloc_2845_, sizeof(void*)*28, v_bootstrap_2806_);
lean_ctor_set_uint8(v_reuseFailAlloc_2845_, sizeof(void*)*28 + 1, v_precompileModules_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2845_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2818_);
lean_ctor_set_uint8(v_reuseFailAlloc_2845_, sizeof(void*)*28 + 3, v_reservoir_2831_);
lean_ctor_set_uint8(v_reuseFailAlloc_2845_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2834_);
lean_ctor_set_uint8(v_reuseFailAlloc_2845_, sizeof(void*)*28 + 5, v_allowImportAll_2835_);
lean_ctor_set_uint8(v_reuseFailAlloc_2845_, sizeof(void*)*28 + 6, v_fixedToolchain_2838_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg(){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = ((lean_object*)(l_Lake_PackageConfig_homepage___proj___redArg___closed__3));
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___boxed(lean_object* v___dummy_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lake_PackageConfig_homepage___proj___redArg();
return v_res_2858_;
}
}
static lean_object* _init_l_Lake_PackageConfig_homepage___proj___closed__0(void){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lake_PackageConfig_homepage___proj___redArg();
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object* v_p_2860_, lean_object* v_n_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = lean_obj_once(&l_Lake_PackageConfig_homepage___proj___closed__0, &l_Lake_PackageConfig_homepage___proj___closed__0_once, _init_l_Lake_PackageConfig_homepage___proj___closed__0);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object* v_p_2863_, lean_object* v_n_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lake_PackageConfig_homepage___proj(v_p_2863_, v_n_2864_);
lean_dec(v_n_2864_);
lean_dec(v_p_2863_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___redArg(){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_obj_once(&l_Lake_PackageConfig_homepage___proj___closed__0, &l_Lake_PackageConfig_homepage___proj___closed__0_once, _init_l_Lake_PackageConfig_homepage___proj___closed__0);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___redArg___boxed(lean_object* v___dummy_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lake_PackageConfig_homepage_instConfigField___redArg();
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object* v_p_2870_, lean_object* v_n_2871_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_obj_once(&l_Lake_PackageConfig_homepage___proj___closed__0, &l_Lake_PackageConfig_homepage___proj___closed__0_once, _init_l_Lake_PackageConfig_homepage___proj___closed__0);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object* v_p_2873_, lean_object* v_n_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lake_PackageConfig_homepage_instConfigField(v_p_2873_, v_n_2874_);
lean_dec(v_n_2874_);
lean_dec(v_p_2873_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__0(lean_object* v_cfg_2876_){
_start:
{
lean_object* v_license_2877_; 
v_license_2877_ = lean_ctor_get(v_cfg_2876_, 21);
lean_inc_ref(v_license_2877_);
return v_license_2877_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__0___boxed(lean_object* v_cfg_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lake_PackageConfig_license___proj___redArg___lam__0(v_cfg_2878_);
lean_dec_ref(v_cfg_2878_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__1(lean_object* v_val_2880_, lean_object* v_cfg_2881_){
_start:
{
lean_object* v_toWorkspaceConfig_2882_; lean_object* v_toLeanConfig_2883_; uint8_t v_bootstrap_2884_; lean_object* v_extraDepTargets_2885_; uint8_t v_precompileModules_2886_; lean_object* v_moreGlobalServerArgs_2887_; lean_object* v_srcDir_2888_; lean_object* v_buildDir_2889_; lean_object* v_leanLibDir_2890_; lean_object* v_nativeLibDir_2891_; lean_object* v_binDir_2892_; lean_object* v_irDir_2893_; lean_object* v_releaseRepo_2894_; lean_object* v_buildArchive_2895_; uint8_t v_preferReleaseBuild_2896_; lean_object* v_testDriver_2897_; lean_object* v_testDriverArgs_2898_; lean_object* v_lintDriver_2899_; lean_object* v_lintDriverArgs_2900_; lean_object* v_version_2901_; lean_object* v_versionTags_2902_; lean_object* v_description_2903_; lean_object* v_keywords_2904_; lean_object* v_homepage_2905_; lean_object* v_licenseFiles_2906_; lean_object* v_readmeFile_2907_; uint8_t v_reservoir_2908_; lean_object* v_enableArtifactCache_x3f_2909_; lean_object* v_restoreAllArtifacts_x3f_2910_; uint8_t v_libPrefixOnWindows_2911_; uint8_t v_allowImportAll_2912_; lean_object* v_builtinLint_x3f_2913_; lean_object* v_checks_2914_; uint8_t v_fixedToolchain_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
v_toWorkspaceConfig_2882_ = lean_ctor_get(v_cfg_2881_, 0);
v_toLeanConfig_2883_ = lean_ctor_get(v_cfg_2881_, 1);
v_bootstrap_2884_ = lean_ctor_get_uint8(v_cfg_2881_, sizeof(void*)*28);
v_extraDepTargets_2885_ = lean_ctor_get(v_cfg_2881_, 2);
v_precompileModules_2886_ = lean_ctor_get_uint8(v_cfg_2881_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2887_ = lean_ctor_get(v_cfg_2881_, 3);
v_srcDir_2888_ = lean_ctor_get(v_cfg_2881_, 4);
v_buildDir_2889_ = lean_ctor_get(v_cfg_2881_, 5);
v_leanLibDir_2890_ = lean_ctor_get(v_cfg_2881_, 6);
v_nativeLibDir_2891_ = lean_ctor_get(v_cfg_2881_, 7);
v_binDir_2892_ = lean_ctor_get(v_cfg_2881_, 8);
v_irDir_2893_ = lean_ctor_get(v_cfg_2881_, 9);
v_releaseRepo_2894_ = lean_ctor_get(v_cfg_2881_, 10);
v_buildArchive_2895_ = lean_ctor_get(v_cfg_2881_, 11);
v_preferReleaseBuild_2896_ = lean_ctor_get_uint8(v_cfg_2881_, sizeof(void*)*28 + 2);
v_testDriver_2897_ = lean_ctor_get(v_cfg_2881_, 12);
v_testDriverArgs_2898_ = lean_ctor_get(v_cfg_2881_, 13);
v_lintDriver_2899_ = lean_ctor_get(v_cfg_2881_, 14);
v_lintDriverArgs_2900_ = lean_ctor_get(v_cfg_2881_, 15);
v_version_2901_ = lean_ctor_get(v_cfg_2881_, 16);
v_versionTags_2902_ = lean_ctor_get(v_cfg_2881_, 17);
v_description_2903_ = lean_ctor_get(v_cfg_2881_, 18);
v_keywords_2904_ = lean_ctor_get(v_cfg_2881_, 19);
v_homepage_2905_ = lean_ctor_get(v_cfg_2881_, 20);
v_licenseFiles_2906_ = lean_ctor_get(v_cfg_2881_, 22);
v_readmeFile_2907_ = lean_ctor_get(v_cfg_2881_, 23);
v_reservoir_2908_ = lean_ctor_get_uint8(v_cfg_2881_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2909_ = lean_ctor_get(v_cfg_2881_, 24);
v_restoreAllArtifacts_x3f_2910_ = lean_ctor_get(v_cfg_2881_, 25);
v_libPrefixOnWindows_2911_ = lean_ctor_get_uint8(v_cfg_2881_, sizeof(void*)*28 + 4);
v_allowImportAll_2912_ = lean_ctor_get_uint8(v_cfg_2881_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2913_ = lean_ctor_get(v_cfg_2881_, 26);
v_checks_2914_ = lean_ctor_get(v_cfg_2881_, 27);
v_fixedToolchain_2915_ = lean_ctor_get_uint8(v_cfg_2881_, sizeof(void*)*28 + 6);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_cfg_2881_);
if (v_isSharedCheck_2922_ == 0)
{
lean_object* v_unused_2923_; 
v_unused_2923_ = lean_ctor_get(v_cfg_2881_, 21);
lean_dec(v_unused_2923_);
v___x_2917_ = v_cfg_2881_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_checks_2914_);
lean_inc(v_builtinLint_x3f_2913_);
lean_inc(v_restoreAllArtifacts_x3f_2910_);
lean_inc(v_enableArtifactCache_x3f_2909_);
lean_inc(v_readmeFile_2907_);
lean_inc(v_licenseFiles_2906_);
lean_inc(v_homepage_2905_);
lean_inc(v_keywords_2904_);
lean_inc(v_description_2903_);
lean_inc(v_versionTags_2902_);
lean_inc(v_version_2901_);
lean_inc(v_lintDriverArgs_2900_);
lean_inc(v_lintDriver_2899_);
lean_inc(v_testDriverArgs_2898_);
lean_inc(v_testDriver_2897_);
lean_inc(v_buildArchive_2895_);
lean_inc(v_releaseRepo_2894_);
lean_inc(v_irDir_2893_);
lean_inc(v_binDir_2892_);
lean_inc(v_nativeLibDir_2891_);
lean_inc(v_leanLibDir_2890_);
lean_inc(v_buildDir_2889_);
lean_inc(v_srcDir_2888_);
lean_inc(v_moreGlobalServerArgs_2887_);
lean_inc(v_extraDepTargets_2885_);
lean_inc(v_toLeanConfig_2883_);
lean_inc(v_toWorkspaceConfig_2882_);
lean_dec(v_cfg_2881_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 21, v_val_2880_);
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_toWorkspaceConfig_2882_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_toLeanConfig_2883_);
lean_ctor_set(v_reuseFailAlloc_2921_, 2, v_extraDepTargets_2885_);
lean_ctor_set(v_reuseFailAlloc_2921_, 3, v_moreGlobalServerArgs_2887_);
lean_ctor_set(v_reuseFailAlloc_2921_, 4, v_srcDir_2888_);
lean_ctor_set(v_reuseFailAlloc_2921_, 5, v_buildDir_2889_);
lean_ctor_set(v_reuseFailAlloc_2921_, 6, v_leanLibDir_2890_);
lean_ctor_set(v_reuseFailAlloc_2921_, 7, v_nativeLibDir_2891_);
lean_ctor_set(v_reuseFailAlloc_2921_, 8, v_binDir_2892_);
lean_ctor_set(v_reuseFailAlloc_2921_, 9, v_irDir_2893_);
lean_ctor_set(v_reuseFailAlloc_2921_, 10, v_releaseRepo_2894_);
lean_ctor_set(v_reuseFailAlloc_2921_, 11, v_buildArchive_2895_);
lean_ctor_set(v_reuseFailAlloc_2921_, 12, v_testDriver_2897_);
lean_ctor_set(v_reuseFailAlloc_2921_, 13, v_testDriverArgs_2898_);
lean_ctor_set(v_reuseFailAlloc_2921_, 14, v_lintDriver_2899_);
lean_ctor_set(v_reuseFailAlloc_2921_, 15, v_lintDriverArgs_2900_);
lean_ctor_set(v_reuseFailAlloc_2921_, 16, v_version_2901_);
lean_ctor_set(v_reuseFailAlloc_2921_, 17, v_versionTags_2902_);
lean_ctor_set(v_reuseFailAlloc_2921_, 18, v_description_2903_);
lean_ctor_set(v_reuseFailAlloc_2921_, 19, v_keywords_2904_);
lean_ctor_set(v_reuseFailAlloc_2921_, 20, v_homepage_2905_);
lean_ctor_set(v_reuseFailAlloc_2921_, 21, v_val_2880_);
lean_ctor_set(v_reuseFailAlloc_2921_, 22, v_licenseFiles_2906_);
lean_ctor_set(v_reuseFailAlloc_2921_, 23, v_readmeFile_2907_);
lean_ctor_set(v_reuseFailAlloc_2921_, 24, v_enableArtifactCache_x3f_2909_);
lean_ctor_set(v_reuseFailAlloc_2921_, 25, v_restoreAllArtifacts_x3f_2910_);
lean_ctor_set(v_reuseFailAlloc_2921_, 26, v_builtinLint_x3f_2913_);
lean_ctor_set(v_reuseFailAlloc_2921_, 27, v_checks_2914_);
lean_ctor_set_uint8(v_reuseFailAlloc_2921_, sizeof(void*)*28, v_bootstrap_2884_);
lean_ctor_set_uint8(v_reuseFailAlloc_2921_, sizeof(void*)*28 + 1, v_precompileModules_2886_);
lean_ctor_set_uint8(v_reuseFailAlloc_2921_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2896_);
lean_ctor_set_uint8(v_reuseFailAlloc_2921_, sizeof(void*)*28 + 3, v_reservoir_2908_);
lean_ctor_set_uint8(v_reuseFailAlloc_2921_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2911_);
lean_ctor_set_uint8(v_reuseFailAlloc_2921_, sizeof(void*)*28 + 5, v_allowImportAll_2912_);
lean_ctor_set_uint8(v_reuseFailAlloc_2921_, sizeof(void*)*28 + 6, v_fixedToolchain_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__2(lean_object* v_f_2924_, lean_object* v_cfg_2925_){
_start:
{
lean_object* v_toWorkspaceConfig_2926_; lean_object* v_toLeanConfig_2927_; uint8_t v_bootstrap_2928_; lean_object* v_extraDepTargets_2929_; uint8_t v_precompileModules_2930_; lean_object* v_moreGlobalServerArgs_2931_; lean_object* v_srcDir_2932_; lean_object* v_buildDir_2933_; lean_object* v_leanLibDir_2934_; lean_object* v_nativeLibDir_2935_; lean_object* v_binDir_2936_; lean_object* v_irDir_2937_; lean_object* v_releaseRepo_2938_; lean_object* v_buildArchive_2939_; uint8_t v_preferReleaseBuild_2940_; lean_object* v_testDriver_2941_; lean_object* v_testDriverArgs_2942_; lean_object* v_lintDriver_2943_; lean_object* v_lintDriverArgs_2944_; lean_object* v_version_2945_; lean_object* v_versionTags_2946_; lean_object* v_description_2947_; lean_object* v_keywords_2948_; lean_object* v_homepage_2949_; lean_object* v_license_2950_; lean_object* v_licenseFiles_2951_; lean_object* v_readmeFile_2952_; uint8_t v_reservoir_2953_; lean_object* v_enableArtifactCache_x3f_2954_; lean_object* v_restoreAllArtifacts_x3f_2955_; uint8_t v_libPrefixOnWindows_2956_; uint8_t v_allowImportAll_2957_; lean_object* v_builtinLint_x3f_2958_; lean_object* v_checks_2959_; uint8_t v_fixedToolchain_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2968_; 
v_toWorkspaceConfig_2926_ = lean_ctor_get(v_cfg_2925_, 0);
v_toLeanConfig_2927_ = lean_ctor_get(v_cfg_2925_, 1);
v_bootstrap_2928_ = lean_ctor_get_uint8(v_cfg_2925_, sizeof(void*)*28);
v_extraDepTargets_2929_ = lean_ctor_get(v_cfg_2925_, 2);
v_precompileModules_2930_ = lean_ctor_get_uint8(v_cfg_2925_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2931_ = lean_ctor_get(v_cfg_2925_, 3);
v_srcDir_2932_ = lean_ctor_get(v_cfg_2925_, 4);
v_buildDir_2933_ = lean_ctor_get(v_cfg_2925_, 5);
v_leanLibDir_2934_ = lean_ctor_get(v_cfg_2925_, 6);
v_nativeLibDir_2935_ = lean_ctor_get(v_cfg_2925_, 7);
v_binDir_2936_ = lean_ctor_get(v_cfg_2925_, 8);
v_irDir_2937_ = lean_ctor_get(v_cfg_2925_, 9);
v_releaseRepo_2938_ = lean_ctor_get(v_cfg_2925_, 10);
v_buildArchive_2939_ = lean_ctor_get(v_cfg_2925_, 11);
v_preferReleaseBuild_2940_ = lean_ctor_get_uint8(v_cfg_2925_, sizeof(void*)*28 + 2);
v_testDriver_2941_ = lean_ctor_get(v_cfg_2925_, 12);
v_testDriverArgs_2942_ = lean_ctor_get(v_cfg_2925_, 13);
v_lintDriver_2943_ = lean_ctor_get(v_cfg_2925_, 14);
v_lintDriverArgs_2944_ = lean_ctor_get(v_cfg_2925_, 15);
v_version_2945_ = lean_ctor_get(v_cfg_2925_, 16);
v_versionTags_2946_ = lean_ctor_get(v_cfg_2925_, 17);
v_description_2947_ = lean_ctor_get(v_cfg_2925_, 18);
v_keywords_2948_ = lean_ctor_get(v_cfg_2925_, 19);
v_homepage_2949_ = lean_ctor_get(v_cfg_2925_, 20);
v_license_2950_ = lean_ctor_get(v_cfg_2925_, 21);
v_licenseFiles_2951_ = lean_ctor_get(v_cfg_2925_, 22);
v_readmeFile_2952_ = lean_ctor_get(v_cfg_2925_, 23);
v_reservoir_2953_ = lean_ctor_get_uint8(v_cfg_2925_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2954_ = lean_ctor_get(v_cfg_2925_, 24);
v_restoreAllArtifacts_x3f_2955_ = lean_ctor_get(v_cfg_2925_, 25);
v_libPrefixOnWindows_2956_ = lean_ctor_get_uint8(v_cfg_2925_, sizeof(void*)*28 + 4);
v_allowImportAll_2957_ = lean_ctor_get_uint8(v_cfg_2925_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2958_ = lean_ctor_get(v_cfg_2925_, 26);
v_checks_2959_ = lean_ctor_get(v_cfg_2925_, 27);
v_fixedToolchain_2960_ = lean_ctor_get_uint8(v_cfg_2925_, sizeof(void*)*28 + 6);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_cfg_2925_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2962_ = v_cfg_2925_;
v_isShared_2963_ = v_isSharedCheck_2968_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_checks_2959_);
lean_inc(v_builtinLint_x3f_2958_);
lean_inc(v_restoreAllArtifacts_x3f_2955_);
lean_inc(v_enableArtifactCache_x3f_2954_);
lean_inc(v_readmeFile_2952_);
lean_inc(v_licenseFiles_2951_);
lean_inc(v_license_2950_);
lean_inc(v_homepage_2949_);
lean_inc(v_keywords_2948_);
lean_inc(v_description_2947_);
lean_inc(v_versionTags_2946_);
lean_inc(v_version_2945_);
lean_inc(v_lintDriverArgs_2944_);
lean_inc(v_lintDriver_2943_);
lean_inc(v_testDriverArgs_2942_);
lean_inc(v_testDriver_2941_);
lean_inc(v_buildArchive_2939_);
lean_inc(v_releaseRepo_2938_);
lean_inc(v_irDir_2937_);
lean_inc(v_binDir_2936_);
lean_inc(v_nativeLibDir_2935_);
lean_inc(v_leanLibDir_2934_);
lean_inc(v_buildDir_2933_);
lean_inc(v_srcDir_2932_);
lean_inc(v_moreGlobalServerArgs_2931_);
lean_inc(v_extraDepTargets_2929_);
lean_inc(v_toLeanConfig_2927_);
lean_inc(v_toWorkspaceConfig_2926_);
lean_dec(v_cfg_2925_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2968_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2964_ = lean_apply_1(v_f_2924_, v_license_2950_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 21, v___x_2964_);
v___x_2966_ = v___x_2962_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_toWorkspaceConfig_2926_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_toLeanConfig_2927_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v_extraDepTargets_2929_);
lean_ctor_set(v_reuseFailAlloc_2967_, 3, v_moreGlobalServerArgs_2931_);
lean_ctor_set(v_reuseFailAlloc_2967_, 4, v_srcDir_2932_);
lean_ctor_set(v_reuseFailAlloc_2967_, 5, v_buildDir_2933_);
lean_ctor_set(v_reuseFailAlloc_2967_, 6, v_leanLibDir_2934_);
lean_ctor_set(v_reuseFailAlloc_2967_, 7, v_nativeLibDir_2935_);
lean_ctor_set(v_reuseFailAlloc_2967_, 8, v_binDir_2936_);
lean_ctor_set(v_reuseFailAlloc_2967_, 9, v_irDir_2937_);
lean_ctor_set(v_reuseFailAlloc_2967_, 10, v_releaseRepo_2938_);
lean_ctor_set(v_reuseFailAlloc_2967_, 11, v_buildArchive_2939_);
lean_ctor_set(v_reuseFailAlloc_2967_, 12, v_testDriver_2941_);
lean_ctor_set(v_reuseFailAlloc_2967_, 13, v_testDriverArgs_2942_);
lean_ctor_set(v_reuseFailAlloc_2967_, 14, v_lintDriver_2943_);
lean_ctor_set(v_reuseFailAlloc_2967_, 15, v_lintDriverArgs_2944_);
lean_ctor_set(v_reuseFailAlloc_2967_, 16, v_version_2945_);
lean_ctor_set(v_reuseFailAlloc_2967_, 17, v_versionTags_2946_);
lean_ctor_set(v_reuseFailAlloc_2967_, 18, v_description_2947_);
lean_ctor_set(v_reuseFailAlloc_2967_, 19, v_keywords_2948_);
lean_ctor_set(v_reuseFailAlloc_2967_, 20, v_homepage_2949_);
lean_ctor_set(v_reuseFailAlloc_2967_, 21, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2967_, 22, v_licenseFiles_2951_);
lean_ctor_set(v_reuseFailAlloc_2967_, 23, v_readmeFile_2952_);
lean_ctor_set(v_reuseFailAlloc_2967_, 24, v_enableArtifactCache_x3f_2954_);
lean_ctor_set(v_reuseFailAlloc_2967_, 25, v_restoreAllArtifacts_x3f_2955_);
lean_ctor_set(v_reuseFailAlloc_2967_, 26, v_builtinLint_x3f_2958_);
lean_ctor_set(v_reuseFailAlloc_2967_, 27, v_checks_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*28, v_bootstrap_2928_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*28 + 1, v_precompileModules_2930_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2940_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*28 + 3, v_reservoir_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*28 + 5, v_allowImportAll_2957_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*28 + 6, v_fixedToolchain_2960_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg(){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = ((lean_object*)(l_Lake_PackageConfig_license___proj___redArg___closed__3));
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___boxed(lean_object* v___dummy_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lake_PackageConfig_license___proj___redArg();
return v_res_2980_;
}
}
static lean_object* _init_l_Lake_PackageConfig_license___proj___closed__0(void){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lake_PackageConfig_license___proj___redArg();
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object* v_p_2982_, lean_object* v_n_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_obj_once(&l_Lake_PackageConfig_license___proj___closed__0, &l_Lake_PackageConfig_license___proj___closed__0_once, _init_l_Lake_PackageConfig_license___proj___closed__0);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object* v_p_2985_, lean_object* v_n_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lake_PackageConfig_license___proj(v_p_2985_, v_n_2986_);
lean_dec(v_n_2986_);
lean_dec(v_p_2985_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___redArg(){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = lean_obj_once(&l_Lake_PackageConfig_license___proj___closed__0, &l_Lake_PackageConfig_license___proj___closed__0_once, _init_l_Lake_PackageConfig_license___proj___closed__0);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___redArg___boxed(lean_object* v___dummy_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lake_PackageConfig_license_instConfigField___redArg();
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object* v_p_2992_, lean_object* v_n_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_obj_once(&l_Lake_PackageConfig_license___proj___closed__0, &l_Lake_PackageConfig_license___proj___closed__0_once, _init_l_Lake_PackageConfig_license___proj___closed__0);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object* v_p_2995_, lean_object* v_n_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lake_PackageConfig_license_instConfigField(v_p_2995_, v_n_2996_);
lean_dec(v_n_2996_);
lean_dec(v_p_2995_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0(lean_object* v_cfg_2998_){
_start:
{
lean_object* v_licenseFiles_2999_; 
v_licenseFiles_2999_ = lean_ctor_get(v_cfg_2998_, 22);
lean_inc_ref(v_licenseFiles_2999_);
return v_licenseFiles_2999_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0___boxed(lean_object* v_cfg_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0(v_cfg_3000_);
lean_dec_ref(v_cfg_3000_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__1(lean_object* v_val_3002_, lean_object* v_cfg_3003_){
_start:
{
lean_object* v_toWorkspaceConfig_3004_; lean_object* v_toLeanConfig_3005_; uint8_t v_bootstrap_3006_; lean_object* v_extraDepTargets_3007_; uint8_t v_precompileModules_3008_; lean_object* v_moreGlobalServerArgs_3009_; lean_object* v_srcDir_3010_; lean_object* v_buildDir_3011_; lean_object* v_leanLibDir_3012_; lean_object* v_nativeLibDir_3013_; lean_object* v_binDir_3014_; lean_object* v_irDir_3015_; lean_object* v_releaseRepo_3016_; lean_object* v_buildArchive_3017_; uint8_t v_preferReleaseBuild_3018_; lean_object* v_testDriver_3019_; lean_object* v_testDriverArgs_3020_; lean_object* v_lintDriver_3021_; lean_object* v_lintDriverArgs_3022_; lean_object* v_version_3023_; lean_object* v_versionTags_3024_; lean_object* v_description_3025_; lean_object* v_keywords_3026_; lean_object* v_homepage_3027_; lean_object* v_license_3028_; lean_object* v_readmeFile_3029_; uint8_t v_reservoir_3030_; lean_object* v_enableArtifactCache_x3f_3031_; lean_object* v_restoreAllArtifacts_x3f_3032_; uint8_t v_libPrefixOnWindows_3033_; uint8_t v_allowImportAll_3034_; lean_object* v_builtinLint_x3f_3035_; lean_object* v_checks_3036_; uint8_t v_fixedToolchain_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
v_toWorkspaceConfig_3004_ = lean_ctor_get(v_cfg_3003_, 0);
v_toLeanConfig_3005_ = lean_ctor_get(v_cfg_3003_, 1);
v_bootstrap_3006_ = lean_ctor_get_uint8(v_cfg_3003_, sizeof(void*)*28);
v_extraDepTargets_3007_ = lean_ctor_get(v_cfg_3003_, 2);
v_precompileModules_3008_ = lean_ctor_get_uint8(v_cfg_3003_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3009_ = lean_ctor_get(v_cfg_3003_, 3);
v_srcDir_3010_ = lean_ctor_get(v_cfg_3003_, 4);
v_buildDir_3011_ = lean_ctor_get(v_cfg_3003_, 5);
v_leanLibDir_3012_ = lean_ctor_get(v_cfg_3003_, 6);
v_nativeLibDir_3013_ = lean_ctor_get(v_cfg_3003_, 7);
v_binDir_3014_ = lean_ctor_get(v_cfg_3003_, 8);
v_irDir_3015_ = lean_ctor_get(v_cfg_3003_, 9);
v_releaseRepo_3016_ = lean_ctor_get(v_cfg_3003_, 10);
v_buildArchive_3017_ = lean_ctor_get(v_cfg_3003_, 11);
v_preferReleaseBuild_3018_ = lean_ctor_get_uint8(v_cfg_3003_, sizeof(void*)*28 + 2);
v_testDriver_3019_ = lean_ctor_get(v_cfg_3003_, 12);
v_testDriverArgs_3020_ = lean_ctor_get(v_cfg_3003_, 13);
v_lintDriver_3021_ = lean_ctor_get(v_cfg_3003_, 14);
v_lintDriverArgs_3022_ = lean_ctor_get(v_cfg_3003_, 15);
v_version_3023_ = lean_ctor_get(v_cfg_3003_, 16);
v_versionTags_3024_ = lean_ctor_get(v_cfg_3003_, 17);
v_description_3025_ = lean_ctor_get(v_cfg_3003_, 18);
v_keywords_3026_ = lean_ctor_get(v_cfg_3003_, 19);
v_homepage_3027_ = lean_ctor_get(v_cfg_3003_, 20);
v_license_3028_ = lean_ctor_get(v_cfg_3003_, 21);
v_readmeFile_3029_ = lean_ctor_get(v_cfg_3003_, 23);
v_reservoir_3030_ = lean_ctor_get_uint8(v_cfg_3003_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3031_ = lean_ctor_get(v_cfg_3003_, 24);
v_restoreAllArtifacts_x3f_3032_ = lean_ctor_get(v_cfg_3003_, 25);
v_libPrefixOnWindows_3033_ = lean_ctor_get_uint8(v_cfg_3003_, sizeof(void*)*28 + 4);
v_allowImportAll_3034_ = lean_ctor_get_uint8(v_cfg_3003_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3035_ = lean_ctor_get(v_cfg_3003_, 26);
v_checks_3036_ = lean_ctor_get(v_cfg_3003_, 27);
v_fixedToolchain_3037_ = lean_ctor_get_uint8(v_cfg_3003_, sizeof(void*)*28 + 6);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_cfg_3003_);
if (v_isSharedCheck_3044_ == 0)
{
lean_object* v_unused_3045_; 
v_unused_3045_ = lean_ctor_get(v_cfg_3003_, 22);
lean_dec(v_unused_3045_);
v___x_3039_ = v_cfg_3003_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_checks_3036_);
lean_inc(v_builtinLint_x3f_3035_);
lean_inc(v_restoreAllArtifacts_x3f_3032_);
lean_inc(v_enableArtifactCache_x3f_3031_);
lean_inc(v_readmeFile_3029_);
lean_inc(v_license_3028_);
lean_inc(v_homepage_3027_);
lean_inc(v_keywords_3026_);
lean_inc(v_description_3025_);
lean_inc(v_versionTags_3024_);
lean_inc(v_version_3023_);
lean_inc(v_lintDriverArgs_3022_);
lean_inc(v_lintDriver_3021_);
lean_inc(v_testDriverArgs_3020_);
lean_inc(v_testDriver_3019_);
lean_inc(v_buildArchive_3017_);
lean_inc(v_releaseRepo_3016_);
lean_inc(v_irDir_3015_);
lean_inc(v_binDir_3014_);
lean_inc(v_nativeLibDir_3013_);
lean_inc(v_leanLibDir_3012_);
lean_inc(v_buildDir_3011_);
lean_inc(v_srcDir_3010_);
lean_inc(v_moreGlobalServerArgs_3009_);
lean_inc(v_extraDepTargets_3007_);
lean_inc(v_toLeanConfig_3005_);
lean_inc(v_toWorkspaceConfig_3004_);
lean_dec(v_cfg_3003_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 22, v_val_3002_);
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_toWorkspaceConfig_3004_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v_toLeanConfig_3005_);
lean_ctor_set(v_reuseFailAlloc_3043_, 2, v_extraDepTargets_3007_);
lean_ctor_set(v_reuseFailAlloc_3043_, 3, v_moreGlobalServerArgs_3009_);
lean_ctor_set(v_reuseFailAlloc_3043_, 4, v_srcDir_3010_);
lean_ctor_set(v_reuseFailAlloc_3043_, 5, v_buildDir_3011_);
lean_ctor_set(v_reuseFailAlloc_3043_, 6, v_leanLibDir_3012_);
lean_ctor_set(v_reuseFailAlloc_3043_, 7, v_nativeLibDir_3013_);
lean_ctor_set(v_reuseFailAlloc_3043_, 8, v_binDir_3014_);
lean_ctor_set(v_reuseFailAlloc_3043_, 9, v_irDir_3015_);
lean_ctor_set(v_reuseFailAlloc_3043_, 10, v_releaseRepo_3016_);
lean_ctor_set(v_reuseFailAlloc_3043_, 11, v_buildArchive_3017_);
lean_ctor_set(v_reuseFailAlloc_3043_, 12, v_testDriver_3019_);
lean_ctor_set(v_reuseFailAlloc_3043_, 13, v_testDriverArgs_3020_);
lean_ctor_set(v_reuseFailAlloc_3043_, 14, v_lintDriver_3021_);
lean_ctor_set(v_reuseFailAlloc_3043_, 15, v_lintDriverArgs_3022_);
lean_ctor_set(v_reuseFailAlloc_3043_, 16, v_version_3023_);
lean_ctor_set(v_reuseFailAlloc_3043_, 17, v_versionTags_3024_);
lean_ctor_set(v_reuseFailAlloc_3043_, 18, v_description_3025_);
lean_ctor_set(v_reuseFailAlloc_3043_, 19, v_keywords_3026_);
lean_ctor_set(v_reuseFailAlloc_3043_, 20, v_homepage_3027_);
lean_ctor_set(v_reuseFailAlloc_3043_, 21, v_license_3028_);
lean_ctor_set(v_reuseFailAlloc_3043_, 22, v_val_3002_);
lean_ctor_set(v_reuseFailAlloc_3043_, 23, v_readmeFile_3029_);
lean_ctor_set(v_reuseFailAlloc_3043_, 24, v_enableArtifactCache_x3f_3031_);
lean_ctor_set(v_reuseFailAlloc_3043_, 25, v_restoreAllArtifacts_x3f_3032_);
lean_ctor_set(v_reuseFailAlloc_3043_, 26, v_builtinLint_x3f_3035_);
lean_ctor_set(v_reuseFailAlloc_3043_, 27, v_checks_3036_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, sizeof(void*)*28, v_bootstrap_3006_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, sizeof(void*)*28 + 1, v_precompileModules_3008_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3018_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, sizeof(void*)*28 + 3, v_reservoir_3030_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3033_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, sizeof(void*)*28 + 5, v_allowImportAll_3034_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, sizeof(void*)*28 + 6, v_fixedToolchain_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__2(lean_object* v_f_3046_, lean_object* v_cfg_3047_){
_start:
{
lean_object* v_toWorkspaceConfig_3048_; lean_object* v_toLeanConfig_3049_; uint8_t v_bootstrap_3050_; lean_object* v_extraDepTargets_3051_; uint8_t v_precompileModules_3052_; lean_object* v_moreGlobalServerArgs_3053_; lean_object* v_srcDir_3054_; lean_object* v_buildDir_3055_; lean_object* v_leanLibDir_3056_; lean_object* v_nativeLibDir_3057_; lean_object* v_binDir_3058_; lean_object* v_irDir_3059_; lean_object* v_releaseRepo_3060_; lean_object* v_buildArchive_3061_; uint8_t v_preferReleaseBuild_3062_; lean_object* v_testDriver_3063_; lean_object* v_testDriverArgs_3064_; lean_object* v_lintDriver_3065_; lean_object* v_lintDriverArgs_3066_; lean_object* v_version_3067_; lean_object* v_versionTags_3068_; lean_object* v_description_3069_; lean_object* v_keywords_3070_; lean_object* v_homepage_3071_; lean_object* v_license_3072_; lean_object* v_licenseFiles_3073_; lean_object* v_readmeFile_3074_; uint8_t v_reservoir_3075_; lean_object* v_enableArtifactCache_x3f_3076_; lean_object* v_restoreAllArtifacts_x3f_3077_; uint8_t v_libPrefixOnWindows_3078_; uint8_t v_allowImportAll_3079_; lean_object* v_builtinLint_x3f_3080_; lean_object* v_checks_3081_; uint8_t v_fixedToolchain_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3090_; 
v_toWorkspaceConfig_3048_ = lean_ctor_get(v_cfg_3047_, 0);
v_toLeanConfig_3049_ = lean_ctor_get(v_cfg_3047_, 1);
v_bootstrap_3050_ = lean_ctor_get_uint8(v_cfg_3047_, sizeof(void*)*28);
v_extraDepTargets_3051_ = lean_ctor_get(v_cfg_3047_, 2);
v_precompileModules_3052_ = lean_ctor_get_uint8(v_cfg_3047_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3053_ = lean_ctor_get(v_cfg_3047_, 3);
v_srcDir_3054_ = lean_ctor_get(v_cfg_3047_, 4);
v_buildDir_3055_ = lean_ctor_get(v_cfg_3047_, 5);
v_leanLibDir_3056_ = lean_ctor_get(v_cfg_3047_, 6);
v_nativeLibDir_3057_ = lean_ctor_get(v_cfg_3047_, 7);
v_binDir_3058_ = lean_ctor_get(v_cfg_3047_, 8);
v_irDir_3059_ = lean_ctor_get(v_cfg_3047_, 9);
v_releaseRepo_3060_ = lean_ctor_get(v_cfg_3047_, 10);
v_buildArchive_3061_ = lean_ctor_get(v_cfg_3047_, 11);
v_preferReleaseBuild_3062_ = lean_ctor_get_uint8(v_cfg_3047_, sizeof(void*)*28 + 2);
v_testDriver_3063_ = lean_ctor_get(v_cfg_3047_, 12);
v_testDriverArgs_3064_ = lean_ctor_get(v_cfg_3047_, 13);
v_lintDriver_3065_ = lean_ctor_get(v_cfg_3047_, 14);
v_lintDriverArgs_3066_ = lean_ctor_get(v_cfg_3047_, 15);
v_version_3067_ = lean_ctor_get(v_cfg_3047_, 16);
v_versionTags_3068_ = lean_ctor_get(v_cfg_3047_, 17);
v_description_3069_ = lean_ctor_get(v_cfg_3047_, 18);
v_keywords_3070_ = lean_ctor_get(v_cfg_3047_, 19);
v_homepage_3071_ = lean_ctor_get(v_cfg_3047_, 20);
v_license_3072_ = lean_ctor_get(v_cfg_3047_, 21);
v_licenseFiles_3073_ = lean_ctor_get(v_cfg_3047_, 22);
v_readmeFile_3074_ = lean_ctor_get(v_cfg_3047_, 23);
v_reservoir_3075_ = lean_ctor_get_uint8(v_cfg_3047_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3076_ = lean_ctor_get(v_cfg_3047_, 24);
v_restoreAllArtifacts_x3f_3077_ = lean_ctor_get(v_cfg_3047_, 25);
v_libPrefixOnWindows_3078_ = lean_ctor_get_uint8(v_cfg_3047_, sizeof(void*)*28 + 4);
v_allowImportAll_3079_ = lean_ctor_get_uint8(v_cfg_3047_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3080_ = lean_ctor_get(v_cfg_3047_, 26);
v_checks_3081_ = lean_ctor_get(v_cfg_3047_, 27);
v_fixedToolchain_3082_ = lean_ctor_get_uint8(v_cfg_3047_, sizeof(void*)*28 + 6);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_cfg_3047_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3084_ = v_cfg_3047_;
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_checks_3081_);
lean_inc(v_builtinLint_x3f_3080_);
lean_inc(v_restoreAllArtifacts_x3f_3077_);
lean_inc(v_enableArtifactCache_x3f_3076_);
lean_inc(v_readmeFile_3074_);
lean_inc(v_licenseFiles_3073_);
lean_inc(v_license_3072_);
lean_inc(v_homepage_3071_);
lean_inc(v_keywords_3070_);
lean_inc(v_description_3069_);
lean_inc(v_versionTags_3068_);
lean_inc(v_version_3067_);
lean_inc(v_lintDriverArgs_3066_);
lean_inc(v_lintDriver_3065_);
lean_inc(v_testDriverArgs_3064_);
lean_inc(v_testDriver_3063_);
lean_inc(v_buildArchive_3061_);
lean_inc(v_releaseRepo_3060_);
lean_inc(v_irDir_3059_);
lean_inc(v_binDir_3058_);
lean_inc(v_nativeLibDir_3057_);
lean_inc(v_leanLibDir_3056_);
lean_inc(v_buildDir_3055_);
lean_inc(v_srcDir_3054_);
lean_inc(v_moreGlobalServerArgs_3053_);
lean_inc(v_extraDepTargets_3051_);
lean_inc(v_toLeanConfig_3049_);
lean_inc(v_toWorkspaceConfig_3048_);
lean_dec(v_cfg_3047_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3086_ = lean_apply_1(v_f_3046_, v_licenseFiles_3073_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 22, v___x_3086_);
v___x_3088_ = v___x_3084_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_toWorkspaceConfig_3048_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_toLeanConfig_3049_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_extraDepTargets_3051_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_moreGlobalServerArgs_3053_);
lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_srcDir_3054_);
lean_ctor_set(v_reuseFailAlloc_3089_, 5, v_buildDir_3055_);
lean_ctor_set(v_reuseFailAlloc_3089_, 6, v_leanLibDir_3056_);
lean_ctor_set(v_reuseFailAlloc_3089_, 7, v_nativeLibDir_3057_);
lean_ctor_set(v_reuseFailAlloc_3089_, 8, v_binDir_3058_);
lean_ctor_set(v_reuseFailAlloc_3089_, 9, v_irDir_3059_);
lean_ctor_set(v_reuseFailAlloc_3089_, 10, v_releaseRepo_3060_);
lean_ctor_set(v_reuseFailAlloc_3089_, 11, v_buildArchive_3061_);
lean_ctor_set(v_reuseFailAlloc_3089_, 12, v_testDriver_3063_);
lean_ctor_set(v_reuseFailAlloc_3089_, 13, v_testDriverArgs_3064_);
lean_ctor_set(v_reuseFailAlloc_3089_, 14, v_lintDriver_3065_);
lean_ctor_set(v_reuseFailAlloc_3089_, 15, v_lintDriverArgs_3066_);
lean_ctor_set(v_reuseFailAlloc_3089_, 16, v_version_3067_);
lean_ctor_set(v_reuseFailAlloc_3089_, 17, v_versionTags_3068_);
lean_ctor_set(v_reuseFailAlloc_3089_, 18, v_description_3069_);
lean_ctor_set(v_reuseFailAlloc_3089_, 19, v_keywords_3070_);
lean_ctor_set(v_reuseFailAlloc_3089_, 20, v_homepage_3071_);
lean_ctor_set(v_reuseFailAlloc_3089_, 21, v_license_3072_);
lean_ctor_set(v_reuseFailAlloc_3089_, 22, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3089_, 23, v_readmeFile_3074_);
lean_ctor_set(v_reuseFailAlloc_3089_, 24, v_enableArtifactCache_x3f_3076_);
lean_ctor_set(v_reuseFailAlloc_3089_, 25, v_restoreAllArtifacts_x3f_3077_);
lean_ctor_set(v_reuseFailAlloc_3089_, 26, v_builtinLint_x3f_3080_);
lean_ctor_set(v_reuseFailAlloc_3089_, 27, v_checks_3081_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*28, v_bootstrap_3050_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*28 + 1, v_precompileModules_3052_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3062_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*28 + 3, v_reservoir_3075_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3078_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*28 + 5, v_allowImportAll_3079_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*28 + 6, v_fixedToolchain_3082_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3(lean_object* v_x_3091_){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_unsigned_to_nat(1u);
v___x_3093_ = lean_mk_empty_array_with_capacity(v___x_3092_);
lean_dec_ref(v___x_3093_);
v___x_3094_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__6));
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3___boxed(lean_object* v_x_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3(v_x_3095_);
lean_dec_ref(v_x_3095_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg(){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__4));
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___boxed(lean_object* v___dummy_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lake_PackageConfig_licenseFiles___proj___redArg();
return v_res_3109_;
}
}
static lean_object* _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0(void){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Lake_PackageConfig_licenseFiles___proj___redArg();
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object* v_p_3111_, lean_object* v_n_3112_){
_start:
{
lean_object* v___x_3113_; 
v___x_3113_ = lean_obj_once(&l_Lake_PackageConfig_licenseFiles___proj___closed__0, &l_Lake_PackageConfig_licenseFiles___proj___closed__0_once, _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object* v_p_3114_, lean_object* v_n_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_3114_, v_n_3115_);
lean_dec(v_n_3115_);
lean_dec(v_p_3114_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___redArg(){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_obj_once(&l_Lake_PackageConfig_licenseFiles___proj___closed__0, &l_Lake_PackageConfig_licenseFiles___proj___closed__0_once, _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___redArg___boxed(lean_object* v___dummy_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lake_PackageConfig_licenseFiles_instConfigField___redArg();
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object* v_p_3121_, lean_object* v_n_3122_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_obj_once(&l_Lake_PackageConfig_licenseFiles___proj___closed__0, &l_Lake_PackageConfig_licenseFiles___proj___closed__0_once, _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object* v_p_3124_, lean_object* v_n_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lake_PackageConfig_licenseFiles_instConfigField(v_p_3124_, v_n_3125_);
lean_dec(v_n_3125_);
lean_dec(v_p_3124_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0(lean_object* v_cfg_3127_){
_start:
{
lean_object* v_readmeFile_3128_; 
v_readmeFile_3128_ = lean_ctor_get(v_cfg_3127_, 23);
lean_inc_ref(v_readmeFile_3128_);
return v_readmeFile_3128_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0___boxed(lean_object* v_cfg_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0(v_cfg_3129_);
lean_dec_ref(v_cfg_3129_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__1(lean_object* v_val_3131_, lean_object* v_cfg_3132_){
_start:
{
lean_object* v_toWorkspaceConfig_3133_; lean_object* v_toLeanConfig_3134_; uint8_t v_bootstrap_3135_; lean_object* v_extraDepTargets_3136_; uint8_t v_precompileModules_3137_; lean_object* v_moreGlobalServerArgs_3138_; lean_object* v_srcDir_3139_; lean_object* v_buildDir_3140_; lean_object* v_leanLibDir_3141_; lean_object* v_nativeLibDir_3142_; lean_object* v_binDir_3143_; lean_object* v_irDir_3144_; lean_object* v_releaseRepo_3145_; lean_object* v_buildArchive_3146_; uint8_t v_preferReleaseBuild_3147_; lean_object* v_testDriver_3148_; lean_object* v_testDriverArgs_3149_; lean_object* v_lintDriver_3150_; lean_object* v_lintDriverArgs_3151_; lean_object* v_version_3152_; lean_object* v_versionTags_3153_; lean_object* v_description_3154_; lean_object* v_keywords_3155_; lean_object* v_homepage_3156_; lean_object* v_license_3157_; lean_object* v_licenseFiles_3158_; uint8_t v_reservoir_3159_; lean_object* v_enableArtifactCache_x3f_3160_; lean_object* v_restoreAllArtifacts_x3f_3161_; uint8_t v_libPrefixOnWindows_3162_; uint8_t v_allowImportAll_3163_; lean_object* v_builtinLint_x3f_3164_; lean_object* v_checks_3165_; uint8_t v_fixedToolchain_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
v_toWorkspaceConfig_3133_ = lean_ctor_get(v_cfg_3132_, 0);
v_toLeanConfig_3134_ = lean_ctor_get(v_cfg_3132_, 1);
v_bootstrap_3135_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*28);
v_extraDepTargets_3136_ = lean_ctor_get(v_cfg_3132_, 2);
v_precompileModules_3137_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3138_ = lean_ctor_get(v_cfg_3132_, 3);
v_srcDir_3139_ = lean_ctor_get(v_cfg_3132_, 4);
v_buildDir_3140_ = lean_ctor_get(v_cfg_3132_, 5);
v_leanLibDir_3141_ = lean_ctor_get(v_cfg_3132_, 6);
v_nativeLibDir_3142_ = lean_ctor_get(v_cfg_3132_, 7);
v_binDir_3143_ = lean_ctor_get(v_cfg_3132_, 8);
v_irDir_3144_ = lean_ctor_get(v_cfg_3132_, 9);
v_releaseRepo_3145_ = lean_ctor_get(v_cfg_3132_, 10);
v_buildArchive_3146_ = lean_ctor_get(v_cfg_3132_, 11);
v_preferReleaseBuild_3147_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*28 + 2);
v_testDriver_3148_ = lean_ctor_get(v_cfg_3132_, 12);
v_testDriverArgs_3149_ = lean_ctor_get(v_cfg_3132_, 13);
v_lintDriver_3150_ = lean_ctor_get(v_cfg_3132_, 14);
v_lintDriverArgs_3151_ = lean_ctor_get(v_cfg_3132_, 15);
v_version_3152_ = lean_ctor_get(v_cfg_3132_, 16);
v_versionTags_3153_ = lean_ctor_get(v_cfg_3132_, 17);
v_description_3154_ = lean_ctor_get(v_cfg_3132_, 18);
v_keywords_3155_ = lean_ctor_get(v_cfg_3132_, 19);
v_homepage_3156_ = lean_ctor_get(v_cfg_3132_, 20);
v_license_3157_ = lean_ctor_get(v_cfg_3132_, 21);
v_licenseFiles_3158_ = lean_ctor_get(v_cfg_3132_, 22);
v_reservoir_3159_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3160_ = lean_ctor_get(v_cfg_3132_, 24);
v_restoreAllArtifacts_x3f_3161_ = lean_ctor_get(v_cfg_3132_, 25);
v_libPrefixOnWindows_3162_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*28 + 4);
v_allowImportAll_3163_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3164_ = lean_ctor_get(v_cfg_3132_, 26);
v_checks_3165_ = lean_ctor_get(v_cfg_3132_, 27);
v_fixedToolchain_3166_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*28 + 6);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_cfg_3132_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v_cfg_3132_, 23);
lean_dec(v_unused_3174_);
v___x_3168_ = v_cfg_3132_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_checks_3165_);
lean_inc(v_builtinLint_x3f_3164_);
lean_inc(v_restoreAllArtifacts_x3f_3161_);
lean_inc(v_enableArtifactCache_x3f_3160_);
lean_inc(v_licenseFiles_3158_);
lean_inc(v_license_3157_);
lean_inc(v_homepage_3156_);
lean_inc(v_keywords_3155_);
lean_inc(v_description_3154_);
lean_inc(v_versionTags_3153_);
lean_inc(v_version_3152_);
lean_inc(v_lintDriverArgs_3151_);
lean_inc(v_lintDriver_3150_);
lean_inc(v_testDriverArgs_3149_);
lean_inc(v_testDriver_3148_);
lean_inc(v_buildArchive_3146_);
lean_inc(v_releaseRepo_3145_);
lean_inc(v_irDir_3144_);
lean_inc(v_binDir_3143_);
lean_inc(v_nativeLibDir_3142_);
lean_inc(v_leanLibDir_3141_);
lean_inc(v_buildDir_3140_);
lean_inc(v_srcDir_3139_);
lean_inc(v_moreGlobalServerArgs_3138_);
lean_inc(v_extraDepTargets_3136_);
lean_inc(v_toLeanConfig_3134_);
lean_inc(v_toWorkspaceConfig_3133_);
lean_dec(v_cfg_3132_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 23, v_val_3131_);
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_toWorkspaceConfig_3133_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_toLeanConfig_3134_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_extraDepTargets_3136_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_moreGlobalServerArgs_3138_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v_srcDir_3139_);
lean_ctor_set(v_reuseFailAlloc_3172_, 5, v_buildDir_3140_);
lean_ctor_set(v_reuseFailAlloc_3172_, 6, v_leanLibDir_3141_);
lean_ctor_set(v_reuseFailAlloc_3172_, 7, v_nativeLibDir_3142_);
lean_ctor_set(v_reuseFailAlloc_3172_, 8, v_binDir_3143_);
lean_ctor_set(v_reuseFailAlloc_3172_, 9, v_irDir_3144_);
lean_ctor_set(v_reuseFailAlloc_3172_, 10, v_releaseRepo_3145_);
lean_ctor_set(v_reuseFailAlloc_3172_, 11, v_buildArchive_3146_);
lean_ctor_set(v_reuseFailAlloc_3172_, 12, v_testDriver_3148_);
lean_ctor_set(v_reuseFailAlloc_3172_, 13, v_testDriverArgs_3149_);
lean_ctor_set(v_reuseFailAlloc_3172_, 14, v_lintDriver_3150_);
lean_ctor_set(v_reuseFailAlloc_3172_, 15, v_lintDriverArgs_3151_);
lean_ctor_set(v_reuseFailAlloc_3172_, 16, v_version_3152_);
lean_ctor_set(v_reuseFailAlloc_3172_, 17, v_versionTags_3153_);
lean_ctor_set(v_reuseFailAlloc_3172_, 18, v_description_3154_);
lean_ctor_set(v_reuseFailAlloc_3172_, 19, v_keywords_3155_);
lean_ctor_set(v_reuseFailAlloc_3172_, 20, v_homepage_3156_);
lean_ctor_set(v_reuseFailAlloc_3172_, 21, v_license_3157_);
lean_ctor_set(v_reuseFailAlloc_3172_, 22, v_licenseFiles_3158_);
lean_ctor_set(v_reuseFailAlloc_3172_, 23, v_val_3131_);
lean_ctor_set(v_reuseFailAlloc_3172_, 24, v_enableArtifactCache_x3f_3160_);
lean_ctor_set(v_reuseFailAlloc_3172_, 25, v_restoreAllArtifacts_x3f_3161_);
lean_ctor_set(v_reuseFailAlloc_3172_, 26, v_builtinLint_x3f_3164_);
lean_ctor_set(v_reuseFailAlloc_3172_, 27, v_checks_3165_);
lean_ctor_set_uint8(v_reuseFailAlloc_3172_, sizeof(void*)*28, v_bootstrap_3135_);
lean_ctor_set_uint8(v_reuseFailAlloc_3172_, sizeof(void*)*28 + 1, v_precompileModules_3137_);
lean_ctor_set_uint8(v_reuseFailAlloc_3172_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3147_);
lean_ctor_set_uint8(v_reuseFailAlloc_3172_, sizeof(void*)*28 + 3, v_reservoir_3159_);
lean_ctor_set_uint8(v_reuseFailAlloc_3172_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3162_);
lean_ctor_set_uint8(v_reuseFailAlloc_3172_, sizeof(void*)*28 + 5, v_allowImportAll_3163_);
lean_ctor_set_uint8(v_reuseFailAlloc_3172_, sizeof(void*)*28 + 6, v_fixedToolchain_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__2(lean_object* v_f_3175_, lean_object* v_cfg_3176_){
_start:
{
lean_object* v_toWorkspaceConfig_3177_; lean_object* v_toLeanConfig_3178_; uint8_t v_bootstrap_3179_; lean_object* v_extraDepTargets_3180_; uint8_t v_precompileModules_3181_; lean_object* v_moreGlobalServerArgs_3182_; lean_object* v_srcDir_3183_; lean_object* v_buildDir_3184_; lean_object* v_leanLibDir_3185_; lean_object* v_nativeLibDir_3186_; lean_object* v_binDir_3187_; lean_object* v_irDir_3188_; lean_object* v_releaseRepo_3189_; lean_object* v_buildArchive_3190_; uint8_t v_preferReleaseBuild_3191_; lean_object* v_testDriver_3192_; lean_object* v_testDriverArgs_3193_; lean_object* v_lintDriver_3194_; lean_object* v_lintDriverArgs_3195_; lean_object* v_version_3196_; lean_object* v_versionTags_3197_; lean_object* v_description_3198_; lean_object* v_keywords_3199_; lean_object* v_homepage_3200_; lean_object* v_license_3201_; lean_object* v_licenseFiles_3202_; lean_object* v_readmeFile_3203_; uint8_t v_reservoir_3204_; lean_object* v_enableArtifactCache_x3f_3205_; lean_object* v_restoreAllArtifacts_x3f_3206_; uint8_t v_libPrefixOnWindows_3207_; uint8_t v_allowImportAll_3208_; lean_object* v_builtinLint_x3f_3209_; lean_object* v_checks_3210_; uint8_t v_fixedToolchain_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3219_; 
v_toWorkspaceConfig_3177_ = lean_ctor_get(v_cfg_3176_, 0);
v_toLeanConfig_3178_ = lean_ctor_get(v_cfg_3176_, 1);
v_bootstrap_3179_ = lean_ctor_get_uint8(v_cfg_3176_, sizeof(void*)*28);
v_extraDepTargets_3180_ = lean_ctor_get(v_cfg_3176_, 2);
v_precompileModules_3181_ = lean_ctor_get_uint8(v_cfg_3176_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3182_ = lean_ctor_get(v_cfg_3176_, 3);
v_srcDir_3183_ = lean_ctor_get(v_cfg_3176_, 4);
v_buildDir_3184_ = lean_ctor_get(v_cfg_3176_, 5);
v_leanLibDir_3185_ = lean_ctor_get(v_cfg_3176_, 6);
v_nativeLibDir_3186_ = lean_ctor_get(v_cfg_3176_, 7);
v_binDir_3187_ = lean_ctor_get(v_cfg_3176_, 8);
v_irDir_3188_ = lean_ctor_get(v_cfg_3176_, 9);
v_releaseRepo_3189_ = lean_ctor_get(v_cfg_3176_, 10);
v_buildArchive_3190_ = lean_ctor_get(v_cfg_3176_, 11);
v_preferReleaseBuild_3191_ = lean_ctor_get_uint8(v_cfg_3176_, sizeof(void*)*28 + 2);
v_testDriver_3192_ = lean_ctor_get(v_cfg_3176_, 12);
v_testDriverArgs_3193_ = lean_ctor_get(v_cfg_3176_, 13);
v_lintDriver_3194_ = lean_ctor_get(v_cfg_3176_, 14);
v_lintDriverArgs_3195_ = lean_ctor_get(v_cfg_3176_, 15);
v_version_3196_ = lean_ctor_get(v_cfg_3176_, 16);
v_versionTags_3197_ = lean_ctor_get(v_cfg_3176_, 17);
v_description_3198_ = lean_ctor_get(v_cfg_3176_, 18);
v_keywords_3199_ = lean_ctor_get(v_cfg_3176_, 19);
v_homepage_3200_ = lean_ctor_get(v_cfg_3176_, 20);
v_license_3201_ = lean_ctor_get(v_cfg_3176_, 21);
v_licenseFiles_3202_ = lean_ctor_get(v_cfg_3176_, 22);
v_readmeFile_3203_ = lean_ctor_get(v_cfg_3176_, 23);
v_reservoir_3204_ = lean_ctor_get_uint8(v_cfg_3176_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3205_ = lean_ctor_get(v_cfg_3176_, 24);
v_restoreAllArtifacts_x3f_3206_ = lean_ctor_get(v_cfg_3176_, 25);
v_libPrefixOnWindows_3207_ = lean_ctor_get_uint8(v_cfg_3176_, sizeof(void*)*28 + 4);
v_allowImportAll_3208_ = lean_ctor_get_uint8(v_cfg_3176_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3209_ = lean_ctor_get(v_cfg_3176_, 26);
v_checks_3210_ = lean_ctor_get(v_cfg_3176_, 27);
v_fixedToolchain_3211_ = lean_ctor_get_uint8(v_cfg_3176_, sizeof(void*)*28 + 6);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_cfg_3176_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3213_ = v_cfg_3176_;
v_isShared_3214_ = v_isSharedCheck_3219_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_checks_3210_);
lean_inc(v_builtinLint_x3f_3209_);
lean_inc(v_restoreAllArtifacts_x3f_3206_);
lean_inc(v_enableArtifactCache_x3f_3205_);
lean_inc(v_readmeFile_3203_);
lean_inc(v_licenseFiles_3202_);
lean_inc(v_license_3201_);
lean_inc(v_homepage_3200_);
lean_inc(v_keywords_3199_);
lean_inc(v_description_3198_);
lean_inc(v_versionTags_3197_);
lean_inc(v_version_3196_);
lean_inc(v_lintDriverArgs_3195_);
lean_inc(v_lintDriver_3194_);
lean_inc(v_testDriverArgs_3193_);
lean_inc(v_testDriver_3192_);
lean_inc(v_buildArchive_3190_);
lean_inc(v_releaseRepo_3189_);
lean_inc(v_irDir_3188_);
lean_inc(v_binDir_3187_);
lean_inc(v_nativeLibDir_3186_);
lean_inc(v_leanLibDir_3185_);
lean_inc(v_buildDir_3184_);
lean_inc(v_srcDir_3183_);
lean_inc(v_moreGlobalServerArgs_3182_);
lean_inc(v_extraDepTargets_3180_);
lean_inc(v_toLeanConfig_3178_);
lean_inc(v_toWorkspaceConfig_3177_);
lean_dec(v_cfg_3176_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3219_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3215_ = lean_apply_1(v_f_3175_, v_readmeFile_3203_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 23, v___x_3215_);
v___x_3217_ = v___x_3213_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_toWorkspaceConfig_3177_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_toLeanConfig_3178_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_extraDepTargets_3180_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_moreGlobalServerArgs_3182_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v_srcDir_3183_);
lean_ctor_set(v_reuseFailAlloc_3218_, 5, v_buildDir_3184_);
lean_ctor_set(v_reuseFailAlloc_3218_, 6, v_leanLibDir_3185_);
lean_ctor_set(v_reuseFailAlloc_3218_, 7, v_nativeLibDir_3186_);
lean_ctor_set(v_reuseFailAlloc_3218_, 8, v_binDir_3187_);
lean_ctor_set(v_reuseFailAlloc_3218_, 9, v_irDir_3188_);
lean_ctor_set(v_reuseFailAlloc_3218_, 10, v_releaseRepo_3189_);
lean_ctor_set(v_reuseFailAlloc_3218_, 11, v_buildArchive_3190_);
lean_ctor_set(v_reuseFailAlloc_3218_, 12, v_testDriver_3192_);
lean_ctor_set(v_reuseFailAlloc_3218_, 13, v_testDriverArgs_3193_);
lean_ctor_set(v_reuseFailAlloc_3218_, 14, v_lintDriver_3194_);
lean_ctor_set(v_reuseFailAlloc_3218_, 15, v_lintDriverArgs_3195_);
lean_ctor_set(v_reuseFailAlloc_3218_, 16, v_version_3196_);
lean_ctor_set(v_reuseFailAlloc_3218_, 17, v_versionTags_3197_);
lean_ctor_set(v_reuseFailAlloc_3218_, 18, v_description_3198_);
lean_ctor_set(v_reuseFailAlloc_3218_, 19, v_keywords_3199_);
lean_ctor_set(v_reuseFailAlloc_3218_, 20, v_homepage_3200_);
lean_ctor_set(v_reuseFailAlloc_3218_, 21, v_license_3201_);
lean_ctor_set(v_reuseFailAlloc_3218_, 22, v_licenseFiles_3202_);
lean_ctor_set(v_reuseFailAlloc_3218_, 23, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3218_, 24, v_enableArtifactCache_x3f_3205_);
lean_ctor_set(v_reuseFailAlloc_3218_, 25, v_restoreAllArtifacts_x3f_3206_);
lean_ctor_set(v_reuseFailAlloc_3218_, 26, v_builtinLint_x3f_3209_);
lean_ctor_set(v_reuseFailAlloc_3218_, 27, v_checks_3210_);
lean_ctor_set_uint8(v_reuseFailAlloc_3218_, sizeof(void*)*28, v_bootstrap_3179_);
lean_ctor_set_uint8(v_reuseFailAlloc_3218_, sizeof(void*)*28 + 1, v_precompileModules_3181_);
lean_ctor_set_uint8(v_reuseFailAlloc_3218_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3191_);
lean_ctor_set_uint8(v_reuseFailAlloc_3218_, sizeof(void*)*28 + 3, v_reservoir_3204_);
lean_ctor_set_uint8(v_reuseFailAlloc_3218_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3207_);
lean_ctor_set_uint8(v_reuseFailAlloc_3218_, sizeof(void*)*28 + 5, v_allowImportAll_3208_);
lean_ctor_set_uint8(v_reuseFailAlloc_3218_, sizeof(void*)*28 + 6, v_fixedToolchain_3211_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3(lean_object* v_x_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__7));
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3___boxed(lean_object* v_x_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3(v_x_3222_);
lean_dec_ref(v_x_3222_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg(){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___redArg___closed__4));
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___boxed(lean_object* v___dummy_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Lake_PackageConfig_readmeFile___proj___redArg();
return v_res_3236_;
}
}
static lean_object* _init_l_Lake_PackageConfig_readmeFile___proj___closed__0(void){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lake_PackageConfig_readmeFile___proj___redArg();
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object* v_p_3238_, lean_object* v_n_3239_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = lean_obj_once(&l_Lake_PackageConfig_readmeFile___proj___closed__0, &l_Lake_PackageConfig_readmeFile___proj___closed__0_once, _init_l_Lake_PackageConfig_readmeFile___proj___closed__0);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object* v_p_3241_, lean_object* v_n_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lake_PackageConfig_readmeFile___proj(v_p_3241_, v_n_3242_);
lean_dec(v_n_3242_);
lean_dec(v_p_3241_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___redArg(){
_start:
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_obj_once(&l_Lake_PackageConfig_readmeFile___proj___closed__0, &l_Lake_PackageConfig_readmeFile___proj___closed__0_once, _init_l_Lake_PackageConfig_readmeFile___proj___closed__0);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___redArg___boxed(lean_object* v___dummy_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lake_PackageConfig_readmeFile_instConfigField___redArg();
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object* v_p_3248_, lean_object* v_n_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_obj_once(&l_Lake_PackageConfig_readmeFile___proj___closed__0, &l_Lake_PackageConfig_readmeFile___proj___closed__0_once, _init_l_Lake_PackageConfig_readmeFile___proj___closed__0);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object* v_p_3251_, lean_object* v_n_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lake_PackageConfig_readmeFile_instConfigField(v_p_3251_, v_n_3252_);
lean_dec(v_n_3252_);
lean_dec(v_p_3251_);
return v_res_3253_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___redArg___lam__0(lean_object* v_cfg_3254_){
_start:
{
uint8_t v_reservoir_3255_; 
v_reservoir_3255_ = lean_ctor_get_uint8(v_cfg_3254_, sizeof(void*)*28 + 3);
return v_reservoir_3255_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__0___boxed(lean_object* v_cfg_3256_){
_start:
{
uint8_t v_res_3257_; lean_object* v_r_3258_; 
v_res_3257_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__0(v_cfg_3256_);
lean_dec_ref(v_cfg_3256_);
v_r_3258_ = lean_box(v_res_3257_);
return v_r_3258_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__1(uint8_t v_val_3259_, lean_object* v_cfg_3260_){
_start:
{
lean_object* v_toWorkspaceConfig_3261_; lean_object* v_toLeanConfig_3262_; uint8_t v_bootstrap_3263_; lean_object* v_extraDepTargets_3264_; uint8_t v_precompileModules_3265_; lean_object* v_moreGlobalServerArgs_3266_; lean_object* v_srcDir_3267_; lean_object* v_buildDir_3268_; lean_object* v_leanLibDir_3269_; lean_object* v_nativeLibDir_3270_; lean_object* v_binDir_3271_; lean_object* v_irDir_3272_; lean_object* v_releaseRepo_3273_; lean_object* v_buildArchive_3274_; uint8_t v_preferReleaseBuild_3275_; lean_object* v_testDriver_3276_; lean_object* v_testDriverArgs_3277_; lean_object* v_lintDriver_3278_; lean_object* v_lintDriverArgs_3279_; lean_object* v_version_3280_; lean_object* v_versionTags_3281_; lean_object* v_description_3282_; lean_object* v_keywords_3283_; lean_object* v_homepage_3284_; lean_object* v_license_3285_; lean_object* v_licenseFiles_3286_; lean_object* v_readmeFile_3287_; lean_object* v_enableArtifactCache_x3f_3288_; lean_object* v_restoreAllArtifacts_x3f_3289_; uint8_t v_libPrefixOnWindows_3290_; uint8_t v_allowImportAll_3291_; lean_object* v_builtinLint_x3f_3292_; lean_object* v_checks_3293_; uint8_t v_fixedToolchain_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
v_toWorkspaceConfig_3261_ = lean_ctor_get(v_cfg_3260_, 0);
v_toLeanConfig_3262_ = lean_ctor_get(v_cfg_3260_, 1);
v_bootstrap_3263_ = lean_ctor_get_uint8(v_cfg_3260_, sizeof(void*)*28);
v_extraDepTargets_3264_ = lean_ctor_get(v_cfg_3260_, 2);
v_precompileModules_3265_ = lean_ctor_get_uint8(v_cfg_3260_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3266_ = lean_ctor_get(v_cfg_3260_, 3);
v_srcDir_3267_ = lean_ctor_get(v_cfg_3260_, 4);
v_buildDir_3268_ = lean_ctor_get(v_cfg_3260_, 5);
v_leanLibDir_3269_ = lean_ctor_get(v_cfg_3260_, 6);
v_nativeLibDir_3270_ = lean_ctor_get(v_cfg_3260_, 7);
v_binDir_3271_ = lean_ctor_get(v_cfg_3260_, 8);
v_irDir_3272_ = lean_ctor_get(v_cfg_3260_, 9);
v_releaseRepo_3273_ = lean_ctor_get(v_cfg_3260_, 10);
v_buildArchive_3274_ = lean_ctor_get(v_cfg_3260_, 11);
v_preferReleaseBuild_3275_ = lean_ctor_get_uint8(v_cfg_3260_, sizeof(void*)*28 + 2);
v_testDriver_3276_ = lean_ctor_get(v_cfg_3260_, 12);
v_testDriverArgs_3277_ = lean_ctor_get(v_cfg_3260_, 13);
v_lintDriver_3278_ = lean_ctor_get(v_cfg_3260_, 14);
v_lintDriverArgs_3279_ = lean_ctor_get(v_cfg_3260_, 15);
v_version_3280_ = lean_ctor_get(v_cfg_3260_, 16);
v_versionTags_3281_ = lean_ctor_get(v_cfg_3260_, 17);
v_description_3282_ = lean_ctor_get(v_cfg_3260_, 18);
v_keywords_3283_ = lean_ctor_get(v_cfg_3260_, 19);
v_homepage_3284_ = lean_ctor_get(v_cfg_3260_, 20);
v_license_3285_ = lean_ctor_get(v_cfg_3260_, 21);
v_licenseFiles_3286_ = lean_ctor_get(v_cfg_3260_, 22);
v_readmeFile_3287_ = lean_ctor_get(v_cfg_3260_, 23);
v_enableArtifactCache_x3f_3288_ = lean_ctor_get(v_cfg_3260_, 24);
v_restoreAllArtifacts_x3f_3289_ = lean_ctor_get(v_cfg_3260_, 25);
v_libPrefixOnWindows_3290_ = lean_ctor_get_uint8(v_cfg_3260_, sizeof(void*)*28 + 4);
v_allowImportAll_3291_ = lean_ctor_get_uint8(v_cfg_3260_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3292_ = lean_ctor_get(v_cfg_3260_, 26);
v_checks_3293_ = lean_ctor_get(v_cfg_3260_, 27);
v_fixedToolchain_3294_ = lean_ctor_get_uint8(v_cfg_3260_, sizeof(void*)*28 + 6);
v_isSharedCheck_3301_ = !lean_is_exclusive(v_cfg_3260_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v_cfg_3260_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_checks_3293_);
lean_inc(v_builtinLint_x3f_3292_);
lean_inc(v_restoreAllArtifacts_x3f_3289_);
lean_inc(v_enableArtifactCache_x3f_3288_);
lean_inc(v_readmeFile_3287_);
lean_inc(v_licenseFiles_3286_);
lean_inc(v_license_3285_);
lean_inc(v_homepage_3284_);
lean_inc(v_keywords_3283_);
lean_inc(v_description_3282_);
lean_inc(v_versionTags_3281_);
lean_inc(v_version_3280_);
lean_inc(v_lintDriverArgs_3279_);
lean_inc(v_lintDriver_3278_);
lean_inc(v_testDriverArgs_3277_);
lean_inc(v_testDriver_3276_);
lean_inc(v_buildArchive_3274_);
lean_inc(v_releaseRepo_3273_);
lean_inc(v_irDir_3272_);
lean_inc(v_binDir_3271_);
lean_inc(v_nativeLibDir_3270_);
lean_inc(v_leanLibDir_3269_);
lean_inc(v_buildDir_3268_);
lean_inc(v_srcDir_3267_);
lean_inc(v_moreGlobalServerArgs_3266_);
lean_inc(v_extraDepTargets_3264_);
lean_inc(v_toLeanConfig_3262_);
lean_inc(v_toWorkspaceConfig_3261_);
lean_dec(v_cfg_3260_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_toWorkspaceConfig_3261_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_toLeanConfig_3262_);
lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_extraDepTargets_3264_);
lean_ctor_set(v_reuseFailAlloc_3300_, 3, v_moreGlobalServerArgs_3266_);
lean_ctor_set(v_reuseFailAlloc_3300_, 4, v_srcDir_3267_);
lean_ctor_set(v_reuseFailAlloc_3300_, 5, v_buildDir_3268_);
lean_ctor_set(v_reuseFailAlloc_3300_, 6, v_leanLibDir_3269_);
lean_ctor_set(v_reuseFailAlloc_3300_, 7, v_nativeLibDir_3270_);
lean_ctor_set(v_reuseFailAlloc_3300_, 8, v_binDir_3271_);
lean_ctor_set(v_reuseFailAlloc_3300_, 9, v_irDir_3272_);
lean_ctor_set(v_reuseFailAlloc_3300_, 10, v_releaseRepo_3273_);
lean_ctor_set(v_reuseFailAlloc_3300_, 11, v_buildArchive_3274_);
lean_ctor_set(v_reuseFailAlloc_3300_, 12, v_testDriver_3276_);
lean_ctor_set(v_reuseFailAlloc_3300_, 13, v_testDriverArgs_3277_);
lean_ctor_set(v_reuseFailAlloc_3300_, 14, v_lintDriver_3278_);
lean_ctor_set(v_reuseFailAlloc_3300_, 15, v_lintDriverArgs_3279_);
lean_ctor_set(v_reuseFailAlloc_3300_, 16, v_version_3280_);
lean_ctor_set(v_reuseFailAlloc_3300_, 17, v_versionTags_3281_);
lean_ctor_set(v_reuseFailAlloc_3300_, 18, v_description_3282_);
lean_ctor_set(v_reuseFailAlloc_3300_, 19, v_keywords_3283_);
lean_ctor_set(v_reuseFailAlloc_3300_, 20, v_homepage_3284_);
lean_ctor_set(v_reuseFailAlloc_3300_, 21, v_license_3285_);
lean_ctor_set(v_reuseFailAlloc_3300_, 22, v_licenseFiles_3286_);
lean_ctor_set(v_reuseFailAlloc_3300_, 23, v_readmeFile_3287_);
lean_ctor_set(v_reuseFailAlloc_3300_, 24, v_enableArtifactCache_x3f_3288_);
lean_ctor_set(v_reuseFailAlloc_3300_, 25, v_restoreAllArtifacts_x3f_3289_);
lean_ctor_set(v_reuseFailAlloc_3300_, 26, v_builtinLint_x3f_3292_);
lean_ctor_set(v_reuseFailAlloc_3300_, 27, v_checks_3293_);
lean_ctor_set_uint8(v_reuseFailAlloc_3300_, sizeof(void*)*28, v_bootstrap_3263_);
lean_ctor_set_uint8(v_reuseFailAlloc_3300_, sizeof(void*)*28 + 1, v_precompileModules_3265_);
lean_ctor_set_uint8(v_reuseFailAlloc_3300_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3275_);
lean_ctor_set_uint8(v_reuseFailAlloc_3300_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3290_);
lean_ctor_set_uint8(v_reuseFailAlloc_3300_, sizeof(void*)*28 + 5, v_allowImportAll_3291_);
lean_ctor_set_uint8(v_reuseFailAlloc_3300_, sizeof(void*)*28 + 6, v_fixedToolchain_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_ctor_set_uint8(v___x_3299_, sizeof(void*)*28 + 3, v_val_3259_);
return v___x_3299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__1___boxed(lean_object* v_val_3302_, lean_object* v_cfg_3303_){
_start:
{
uint8_t v_val_141__boxed_3304_; lean_object* v_res_3305_; 
v_val_141__boxed_3304_ = lean_unbox(v_val_3302_);
v_res_3305_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__1(v_val_141__boxed_3304_, v_cfg_3303_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__2(lean_object* v_f_3306_, lean_object* v_cfg_3307_){
_start:
{
lean_object* v_toWorkspaceConfig_3308_; lean_object* v_toLeanConfig_3309_; uint8_t v_bootstrap_3310_; lean_object* v_extraDepTargets_3311_; uint8_t v_precompileModules_3312_; lean_object* v_moreGlobalServerArgs_3313_; lean_object* v_srcDir_3314_; lean_object* v_buildDir_3315_; lean_object* v_leanLibDir_3316_; lean_object* v_nativeLibDir_3317_; lean_object* v_binDir_3318_; lean_object* v_irDir_3319_; lean_object* v_releaseRepo_3320_; lean_object* v_buildArchive_3321_; uint8_t v_preferReleaseBuild_3322_; lean_object* v_testDriver_3323_; lean_object* v_testDriverArgs_3324_; lean_object* v_lintDriver_3325_; lean_object* v_lintDriverArgs_3326_; lean_object* v_version_3327_; lean_object* v_versionTags_3328_; lean_object* v_description_3329_; lean_object* v_keywords_3330_; lean_object* v_homepage_3331_; lean_object* v_license_3332_; lean_object* v_licenseFiles_3333_; lean_object* v_readmeFile_3334_; uint8_t v_reservoir_3335_; lean_object* v_enableArtifactCache_x3f_3336_; lean_object* v_restoreAllArtifacts_x3f_3337_; uint8_t v_libPrefixOnWindows_3338_; uint8_t v_allowImportAll_3339_; lean_object* v_builtinLint_x3f_3340_; lean_object* v_checks_3341_; uint8_t v_fixedToolchain_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3352_; 
v_toWorkspaceConfig_3308_ = lean_ctor_get(v_cfg_3307_, 0);
v_toLeanConfig_3309_ = lean_ctor_get(v_cfg_3307_, 1);
v_bootstrap_3310_ = lean_ctor_get_uint8(v_cfg_3307_, sizeof(void*)*28);
v_extraDepTargets_3311_ = lean_ctor_get(v_cfg_3307_, 2);
v_precompileModules_3312_ = lean_ctor_get_uint8(v_cfg_3307_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3313_ = lean_ctor_get(v_cfg_3307_, 3);
v_srcDir_3314_ = lean_ctor_get(v_cfg_3307_, 4);
v_buildDir_3315_ = lean_ctor_get(v_cfg_3307_, 5);
v_leanLibDir_3316_ = lean_ctor_get(v_cfg_3307_, 6);
v_nativeLibDir_3317_ = lean_ctor_get(v_cfg_3307_, 7);
v_binDir_3318_ = lean_ctor_get(v_cfg_3307_, 8);
v_irDir_3319_ = lean_ctor_get(v_cfg_3307_, 9);
v_releaseRepo_3320_ = lean_ctor_get(v_cfg_3307_, 10);
v_buildArchive_3321_ = lean_ctor_get(v_cfg_3307_, 11);
v_preferReleaseBuild_3322_ = lean_ctor_get_uint8(v_cfg_3307_, sizeof(void*)*28 + 2);
v_testDriver_3323_ = lean_ctor_get(v_cfg_3307_, 12);
v_testDriverArgs_3324_ = lean_ctor_get(v_cfg_3307_, 13);
v_lintDriver_3325_ = lean_ctor_get(v_cfg_3307_, 14);
v_lintDriverArgs_3326_ = lean_ctor_get(v_cfg_3307_, 15);
v_version_3327_ = lean_ctor_get(v_cfg_3307_, 16);
v_versionTags_3328_ = lean_ctor_get(v_cfg_3307_, 17);
v_description_3329_ = lean_ctor_get(v_cfg_3307_, 18);
v_keywords_3330_ = lean_ctor_get(v_cfg_3307_, 19);
v_homepage_3331_ = lean_ctor_get(v_cfg_3307_, 20);
v_license_3332_ = lean_ctor_get(v_cfg_3307_, 21);
v_licenseFiles_3333_ = lean_ctor_get(v_cfg_3307_, 22);
v_readmeFile_3334_ = lean_ctor_get(v_cfg_3307_, 23);
v_reservoir_3335_ = lean_ctor_get_uint8(v_cfg_3307_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3336_ = lean_ctor_get(v_cfg_3307_, 24);
v_restoreAllArtifacts_x3f_3337_ = lean_ctor_get(v_cfg_3307_, 25);
v_libPrefixOnWindows_3338_ = lean_ctor_get_uint8(v_cfg_3307_, sizeof(void*)*28 + 4);
v_allowImportAll_3339_ = lean_ctor_get_uint8(v_cfg_3307_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3340_ = lean_ctor_get(v_cfg_3307_, 26);
v_checks_3341_ = lean_ctor_get(v_cfg_3307_, 27);
v_fixedToolchain_3342_ = lean_ctor_get_uint8(v_cfg_3307_, sizeof(void*)*28 + 6);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_cfg_3307_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3344_ = v_cfg_3307_;
v_isShared_3345_ = v_isSharedCheck_3352_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_checks_3341_);
lean_inc(v_builtinLint_x3f_3340_);
lean_inc(v_restoreAllArtifacts_x3f_3337_);
lean_inc(v_enableArtifactCache_x3f_3336_);
lean_inc(v_readmeFile_3334_);
lean_inc(v_licenseFiles_3333_);
lean_inc(v_license_3332_);
lean_inc(v_homepage_3331_);
lean_inc(v_keywords_3330_);
lean_inc(v_description_3329_);
lean_inc(v_versionTags_3328_);
lean_inc(v_version_3327_);
lean_inc(v_lintDriverArgs_3326_);
lean_inc(v_lintDriver_3325_);
lean_inc(v_testDriverArgs_3324_);
lean_inc(v_testDriver_3323_);
lean_inc(v_buildArchive_3321_);
lean_inc(v_releaseRepo_3320_);
lean_inc(v_irDir_3319_);
lean_inc(v_binDir_3318_);
lean_inc(v_nativeLibDir_3317_);
lean_inc(v_leanLibDir_3316_);
lean_inc(v_buildDir_3315_);
lean_inc(v_srcDir_3314_);
lean_inc(v_moreGlobalServerArgs_3313_);
lean_inc(v_extraDepTargets_3311_);
lean_inc(v_toLeanConfig_3309_);
lean_inc(v_toWorkspaceConfig_3308_);
lean_dec(v_cfg_3307_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3352_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3346_ = lean_box(v_reservoir_3335_);
v___x_3347_ = lean_apply_1(v_f_3306_, v___x_3346_);
if (v_isShared_3345_ == 0)
{
v___x_3349_ = v___x_3344_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_toWorkspaceConfig_3308_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_toLeanConfig_3309_);
lean_ctor_set(v_reuseFailAlloc_3351_, 2, v_extraDepTargets_3311_);
lean_ctor_set(v_reuseFailAlloc_3351_, 3, v_moreGlobalServerArgs_3313_);
lean_ctor_set(v_reuseFailAlloc_3351_, 4, v_srcDir_3314_);
lean_ctor_set(v_reuseFailAlloc_3351_, 5, v_buildDir_3315_);
lean_ctor_set(v_reuseFailAlloc_3351_, 6, v_leanLibDir_3316_);
lean_ctor_set(v_reuseFailAlloc_3351_, 7, v_nativeLibDir_3317_);
lean_ctor_set(v_reuseFailAlloc_3351_, 8, v_binDir_3318_);
lean_ctor_set(v_reuseFailAlloc_3351_, 9, v_irDir_3319_);
lean_ctor_set(v_reuseFailAlloc_3351_, 10, v_releaseRepo_3320_);
lean_ctor_set(v_reuseFailAlloc_3351_, 11, v_buildArchive_3321_);
lean_ctor_set(v_reuseFailAlloc_3351_, 12, v_testDriver_3323_);
lean_ctor_set(v_reuseFailAlloc_3351_, 13, v_testDriverArgs_3324_);
lean_ctor_set(v_reuseFailAlloc_3351_, 14, v_lintDriver_3325_);
lean_ctor_set(v_reuseFailAlloc_3351_, 15, v_lintDriverArgs_3326_);
lean_ctor_set(v_reuseFailAlloc_3351_, 16, v_version_3327_);
lean_ctor_set(v_reuseFailAlloc_3351_, 17, v_versionTags_3328_);
lean_ctor_set(v_reuseFailAlloc_3351_, 18, v_description_3329_);
lean_ctor_set(v_reuseFailAlloc_3351_, 19, v_keywords_3330_);
lean_ctor_set(v_reuseFailAlloc_3351_, 20, v_homepage_3331_);
lean_ctor_set(v_reuseFailAlloc_3351_, 21, v_license_3332_);
lean_ctor_set(v_reuseFailAlloc_3351_, 22, v_licenseFiles_3333_);
lean_ctor_set(v_reuseFailAlloc_3351_, 23, v_readmeFile_3334_);
lean_ctor_set(v_reuseFailAlloc_3351_, 24, v_enableArtifactCache_x3f_3336_);
lean_ctor_set(v_reuseFailAlloc_3351_, 25, v_restoreAllArtifacts_x3f_3337_);
lean_ctor_set(v_reuseFailAlloc_3351_, 26, v_builtinLint_x3f_3340_);
lean_ctor_set(v_reuseFailAlloc_3351_, 27, v_checks_3341_);
lean_ctor_set_uint8(v_reuseFailAlloc_3351_, sizeof(void*)*28, v_bootstrap_3310_);
lean_ctor_set_uint8(v_reuseFailAlloc_3351_, sizeof(void*)*28 + 1, v_precompileModules_3312_);
lean_ctor_set_uint8(v_reuseFailAlloc_3351_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3322_);
v___x_3349_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
uint8_t v___x_3350_; 
v___x_3350_ = lean_unbox(v___x_3347_);
lean_ctor_set_uint8(v___x_3349_, sizeof(void*)*28 + 3, v___x_3350_);
lean_ctor_set_uint8(v___x_3349_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3338_);
lean_ctor_set_uint8(v___x_3349_, sizeof(void*)*28 + 5, v_allowImportAll_3339_);
lean_ctor_set_uint8(v___x_3349_, sizeof(void*)*28 + 6, v_fixedToolchain_3342_);
return v___x_3349_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___redArg___lam__3(lean_object* v_x_3353_){
_start:
{
uint8_t v___x_3354_; 
v___x_3354_ = 1;
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__3___boxed(lean_object* v_x_3355_){
_start:
{
uint8_t v_res_3356_; lean_object* v_r_3357_; 
v_res_3356_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__3(v_x_3355_);
lean_dec_ref(v_x_3355_);
v_r_3357_ = lean_box(v_res_3356_);
return v_r_3357_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg(){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = ((lean_object*)(l_Lake_PackageConfig_reservoir___proj___redArg___closed__4));
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___boxed(lean_object* v___dummy_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lake_PackageConfig_reservoir___proj___redArg();
return v_res_3370_;
}
}
static lean_object* _init_l_Lake_PackageConfig_reservoir___proj___closed__0(void){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lake_PackageConfig_reservoir___proj___redArg();
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object* v_p_3372_, lean_object* v_n_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_obj_once(&l_Lake_PackageConfig_reservoir___proj___closed__0, &l_Lake_PackageConfig_reservoir___proj___closed__0_once, _init_l_Lake_PackageConfig_reservoir___proj___closed__0);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object* v_p_3375_, lean_object* v_n_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lake_PackageConfig_reservoir___proj(v_p_3375_, v_n_3376_);
lean_dec(v_n_3376_);
lean_dec(v_p_3375_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___redArg(){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_obj_once(&l_Lake_PackageConfig_reservoir___proj___closed__0, &l_Lake_PackageConfig_reservoir___proj___closed__0_once, _init_l_Lake_PackageConfig_reservoir___proj___closed__0);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___redArg___boxed(lean_object* v___dummy_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lake_PackageConfig_reservoir_instConfigField___redArg();
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object* v_p_3382_, lean_object* v_n_3383_){
_start:
{
lean_object* v___x_3384_; 
v___x_3384_ = lean_obj_once(&l_Lake_PackageConfig_reservoir___proj___closed__0, &l_Lake_PackageConfig_reservoir___proj___closed__0_once, _init_l_Lake_PackageConfig_reservoir___proj___closed__0);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object* v_p_3385_, lean_object* v_n_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lake_PackageConfig_reservoir_instConfigField(v_p_3385_, v_n_3386_);
lean_dec(v_n_3386_);
lean_dec(v_p_3385_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0(lean_object* v_cfg_3388_){
_start:
{
lean_object* v_enableArtifactCache_x3f_3389_; 
v_enableArtifactCache_x3f_3389_ = lean_ctor_get(v_cfg_3388_, 24);
lean_inc(v_enableArtifactCache_x3f_3389_);
return v_enableArtifactCache_x3f_3389_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0___boxed(lean_object* v_cfg_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0(v_cfg_3390_);
lean_dec_ref(v_cfg_3390_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__1(lean_object* v_val_3392_, lean_object* v_cfg_3393_){
_start:
{
lean_object* v_toWorkspaceConfig_3394_; lean_object* v_toLeanConfig_3395_; uint8_t v_bootstrap_3396_; lean_object* v_extraDepTargets_3397_; uint8_t v_precompileModules_3398_; lean_object* v_moreGlobalServerArgs_3399_; lean_object* v_srcDir_3400_; lean_object* v_buildDir_3401_; lean_object* v_leanLibDir_3402_; lean_object* v_nativeLibDir_3403_; lean_object* v_binDir_3404_; lean_object* v_irDir_3405_; lean_object* v_releaseRepo_3406_; lean_object* v_buildArchive_3407_; uint8_t v_preferReleaseBuild_3408_; lean_object* v_testDriver_3409_; lean_object* v_testDriverArgs_3410_; lean_object* v_lintDriver_3411_; lean_object* v_lintDriverArgs_3412_; lean_object* v_version_3413_; lean_object* v_versionTags_3414_; lean_object* v_description_3415_; lean_object* v_keywords_3416_; lean_object* v_homepage_3417_; lean_object* v_license_3418_; lean_object* v_licenseFiles_3419_; lean_object* v_readmeFile_3420_; uint8_t v_reservoir_3421_; lean_object* v_restoreAllArtifacts_x3f_3422_; uint8_t v_libPrefixOnWindows_3423_; uint8_t v_allowImportAll_3424_; lean_object* v_builtinLint_x3f_3425_; lean_object* v_checks_3426_; uint8_t v_fixedToolchain_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
v_toWorkspaceConfig_3394_ = lean_ctor_get(v_cfg_3393_, 0);
v_toLeanConfig_3395_ = lean_ctor_get(v_cfg_3393_, 1);
v_bootstrap_3396_ = lean_ctor_get_uint8(v_cfg_3393_, sizeof(void*)*28);
v_extraDepTargets_3397_ = lean_ctor_get(v_cfg_3393_, 2);
v_precompileModules_3398_ = lean_ctor_get_uint8(v_cfg_3393_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3399_ = lean_ctor_get(v_cfg_3393_, 3);
v_srcDir_3400_ = lean_ctor_get(v_cfg_3393_, 4);
v_buildDir_3401_ = lean_ctor_get(v_cfg_3393_, 5);
v_leanLibDir_3402_ = lean_ctor_get(v_cfg_3393_, 6);
v_nativeLibDir_3403_ = lean_ctor_get(v_cfg_3393_, 7);
v_binDir_3404_ = lean_ctor_get(v_cfg_3393_, 8);
v_irDir_3405_ = lean_ctor_get(v_cfg_3393_, 9);
v_releaseRepo_3406_ = lean_ctor_get(v_cfg_3393_, 10);
v_buildArchive_3407_ = lean_ctor_get(v_cfg_3393_, 11);
v_preferReleaseBuild_3408_ = lean_ctor_get_uint8(v_cfg_3393_, sizeof(void*)*28 + 2);
v_testDriver_3409_ = lean_ctor_get(v_cfg_3393_, 12);
v_testDriverArgs_3410_ = lean_ctor_get(v_cfg_3393_, 13);
v_lintDriver_3411_ = lean_ctor_get(v_cfg_3393_, 14);
v_lintDriverArgs_3412_ = lean_ctor_get(v_cfg_3393_, 15);
v_version_3413_ = lean_ctor_get(v_cfg_3393_, 16);
v_versionTags_3414_ = lean_ctor_get(v_cfg_3393_, 17);
v_description_3415_ = lean_ctor_get(v_cfg_3393_, 18);
v_keywords_3416_ = lean_ctor_get(v_cfg_3393_, 19);
v_homepage_3417_ = lean_ctor_get(v_cfg_3393_, 20);
v_license_3418_ = lean_ctor_get(v_cfg_3393_, 21);
v_licenseFiles_3419_ = lean_ctor_get(v_cfg_3393_, 22);
v_readmeFile_3420_ = lean_ctor_get(v_cfg_3393_, 23);
v_reservoir_3421_ = lean_ctor_get_uint8(v_cfg_3393_, sizeof(void*)*28 + 3);
v_restoreAllArtifacts_x3f_3422_ = lean_ctor_get(v_cfg_3393_, 25);
v_libPrefixOnWindows_3423_ = lean_ctor_get_uint8(v_cfg_3393_, sizeof(void*)*28 + 4);
v_allowImportAll_3424_ = lean_ctor_get_uint8(v_cfg_3393_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3425_ = lean_ctor_get(v_cfg_3393_, 26);
v_checks_3426_ = lean_ctor_get(v_cfg_3393_, 27);
v_fixedToolchain_3427_ = lean_ctor_get_uint8(v_cfg_3393_, sizeof(void*)*28 + 6);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_cfg_3393_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; 
v_unused_3435_ = lean_ctor_get(v_cfg_3393_, 24);
lean_dec(v_unused_3435_);
v___x_3429_ = v_cfg_3393_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_checks_3426_);
lean_inc(v_builtinLint_x3f_3425_);
lean_inc(v_restoreAllArtifacts_x3f_3422_);
lean_inc(v_readmeFile_3420_);
lean_inc(v_licenseFiles_3419_);
lean_inc(v_license_3418_);
lean_inc(v_homepage_3417_);
lean_inc(v_keywords_3416_);
lean_inc(v_description_3415_);
lean_inc(v_versionTags_3414_);
lean_inc(v_version_3413_);
lean_inc(v_lintDriverArgs_3412_);
lean_inc(v_lintDriver_3411_);
lean_inc(v_testDriverArgs_3410_);
lean_inc(v_testDriver_3409_);
lean_inc(v_buildArchive_3407_);
lean_inc(v_releaseRepo_3406_);
lean_inc(v_irDir_3405_);
lean_inc(v_binDir_3404_);
lean_inc(v_nativeLibDir_3403_);
lean_inc(v_leanLibDir_3402_);
lean_inc(v_buildDir_3401_);
lean_inc(v_srcDir_3400_);
lean_inc(v_moreGlobalServerArgs_3399_);
lean_inc(v_extraDepTargets_3397_);
lean_inc(v_toLeanConfig_3395_);
lean_inc(v_toWorkspaceConfig_3394_);
lean_dec(v_cfg_3393_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 24, v_val_3392_);
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_toWorkspaceConfig_3394_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_toLeanConfig_3395_);
lean_ctor_set(v_reuseFailAlloc_3433_, 2, v_extraDepTargets_3397_);
lean_ctor_set(v_reuseFailAlloc_3433_, 3, v_moreGlobalServerArgs_3399_);
lean_ctor_set(v_reuseFailAlloc_3433_, 4, v_srcDir_3400_);
lean_ctor_set(v_reuseFailAlloc_3433_, 5, v_buildDir_3401_);
lean_ctor_set(v_reuseFailAlloc_3433_, 6, v_leanLibDir_3402_);
lean_ctor_set(v_reuseFailAlloc_3433_, 7, v_nativeLibDir_3403_);
lean_ctor_set(v_reuseFailAlloc_3433_, 8, v_binDir_3404_);
lean_ctor_set(v_reuseFailAlloc_3433_, 9, v_irDir_3405_);
lean_ctor_set(v_reuseFailAlloc_3433_, 10, v_releaseRepo_3406_);
lean_ctor_set(v_reuseFailAlloc_3433_, 11, v_buildArchive_3407_);
lean_ctor_set(v_reuseFailAlloc_3433_, 12, v_testDriver_3409_);
lean_ctor_set(v_reuseFailAlloc_3433_, 13, v_testDriverArgs_3410_);
lean_ctor_set(v_reuseFailAlloc_3433_, 14, v_lintDriver_3411_);
lean_ctor_set(v_reuseFailAlloc_3433_, 15, v_lintDriverArgs_3412_);
lean_ctor_set(v_reuseFailAlloc_3433_, 16, v_version_3413_);
lean_ctor_set(v_reuseFailAlloc_3433_, 17, v_versionTags_3414_);
lean_ctor_set(v_reuseFailAlloc_3433_, 18, v_description_3415_);
lean_ctor_set(v_reuseFailAlloc_3433_, 19, v_keywords_3416_);
lean_ctor_set(v_reuseFailAlloc_3433_, 20, v_homepage_3417_);
lean_ctor_set(v_reuseFailAlloc_3433_, 21, v_license_3418_);
lean_ctor_set(v_reuseFailAlloc_3433_, 22, v_licenseFiles_3419_);
lean_ctor_set(v_reuseFailAlloc_3433_, 23, v_readmeFile_3420_);
lean_ctor_set(v_reuseFailAlloc_3433_, 24, v_val_3392_);
lean_ctor_set(v_reuseFailAlloc_3433_, 25, v_restoreAllArtifacts_x3f_3422_);
lean_ctor_set(v_reuseFailAlloc_3433_, 26, v_builtinLint_x3f_3425_);
lean_ctor_set(v_reuseFailAlloc_3433_, 27, v_checks_3426_);
lean_ctor_set_uint8(v_reuseFailAlloc_3433_, sizeof(void*)*28, v_bootstrap_3396_);
lean_ctor_set_uint8(v_reuseFailAlloc_3433_, sizeof(void*)*28 + 1, v_precompileModules_3398_);
lean_ctor_set_uint8(v_reuseFailAlloc_3433_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3408_);
lean_ctor_set_uint8(v_reuseFailAlloc_3433_, sizeof(void*)*28 + 3, v_reservoir_3421_);
lean_ctor_set_uint8(v_reuseFailAlloc_3433_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3423_);
lean_ctor_set_uint8(v_reuseFailAlloc_3433_, sizeof(void*)*28 + 5, v_allowImportAll_3424_);
lean_ctor_set_uint8(v_reuseFailAlloc_3433_, sizeof(void*)*28 + 6, v_fixedToolchain_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__2(lean_object* v_f_3436_, lean_object* v_cfg_3437_){
_start:
{
lean_object* v_toWorkspaceConfig_3438_; lean_object* v_toLeanConfig_3439_; uint8_t v_bootstrap_3440_; lean_object* v_extraDepTargets_3441_; uint8_t v_precompileModules_3442_; lean_object* v_moreGlobalServerArgs_3443_; lean_object* v_srcDir_3444_; lean_object* v_buildDir_3445_; lean_object* v_leanLibDir_3446_; lean_object* v_nativeLibDir_3447_; lean_object* v_binDir_3448_; lean_object* v_irDir_3449_; lean_object* v_releaseRepo_3450_; lean_object* v_buildArchive_3451_; uint8_t v_preferReleaseBuild_3452_; lean_object* v_testDriver_3453_; lean_object* v_testDriverArgs_3454_; lean_object* v_lintDriver_3455_; lean_object* v_lintDriverArgs_3456_; lean_object* v_version_3457_; lean_object* v_versionTags_3458_; lean_object* v_description_3459_; lean_object* v_keywords_3460_; lean_object* v_homepage_3461_; lean_object* v_license_3462_; lean_object* v_licenseFiles_3463_; lean_object* v_readmeFile_3464_; uint8_t v_reservoir_3465_; lean_object* v_enableArtifactCache_x3f_3466_; lean_object* v_restoreAllArtifacts_x3f_3467_; uint8_t v_libPrefixOnWindows_3468_; uint8_t v_allowImportAll_3469_; lean_object* v_builtinLint_x3f_3470_; lean_object* v_checks_3471_; uint8_t v_fixedToolchain_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3480_; 
v_toWorkspaceConfig_3438_ = lean_ctor_get(v_cfg_3437_, 0);
v_toLeanConfig_3439_ = lean_ctor_get(v_cfg_3437_, 1);
v_bootstrap_3440_ = lean_ctor_get_uint8(v_cfg_3437_, sizeof(void*)*28);
v_extraDepTargets_3441_ = lean_ctor_get(v_cfg_3437_, 2);
v_precompileModules_3442_ = lean_ctor_get_uint8(v_cfg_3437_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3443_ = lean_ctor_get(v_cfg_3437_, 3);
v_srcDir_3444_ = lean_ctor_get(v_cfg_3437_, 4);
v_buildDir_3445_ = lean_ctor_get(v_cfg_3437_, 5);
v_leanLibDir_3446_ = lean_ctor_get(v_cfg_3437_, 6);
v_nativeLibDir_3447_ = lean_ctor_get(v_cfg_3437_, 7);
v_binDir_3448_ = lean_ctor_get(v_cfg_3437_, 8);
v_irDir_3449_ = lean_ctor_get(v_cfg_3437_, 9);
v_releaseRepo_3450_ = lean_ctor_get(v_cfg_3437_, 10);
v_buildArchive_3451_ = lean_ctor_get(v_cfg_3437_, 11);
v_preferReleaseBuild_3452_ = lean_ctor_get_uint8(v_cfg_3437_, sizeof(void*)*28 + 2);
v_testDriver_3453_ = lean_ctor_get(v_cfg_3437_, 12);
v_testDriverArgs_3454_ = lean_ctor_get(v_cfg_3437_, 13);
v_lintDriver_3455_ = lean_ctor_get(v_cfg_3437_, 14);
v_lintDriverArgs_3456_ = lean_ctor_get(v_cfg_3437_, 15);
v_version_3457_ = lean_ctor_get(v_cfg_3437_, 16);
v_versionTags_3458_ = lean_ctor_get(v_cfg_3437_, 17);
v_description_3459_ = lean_ctor_get(v_cfg_3437_, 18);
v_keywords_3460_ = lean_ctor_get(v_cfg_3437_, 19);
v_homepage_3461_ = lean_ctor_get(v_cfg_3437_, 20);
v_license_3462_ = lean_ctor_get(v_cfg_3437_, 21);
v_licenseFiles_3463_ = lean_ctor_get(v_cfg_3437_, 22);
v_readmeFile_3464_ = lean_ctor_get(v_cfg_3437_, 23);
v_reservoir_3465_ = lean_ctor_get_uint8(v_cfg_3437_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3466_ = lean_ctor_get(v_cfg_3437_, 24);
v_restoreAllArtifacts_x3f_3467_ = lean_ctor_get(v_cfg_3437_, 25);
v_libPrefixOnWindows_3468_ = lean_ctor_get_uint8(v_cfg_3437_, sizeof(void*)*28 + 4);
v_allowImportAll_3469_ = lean_ctor_get_uint8(v_cfg_3437_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3470_ = lean_ctor_get(v_cfg_3437_, 26);
v_checks_3471_ = lean_ctor_get(v_cfg_3437_, 27);
v_fixedToolchain_3472_ = lean_ctor_get_uint8(v_cfg_3437_, sizeof(void*)*28 + 6);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_cfg_3437_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3474_ = v_cfg_3437_;
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_checks_3471_);
lean_inc(v_builtinLint_x3f_3470_);
lean_inc(v_restoreAllArtifacts_x3f_3467_);
lean_inc(v_enableArtifactCache_x3f_3466_);
lean_inc(v_readmeFile_3464_);
lean_inc(v_licenseFiles_3463_);
lean_inc(v_license_3462_);
lean_inc(v_homepage_3461_);
lean_inc(v_keywords_3460_);
lean_inc(v_description_3459_);
lean_inc(v_versionTags_3458_);
lean_inc(v_version_3457_);
lean_inc(v_lintDriverArgs_3456_);
lean_inc(v_lintDriver_3455_);
lean_inc(v_testDriverArgs_3454_);
lean_inc(v_testDriver_3453_);
lean_inc(v_buildArchive_3451_);
lean_inc(v_releaseRepo_3450_);
lean_inc(v_irDir_3449_);
lean_inc(v_binDir_3448_);
lean_inc(v_nativeLibDir_3447_);
lean_inc(v_leanLibDir_3446_);
lean_inc(v_buildDir_3445_);
lean_inc(v_srcDir_3444_);
lean_inc(v_moreGlobalServerArgs_3443_);
lean_inc(v_extraDepTargets_3441_);
lean_inc(v_toLeanConfig_3439_);
lean_inc(v_toWorkspaceConfig_3438_);
lean_dec(v_cfg_3437_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3476_ = lean_apply_1(v_f_3436_, v_enableArtifactCache_x3f_3466_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 24, v___x_3476_);
v___x_3478_ = v___x_3474_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_toWorkspaceConfig_3438_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_toLeanConfig_3439_);
lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_extraDepTargets_3441_);
lean_ctor_set(v_reuseFailAlloc_3479_, 3, v_moreGlobalServerArgs_3443_);
lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_srcDir_3444_);
lean_ctor_set(v_reuseFailAlloc_3479_, 5, v_buildDir_3445_);
lean_ctor_set(v_reuseFailAlloc_3479_, 6, v_leanLibDir_3446_);
lean_ctor_set(v_reuseFailAlloc_3479_, 7, v_nativeLibDir_3447_);
lean_ctor_set(v_reuseFailAlloc_3479_, 8, v_binDir_3448_);
lean_ctor_set(v_reuseFailAlloc_3479_, 9, v_irDir_3449_);
lean_ctor_set(v_reuseFailAlloc_3479_, 10, v_releaseRepo_3450_);
lean_ctor_set(v_reuseFailAlloc_3479_, 11, v_buildArchive_3451_);
lean_ctor_set(v_reuseFailAlloc_3479_, 12, v_testDriver_3453_);
lean_ctor_set(v_reuseFailAlloc_3479_, 13, v_testDriverArgs_3454_);
lean_ctor_set(v_reuseFailAlloc_3479_, 14, v_lintDriver_3455_);
lean_ctor_set(v_reuseFailAlloc_3479_, 15, v_lintDriverArgs_3456_);
lean_ctor_set(v_reuseFailAlloc_3479_, 16, v_version_3457_);
lean_ctor_set(v_reuseFailAlloc_3479_, 17, v_versionTags_3458_);
lean_ctor_set(v_reuseFailAlloc_3479_, 18, v_description_3459_);
lean_ctor_set(v_reuseFailAlloc_3479_, 19, v_keywords_3460_);
lean_ctor_set(v_reuseFailAlloc_3479_, 20, v_homepage_3461_);
lean_ctor_set(v_reuseFailAlloc_3479_, 21, v_license_3462_);
lean_ctor_set(v_reuseFailAlloc_3479_, 22, v_licenseFiles_3463_);
lean_ctor_set(v_reuseFailAlloc_3479_, 23, v_readmeFile_3464_);
lean_ctor_set(v_reuseFailAlloc_3479_, 24, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3479_, 25, v_restoreAllArtifacts_x3f_3467_);
lean_ctor_set(v_reuseFailAlloc_3479_, 26, v_builtinLint_x3f_3470_);
lean_ctor_set(v_reuseFailAlloc_3479_, 27, v_checks_3471_);
lean_ctor_set_uint8(v_reuseFailAlloc_3479_, sizeof(void*)*28, v_bootstrap_3440_);
lean_ctor_set_uint8(v_reuseFailAlloc_3479_, sizeof(void*)*28 + 1, v_precompileModules_3442_);
lean_ctor_set_uint8(v_reuseFailAlloc_3479_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3452_);
lean_ctor_set_uint8(v_reuseFailAlloc_3479_, sizeof(void*)*28 + 3, v_reservoir_3465_);
lean_ctor_set_uint8(v_reuseFailAlloc_3479_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3468_);
lean_ctor_set_uint8(v_reuseFailAlloc_3479_, sizeof(void*)*28 + 5, v_allowImportAll_3469_);
lean_ctor_set_uint8(v_reuseFailAlloc_3479_, sizeof(void*)*28 + 6, v_fixedToolchain_3472_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3(lean_object* v_x_3481_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_box(0);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3___boxed(lean_object* v_x_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3(v_x_3483_);
lean_dec_ref(v_x_3483_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg(){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = ((lean_object*)(l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__4));
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___boxed(lean_object* v___dummy_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg();
return v_res_3497_;
}
}
static lean_object* _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0(void){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg();
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object* v_p_3499_, lean_object* v_n_3500_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object* v_p_3502_, lean_object* v_n_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3502_, v_n_3503_);
lean_dec(v_n_3503_);
lean_dec(v_p_3502_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg();
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object* v_p_3509_, lean_object* v_n_3510_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object* v_p_3512_, lean_object* v_n_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(v_p_3512_, v_n_3513_);
lean_dec(v_n_3513_);
lean_dec(v_p_3512_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg(){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg___boxed(lean_object* v___dummy_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg();
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object* v_p_3519_, lean_object* v_n_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object* v_p_3522_, lean_object* v_n_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField(v_p_3522_, v_n_3523_);
lean_dec(v_n_3523_);
lean_dec(v_p_3522_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0(lean_object* v_cfg_3525_){
_start:
{
lean_object* v_restoreAllArtifacts_x3f_3526_; 
v_restoreAllArtifacts_x3f_3526_ = lean_ctor_get(v_cfg_3525_, 25);
lean_inc(v_restoreAllArtifacts_x3f_3526_);
return v_restoreAllArtifacts_x3f_3526_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0___boxed(lean_object* v_cfg_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0(v_cfg_3527_);
lean_dec_ref(v_cfg_3527_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__1(lean_object* v_val_3529_, lean_object* v_cfg_3530_){
_start:
{
lean_object* v_toWorkspaceConfig_3531_; lean_object* v_toLeanConfig_3532_; uint8_t v_bootstrap_3533_; lean_object* v_extraDepTargets_3534_; uint8_t v_precompileModules_3535_; lean_object* v_moreGlobalServerArgs_3536_; lean_object* v_srcDir_3537_; lean_object* v_buildDir_3538_; lean_object* v_leanLibDir_3539_; lean_object* v_nativeLibDir_3540_; lean_object* v_binDir_3541_; lean_object* v_irDir_3542_; lean_object* v_releaseRepo_3543_; lean_object* v_buildArchive_3544_; uint8_t v_preferReleaseBuild_3545_; lean_object* v_testDriver_3546_; lean_object* v_testDriverArgs_3547_; lean_object* v_lintDriver_3548_; lean_object* v_lintDriverArgs_3549_; lean_object* v_version_3550_; lean_object* v_versionTags_3551_; lean_object* v_description_3552_; lean_object* v_keywords_3553_; lean_object* v_homepage_3554_; lean_object* v_license_3555_; lean_object* v_licenseFiles_3556_; lean_object* v_readmeFile_3557_; uint8_t v_reservoir_3558_; lean_object* v_enableArtifactCache_x3f_3559_; uint8_t v_libPrefixOnWindows_3560_; uint8_t v_allowImportAll_3561_; lean_object* v_builtinLint_x3f_3562_; lean_object* v_checks_3563_; uint8_t v_fixedToolchain_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
v_toWorkspaceConfig_3531_ = lean_ctor_get(v_cfg_3530_, 0);
v_toLeanConfig_3532_ = lean_ctor_get(v_cfg_3530_, 1);
v_bootstrap_3533_ = lean_ctor_get_uint8(v_cfg_3530_, sizeof(void*)*28);
v_extraDepTargets_3534_ = lean_ctor_get(v_cfg_3530_, 2);
v_precompileModules_3535_ = lean_ctor_get_uint8(v_cfg_3530_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3536_ = lean_ctor_get(v_cfg_3530_, 3);
v_srcDir_3537_ = lean_ctor_get(v_cfg_3530_, 4);
v_buildDir_3538_ = lean_ctor_get(v_cfg_3530_, 5);
v_leanLibDir_3539_ = lean_ctor_get(v_cfg_3530_, 6);
v_nativeLibDir_3540_ = lean_ctor_get(v_cfg_3530_, 7);
v_binDir_3541_ = lean_ctor_get(v_cfg_3530_, 8);
v_irDir_3542_ = lean_ctor_get(v_cfg_3530_, 9);
v_releaseRepo_3543_ = lean_ctor_get(v_cfg_3530_, 10);
v_buildArchive_3544_ = lean_ctor_get(v_cfg_3530_, 11);
v_preferReleaseBuild_3545_ = lean_ctor_get_uint8(v_cfg_3530_, sizeof(void*)*28 + 2);
v_testDriver_3546_ = lean_ctor_get(v_cfg_3530_, 12);
v_testDriverArgs_3547_ = lean_ctor_get(v_cfg_3530_, 13);
v_lintDriver_3548_ = lean_ctor_get(v_cfg_3530_, 14);
v_lintDriverArgs_3549_ = lean_ctor_get(v_cfg_3530_, 15);
v_version_3550_ = lean_ctor_get(v_cfg_3530_, 16);
v_versionTags_3551_ = lean_ctor_get(v_cfg_3530_, 17);
v_description_3552_ = lean_ctor_get(v_cfg_3530_, 18);
v_keywords_3553_ = lean_ctor_get(v_cfg_3530_, 19);
v_homepage_3554_ = lean_ctor_get(v_cfg_3530_, 20);
v_license_3555_ = lean_ctor_get(v_cfg_3530_, 21);
v_licenseFiles_3556_ = lean_ctor_get(v_cfg_3530_, 22);
v_readmeFile_3557_ = lean_ctor_get(v_cfg_3530_, 23);
v_reservoir_3558_ = lean_ctor_get_uint8(v_cfg_3530_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3559_ = lean_ctor_get(v_cfg_3530_, 24);
v_libPrefixOnWindows_3560_ = lean_ctor_get_uint8(v_cfg_3530_, sizeof(void*)*28 + 4);
v_allowImportAll_3561_ = lean_ctor_get_uint8(v_cfg_3530_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3562_ = lean_ctor_get(v_cfg_3530_, 26);
v_checks_3563_ = lean_ctor_get(v_cfg_3530_, 27);
v_fixedToolchain_3564_ = lean_ctor_get_uint8(v_cfg_3530_, sizeof(void*)*28 + 6);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_cfg_3530_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; 
v_unused_3572_ = lean_ctor_get(v_cfg_3530_, 25);
lean_dec(v_unused_3572_);
v___x_3566_ = v_cfg_3530_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_checks_3563_);
lean_inc(v_builtinLint_x3f_3562_);
lean_inc(v_enableArtifactCache_x3f_3559_);
lean_inc(v_readmeFile_3557_);
lean_inc(v_licenseFiles_3556_);
lean_inc(v_license_3555_);
lean_inc(v_homepage_3554_);
lean_inc(v_keywords_3553_);
lean_inc(v_description_3552_);
lean_inc(v_versionTags_3551_);
lean_inc(v_version_3550_);
lean_inc(v_lintDriverArgs_3549_);
lean_inc(v_lintDriver_3548_);
lean_inc(v_testDriverArgs_3547_);
lean_inc(v_testDriver_3546_);
lean_inc(v_buildArchive_3544_);
lean_inc(v_releaseRepo_3543_);
lean_inc(v_irDir_3542_);
lean_inc(v_binDir_3541_);
lean_inc(v_nativeLibDir_3540_);
lean_inc(v_leanLibDir_3539_);
lean_inc(v_buildDir_3538_);
lean_inc(v_srcDir_3537_);
lean_inc(v_moreGlobalServerArgs_3536_);
lean_inc(v_extraDepTargets_3534_);
lean_inc(v_toLeanConfig_3532_);
lean_inc(v_toWorkspaceConfig_3531_);
lean_dec(v_cfg_3530_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 25, v_val_3529_);
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_toWorkspaceConfig_3531_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_toLeanConfig_3532_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_extraDepTargets_3534_);
lean_ctor_set(v_reuseFailAlloc_3570_, 3, v_moreGlobalServerArgs_3536_);
lean_ctor_set(v_reuseFailAlloc_3570_, 4, v_srcDir_3537_);
lean_ctor_set(v_reuseFailAlloc_3570_, 5, v_buildDir_3538_);
lean_ctor_set(v_reuseFailAlloc_3570_, 6, v_leanLibDir_3539_);
lean_ctor_set(v_reuseFailAlloc_3570_, 7, v_nativeLibDir_3540_);
lean_ctor_set(v_reuseFailAlloc_3570_, 8, v_binDir_3541_);
lean_ctor_set(v_reuseFailAlloc_3570_, 9, v_irDir_3542_);
lean_ctor_set(v_reuseFailAlloc_3570_, 10, v_releaseRepo_3543_);
lean_ctor_set(v_reuseFailAlloc_3570_, 11, v_buildArchive_3544_);
lean_ctor_set(v_reuseFailAlloc_3570_, 12, v_testDriver_3546_);
lean_ctor_set(v_reuseFailAlloc_3570_, 13, v_testDriverArgs_3547_);
lean_ctor_set(v_reuseFailAlloc_3570_, 14, v_lintDriver_3548_);
lean_ctor_set(v_reuseFailAlloc_3570_, 15, v_lintDriverArgs_3549_);
lean_ctor_set(v_reuseFailAlloc_3570_, 16, v_version_3550_);
lean_ctor_set(v_reuseFailAlloc_3570_, 17, v_versionTags_3551_);
lean_ctor_set(v_reuseFailAlloc_3570_, 18, v_description_3552_);
lean_ctor_set(v_reuseFailAlloc_3570_, 19, v_keywords_3553_);
lean_ctor_set(v_reuseFailAlloc_3570_, 20, v_homepage_3554_);
lean_ctor_set(v_reuseFailAlloc_3570_, 21, v_license_3555_);
lean_ctor_set(v_reuseFailAlloc_3570_, 22, v_licenseFiles_3556_);
lean_ctor_set(v_reuseFailAlloc_3570_, 23, v_readmeFile_3557_);
lean_ctor_set(v_reuseFailAlloc_3570_, 24, v_enableArtifactCache_x3f_3559_);
lean_ctor_set(v_reuseFailAlloc_3570_, 25, v_val_3529_);
lean_ctor_set(v_reuseFailAlloc_3570_, 26, v_builtinLint_x3f_3562_);
lean_ctor_set(v_reuseFailAlloc_3570_, 27, v_checks_3563_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*28, v_bootstrap_3533_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*28 + 1, v_precompileModules_3535_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3545_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*28 + 3, v_reservoir_3558_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3560_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*28 + 5, v_allowImportAll_3561_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*28 + 6, v_fixedToolchain_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__2(lean_object* v_f_3573_, lean_object* v_cfg_3574_){
_start:
{
lean_object* v_toWorkspaceConfig_3575_; lean_object* v_toLeanConfig_3576_; uint8_t v_bootstrap_3577_; lean_object* v_extraDepTargets_3578_; uint8_t v_precompileModules_3579_; lean_object* v_moreGlobalServerArgs_3580_; lean_object* v_srcDir_3581_; lean_object* v_buildDir_3582_; lean_object* v_leanLibDir_3583_; lean_object* v_nativeLibDir_3584_; lean_object* v_binDir_3585_; lean_object* v_irDir_3586_; lean_object* v_releaseRepo_3587_; lean_object* v_buildArchive_3588_; uint8_t v_preferReleaseBuild_3589_; lean_object* v_testDriver_3590_; lean_object* v_testDriverArgs_3591_; lean_object* v_lintDriver_3592_; lean_object* v_lintDriverArgs_3593_; lean_object* v_version_3594_; lean_object* v_versionTags_3595_; lean_object* v_description_3596_; lean_object* v_keywords_3597_; lean_object* v_homepage_3598_; lean_object* v_license_3599_; lean_object* v_licenseFiles_3600_; lean_object* v_readmeFile_3601_; uint8_t v_reservoir_3602_; lean_object* v_enableArtifactCache_x3f_3603_; lean_object* v_restoreAllArtifacts_x3f_3604_; uint8_t v_libPrefixOnWindows_3605_; uint8_t v_allowImportAll_3606_; lean_object* v_builtinLint_x3f_3607_; lean_object* v_checks_3608_; uint8_t v_fixedToolchain_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3617_; 
v_toWorkspaceConfig_3575_ = lean_ctor_get(v_cfg_3574_, 0);
v_toLeanConfig_3576_ = lean_ctor_get(v_cfg_3574_, 1);
v_bootstrap_3577_ = lean_ctor_get_uint8(v_cfg_3574_, sizeof(void*)*28);
v_extraDepTargets_3578_ = lean_ctor_get(v_cfg_3574_, 2);
v_precompileModules_3579_ = lean_ctor_get_uint8(v_cfg_3574_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3580_ = lean_ctor_get(v_cfg_3574_, 3);
v_srcDir_3581_ = lean_ctor_get(v_cfg_3574_, 4);
v_buildDir_3582_ = lean_ctor_get(v_cfg_3574_, 5);
v_leanLibDir_3583_ = lean_ctor_get(v_cfg_3574_, 6);
v_nativeLibDir_3584_ = lean_ctor_get(v_cfg_3574_, 7);
v_binDir_3585_ = lean_ctor_get(v_cfg_3574_, 8);
v_irDir_3586_ = lean_ctor_get(v_cfg_3574_, 9);
v_releaseRepo_3587_ = lean_ctor_get(v_cfg_3574_, 10);
v_buildArchive_3588_ = lean_ctor_get(v_cfg_3574_, 11);
v_preferReleaseBuild_3589_ = lean_ctor_get_uint8(v_cfg_3574_, sizeof(void*)*28 + 2);
v_testDriver_3590_ = lean_ctor_get(v_cfg_3574_, 12);
v_testDriverArgs_3591_ = lean_ctor_get(v_cfg_3574_, 13);
v_lintDriver_3592_ = lean_ctor_get(v_cfg_3574_, 14);
v_lintDriverArgs_3593_ = lean_ctor_get(v_cfg_3574_, 15);
v_version_3594_ = lean_ctor_get(v_cfg_3574_, 16);
v_versionTags_3595_ = lean_ctor_get(v_cfg_3574_, 17);
v_description_3596_ = lean_ctor_get(v_cfg_3574_, 18);
v_keywords_3597_ = lean_ctor_get(v_cfg_3574_, 19);
v_homepage_3598_ = lean_ctor_get(v_cfg_3574_, 20);
v_license_3599_ = lean_ctor_get(v_cfg_3574_, 21);
v_licenseFiles_3600_ = lean_ctor_get(v_cfg_3574_, 22);
v_readmeFile_3601_ = lean_ctor_get(v_cfg_3574_, 23);
v_reservoir_3602_ = lean_ctor_get_uint8(v_cfg_3574_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3603_ = lean_ctor_get(v_cfg_3574_, 24);
v_restoreAllArtifacts_x3f_3604_ = lean_ctor_get(v_cfg_3574_, 25);
v_libPrefixOnWindows_3605_ = lean_ctor_get_uint8(v_cfg_3574_, sizeof(void*)*28 + 4);
v_allowImportAll_3606_ = lean_ctor_get_uint8(v_cfg_3574_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3607_ = lean_ctor_get(v_cfg_3574_, 26);
v_checks_3608_ = lean_ctor_get(v_cfg_3574_, 27);
v_fixedToolchain_3609_ = lean_ctor_get_uint8(v_cfg_3574_, sizeof(void*)*28 + 6);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_cfg_3574_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3611_ = v_cfg_3574_;
v_isShared_3612_ = v_isSharedCheck_3617_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_checks_3608_);
lean_inc(v_builtinLint_x3f_3607_);
lean_inc(v_restoreAllArtifacts_x3f_3604_);
lean_inc(v_enableArtifactCache_x3f_3603_);
lean_inc(v_readmeFile_3601_);
lean_inc(v_licenseFiles_3600_);
lean_inc(v_license_3599_);
lean_inc(v_homepage_3598_);
lean_inc(v_keywords_3597_);
lean_inc(v_description_3596_);
lean_inc(v_versionTags_3595_);
lean_inc(v_version_3594_);
lean_inc(v_lintDriverArgs_3593_);
lean_inc(v_lintDriver_3592_);
lean_inc(v_testDriverArgs_3591_);
lean_inc(v_testDriver_3590_);
lean_inc(v_buildArchive_3588_);
lean_inc(v_releaseRepo_3587_);
lean_inc(v_irDir_3586_);
lean_inc(v_binDir_3585_);
lean_inc(v_nativeLibDir_3584_);
lean_inc(v_leanLibDir_3583_);
lean_inc(v_buildDir_3582_);
lean_inc(v_srcDir_3581_);
lean_inc(v_moreGlobalServerArgs_3580_);
lean_inc(v_extraDepTargets_3578_);
lean_inc(v_toLeanConfig_3576_);
lean_inc(v_toWorkspaceConfig_3575_);
lean_dec(v_cfg_3574_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3617_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3613_; lean_object* v___x_3615_; 
v___x_3613_ = lean_apply_1(v_f_3573_, v_restoreAllArtifacts_x3f_3604_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 25, v___x_3613_);
v___x_3615_ = v___x_3611_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_toWorkspaceConfig_3575_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_toLeanConfig_3576_);
lean_ctor_set(v_reuseFailAlloc_3616_, 2, v_extraDepTargets_3578_);
lean_ctor_set(v_reuseFailAlloc_3616_, 3, v_moreGlobalServerArgs_3580_);
lean_ctor_set(v_reuseFailAlloc_3616_, 4, v_srcDir_3581_);
lean_ctor_set(v_reuseFailAlloc_3616_, 5, v_buildDir_3582_);
lean_ctor_set(v_reuseFailAlloc_3616_, 6, v_leanLibDir_3583_);
lean_ctor_set(v_reuseFailAlloc_3616_, 7, v_nativeLibDir_3584_);
lean_ctor_set(v_reuseFailAlloc_3616_, 8, v_binDir_3585_);
lean_ctor_set(v_reuseFailAlloc_3616_, 9, v_irDir_3586_);
lean_ctor_set(v_reuseFailAlloc_3616_, 10, v_releaseRepo_3587_);
lean_ctor_set(v_reuseFailAlloc_3616_, 11, v_buildArchive_3588_);
lean_ctor_set(v_reuseFailAlloc_3616_, 12, v_testDriver_3590_);
lean_ctor_set(v_reuseFailAlloc_3616_, 13, v_testDriverArgs_3591_);
lean_ctor_set(v_reuseFailAlloc_3616_, 14, v_lintDriver_3592_);
lean_ctor_set(v_reuseFailAlloc_3616_, 15, v_lintDriverArgs_3593_);
lean_ctor_set(v_reuseFailAlloc_3616_, 16, v_version_3594_);
lean_ctor_set(v_reuseFailAlloc_3616_, 17, v_versionTags_3595_);
lean_ctor_set(v_reuseFailAlloc_3616_, 18, v_description_3596_);
lean_ctor_set(v_reuseFailAlloc_3616_, 19, v_keywords_3597_);
lean_ctor_set(v_reuseFailAlloc_3616_, 20, v_homepage_3598_);
lean_ctor_set(v_reuseFailAlloc_3616_, 21, v_license_3599_);
lean_ctor_set(v_reuseFailAlloc_3616_, 22, v_licenseFiles_3600_);
lean_ctor_set(v_reuseFailAlloc_3616_, 23, v_readmeFile_3601_);
lean_ctor_set(v_reuseFailAlloc_3616_, 24, v_enableArtifactCache_x3f_3603_);
lean_ctor_set(v_reuseFailAlloc_3616_, 25, v___x_3613_);
lean_ctor_set(v_reuseFailAlloc_3616_, 26, v_builtinLint_x3f_3607_);
lean_ctor_set(v_reuseFailAlloc_3616_, 27, v_checks_3608_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, sizeof(void*)*28, v_bootstrap_3577_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, sizeof(void*)*28 + 1, v_precompileModules_3579_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3589_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, sizeof(void*)*28 + 3, v_reservoir_3602_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3605_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, sizeof(void*)*28 + 5, v_allowImportAll_3606_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, sizeof(void*)*28 + 6, v_fixedToolchain_3609_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg(){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = ((lean_object*)(l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__3));
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___boxed(lean_object* v___dummy_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg();
return v_res_3629_;
}
}
static lean_object* _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0(void){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg();
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object* v_p_3631_, lean_object* v_n_3632_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___boxed(lean_object* v_p_3634_, lean_object* v_n_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3634_, v_n_3635_);
lean_dec(v_n_3635_);
lean_dec(v_p_3634_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg();
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object* v_p_3641_, lean_object* v_n_3642_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object* v_p_3644_, lean_object* v_n_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(v_p_3644_, v_n_3645_);
lean_dec(v_n_3645_);
lean_dec(v_p_3644_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg(){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg___boxed(lean_object* v___dummy_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg();
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object* v_p_3651_, lean_object* v_n_3652_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object* v_p_3654_, lean_object* v_n_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(v_p_3654_, v_n_3655_);
lean_dec(v_n_3655_);
lean_dec(v_p_3654_);
return v_res_3656_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0(lean_object* v_cfg_3657_){
_start:
{
uint8_t v_libPrefixOnWindows_3658_; 
v_libPrefixOnWindows_3658_ = lean_ctor_get_uint8(v_cfg_3657_, sizeof(void*)*28 + 4);
return v_libPrefixOnWindows_3658_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0___boxed(lean_object* v_cfg_3659_){
_start:
{
uint8_t v_res_3660_; lean_object* v_r_3661_; 
v_res_3660_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0(v_cfg_3659_);
lean_dec_ref(v_cfg_3659_);
v_r_3661_ = lean_box(v_res_3660_);
return v_r_3661_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1(uint8_t v_val_3662_, lean_object* v_cfg_3663_){
_start:
{
lean_object* v_toWorkspaceConfig_3664_; lean_object* v_toLeanConfig_3665_; uint8_t v_bootstrap_3666_; lean_object* v_extraDepTargets_3667_; uint8_t v_precompileModules_3668_; lean_object* v_moreGlobalServerArgs_3669_; lean_object* v_srcDir_3670_; lean_object* v_buildDir_3671_; lean_object* v_leanLibDir_3672_; lean_object* v_nativeLibDir_3673_; lean_object* v_binDir_3674_; lean_object* v_irDir_3675_; lean_object* v_releaseRepo_3676_; lean_object* v_buildArchive_3677_; uint8_t v_preferReleaseBuild_3678_; lean_object* v_testDriver_3679_; lean_object* v_testDriverArgs_3680_; lean_object* v_lintDriver_3681_; lean_object* v_lintDriverArgs_3682_; lean_object* v_version_3683_; lean_object* v_versionTags_3684_; lean_object* v_description_3685_; lean_object* v_keywords_3686_; lean_object* v_homepage_3687_; lean_object* v_license_3688_; lean_object* v_licenseFiles_3689_; lean_object* v_readmeFile_3690_; uint8_t v_reservoir_3691_; lean_object* v_enableArtifactCache_x3f_3692_; lean_object* v_restoreAllArtifacts_x3f_3693_; uint8_t v_allowImportAll_3694_; lean_object* v_builtinLint_x3f_3695_; lean_object* v_checks_3696_; uint8_t v_fixedToolchain_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
v_toWorkspaceConfig_3664_ = lean_ctor_get(v_cfg_3663_, 0);
v_toLeanConfig_3665_ = lean_ctor_get(v_cfg_3663_, 1);
v_bootstrap_3666_ = lean_ctor_get_uint8(v_cfg_3663_, sizeof(void*)*28);
v_extraDepTargets_3667_ = lean_ctor_get(v_cfg_3663_, 2);
v_precompileModules_3668_ = lean_ctor_get_uint8(v_cfg_3663_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3669_ = lean_ctor_get(v_cfg_3663_, 3);
v_srcDir_3670_ = lean_ctor_get(v_cfg_3663_, 4);
v_buildDir_3671_ = lean_ctor_get(v_cfg_3663_, 5);
v_leanLibDir_3672_ = lean_ctor_get(v_cfg_3663_, 6);
v_nativeLibDir_3673_ = lean_ctor_get(v_cfg_3663_, 7);
v_binDir_3674_ = lean_ctor_get(v_cfg_3663_, 8);
v_irDir_3675_ = lean_ctor_get(v_cfg_3663_, 9);
v_releaseRepo_3676_ = lean_ctor_get(v_cfg_3663_, 10);
v_buildArchive_3677_ = lean_ctor_get(v_cfg_3663_, 11);
v_preferReleaseBuild_3678_ = lean_ctor_get_uint8(v_cfg_3663_, sizeof(void*)*28 + 2);
v_testDriver_3679_ = lean_ctor_get(v_cfg_3663_, 12);
v_testDriverArgs_3680_ = lean_ctor_get(v_cfg_3663_, 13);
v_lintDriver_3681_ = lean_ctor_get(v_cfg_3663_, 14);
v_lintDriverArgs_3682_ = lean_ctor_get(v_cfg_3663_, 15);
v_version_3683_ = lean_ctor_get(v_cfg_3663_, 16);
v_versionTags_3684_ = lean_ctor_get(v_cfg_3663_, 17);
v_description_3685_ = lean_ctor_get(v_cfg_3663_, 18);
v_keywords_3686_ = lean_ctor_get(v_cfg_3663_, 19);
v_homepage_3687_ = lean_ctor_get(v_cfg_3663_, 20);
v_license_3688_ = lean_ctor_get(v_cfg_3663_, 21);
v_licenseFiles_3689_ = lean_ctor_get(v_cfg_3663_, 22);
v_readmeFile_3690_ = lean_ctor_get(v_cfg_3663_, 23);
v_reservoir_3691_ = lean_ctor_get_uint8(v_cfg_3663_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3692_ = lean_ctor_get(v_cfg_3663_, 24);
v_restoreAllArtifacts_x3f_3693_ = lean_ctor_get(v_cfg_3663_, 25);
v_allowImportAll_3694_ = lean_ctor_get_uint8(v_cfg_3663_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3695_ = lean_ctor_get(v_cfg_3663_, 26);
v_checks_3696_ = lean_ctor_get(v_cfg_3663_, 27);
v_fixedToolchain_3697_ = lean_ctor_get_uint8(v_cfg_3663_, sizeof(void*)*28 + 6);
v_isSharedCheck_3704_ = !lean_is_exclusive(v_cfg_3663_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3699_ = v_cfg_3663_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_checks_3696_);
lean_inc(v_builtinLint_x3f_3695_);
lean_inc(v_restoreAllArtifacts_x3f_3693_);
lean_inc(v_enableArtifactCache_x3f_3692_);
lean_inc(v_readmeFile_3690_);
lean_inc(v_licenseFiles_3689_);
lean_inc(v_license_3688_);
lean_inc(v_homepage_3687_);
lean_inc(v_keywords_3686_);
lean_inc(v_description_3685_);
lean_inc(v_versionTags_3684_);
lean_inc(v_version_3683_);
lean_inc(v_lintDriverArgs_3682_);
lean_inc(v_lintDriver_3681_);
lean_inc(v_testDriverArgs_3680_);
lean_inc(v_testDriver_3679_);
lean_inc(v_buildArchive_3677_);
lean_inc(v_releaseRepo_3676_);
lean_inc(v_irDir_3675_);
lean_inc(v_binDir_3674_);
lean_inc(v_nativeLibDir_3673_);
lean_inc(v_leanLibDir_3672_);
lean_inc(v_buildDir_3671_);
lean_inc(v_srcDir_3670_);
lean_inc(v_moreGlobalServerArgs_3669_);
lean_inc(v_extraDepTargets_3667_);
lean_inc(v_toLeanConfig_3665_);
lean_inc(v_toWorkspaceConfig_3664_);
lean_dec(v_cfg_3663_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_toWorkspaceConfig_3664_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_toLeanConfig_3665_);
lean_ctor_set(v_reuseFailAlloc_3703_, 2, v_extraDepTargets_3667_);
lean_ctor_set(v_reuseFailAlloc_3703_, 3, v_moreGlobalServerArgs_3669_);
lean_ctor_set(v_reuseFailAlloc_3703_, 4, v_srcDir_3670_);
lean_ctor_set(v_reuseFailAlloc_3703_, 5, v_buildDir_3671_);
lean_ctor_set(v_reuseFailAlloc_3703_, 6, v_leanLibDir_3672_);
lean_ctor_set(v_reuseFailAlloc_3703_, 7, v_nativeLibDir_3673_);
lean_ctor_set(v_reuseFailAlloc_3703_, 8, v_binDir_3674_);
lean_ctor_set(v_reuseFailAlloc_3703_, 9, v_irDir_3675_);
lean_ctor_set(v_reuseFailAlloc_3703_, 10, v_releaseRepo_3676_);
lean_ctor_set(v_reuseFailAlloc_3703_, 11, v_buildArchive_3677_);
lean_ctor_set(v_reuseFailAlloc_3703_, 12, v_testDriver_3679_);
lean_ctor_set(v_reuseFailAlloc_3703_, 13, v_testDriverArgs_3680_);
lean_ctor_set(v_reuseFailAlloc_3703_, 14, v_lintDriver_3681_);
lean_ctor_set(v_reuseFailAlloc_3703_, 15, v_lintDriverArgs_3682_);
lean_ctor_set(v_reuseFailAlloc_3703_, 16, v_version_3683_);
lean_ctor_set(v_reuseFailAlloc_3703_, 17, v_versionTags_3684_);
lean_ctor_set(v_reuseFailAlloc_3703_, 18, v_description_3685_);
lean_ctor_set(v_reuseFailAlloc_3703_, 19, v_keywords_3686_);
lean_ctor_set(v_reuseFailAlloc_3703_, 20, v_homepage_3687_);
lean_ctor_set(v_reuseFailAlloc_3703_, 21, v_license_3688_);
lean_ctor_set(v_reuseFailAlloc_3703_, 22, v_licenseFiles_3689_);
lean_ctor_set(v_reuseFailAlloc_3703_, 23, v_readmeFile_3690_);
lean_ctor_set(v_reuseFailAlloc_3703_, 24, v_enableArtifactCache_x3f_3692_);
lean_ctor_set(v_reuseFailAlloc_3703_, 25, v_restoreAllArtifacts_x3f_3693_);
lean_ctor_set(v_reuseFailAlloc_3703_, 26, v_builtinLint_x3f_3695_);
lean_ctor_set(v_reuseFailAlloc_3703_, 27, v_checks_3696_);
lean_ctor_set_uint8(v_reuseFailAlloc_3703_, sizeof(void*)*28, v_bootstrap_3666_);
lean_ctor_set_uint8(v_reuseFailAlloc_3703_, sizeof(void*)*28 + 1, v_precompileModules_3668_);
lean_ctor_set_uint8(v_reuseFailAlloc_3703_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3703_, sizeof(void*)*28 + 3, v_reservoir_3691_);
lean_ctor_set_uint8(v_reuseFailAlloc_3703_, sizeof(void*)*28 + 5, v_allowImportAll_3694_);
lean_ctor_set_uint8(v_reuseFailAlloc_3703_, sizeof(void*)*28 + 6, v_fixedToolchain_3697_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_ctor_set_uint8(v___x_3702_, sizeof(void*)*28 + 4, v_val_3662_);
return v___x_3702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1___boxed(lean_object* v_val_3705_, lean_object* v_cfg_3706_){
_start:
{
uint8_t v_val_141__boxed_3707_; lean_object* v_res_3708_; 
v_val_141__boxed_3707_ = lean_unbox(v_val_3705_);
v_res_3708_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1(v_val_141__boxed_3707_, v_cfg_3706_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__2(lean_object* v_f_3709_, lean_object* v_cfg_3710_){
_start:
{
lean_object* v_toWorkspaceConfig_3711_; lean_object* v_toLeanConfig_3712_; uint8_t v_bootstrap_3713_; lean_object* v_extraDepTargets_3714_; uint8_t v_precompileModules_3715_; lean_object* v_moreGlobalServerArgs_3716_; lean_object* v_srcDir_3717_; lean_object* v_buildDir_3718_; lean_object* v_leanLibDir_3719_; lean_object* v_nativeLibDir_3720_; lean_object* v_binDir_3721_; lean_object* v_irDir_3722_; lean_object* v_releaseRepo_3723_; lean_object* v_buildArchive_3724_; uint8_t v_preferReleaseBuild_3725_; lean_object* v_testDriver_3726_; lean_object* v_testDriverArgs_3727_; lean_object* v_lintDriver_3728_; lean_object* v_lintDriverArgs_3729_; lean_object* v_version_3730_; lean_object* v_versionTags_3731_; lean_object* v_description_3732_; lean_object* v_keywords_3733_; lean_object* v_homepage_3734_; lean_object* v_license_3735_; lean_object* v_licenseFiles_3736_; lean_object* v_readmeFile_3737_; uint8_t v_reservoir_3738_; lean_object* v_enableArtifactCache_x3f_3739_; lean_object* v_restoreAllArtifacts_x3f_3740_; uint8_t v_libPrefixOnWindows_3741_; uint8_t v_allowImportAll_3742_; lean_object* v_builtinLint_x3f_3743_; lean_object* v_checks_3744_; uint8_t v_fixedToolchain_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3755_; 
v_toWorkspaceConfig_3711_ = lean_ctor_get(v_cfg_3710_, 0);
v_toLeanConfig_3712_ = lean_ctor_get(v_cfg_3710_, 1);
v_bootstrap_3713_ = lean_ctor_get_uint8(v_cfg_3710_, sizeof(void*)*28);
v_extraDepTargets_3714_ = lean_ctor_get(v_cfg_3710_, 2);
v_precompileModules_3715_ = lean_ctor_get_uint8(v_cfg_3710_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3716_ = lean_ctor_get(v_cfg_3710_, 3);
v_srcDir_3717_ = lean_ctor_get(v_cfg_3710_, 4);
v_buildDir_3718_ = lean_ctor_get(v_cfg_3710_, 5);
v_leanLibDir_3719_ = lean_ctor_get(v_cfg_3710_, 6);
v_nativeLibDir_3720_ = lean_ctor_get(v_cfg_3710_, 7);
v_binDir_3721_ = lean_ctor_get(v_cfg_3710_, 8);
v_irDir_3722_ = lean_ctor_get(v_cfg_3710_, 9);
v_releaseRepo_3723_ = lean_ctor_get(v_cfg_3710_, 10);
v_buildArchive_3724_ = lean_ctor_get(v_cfg_3710_, 11);
v_preferReleaseBuild_3725_ = lean_ctor_get_uint8(v_cfg_3710_, sizeof(void*)*28 + 2);
v_testDriver_3726_ = lean_ctor_get(v_cfg_3710_, 12);
v_testDriverArgs_3727_ = lean_ctor_get(v_cfg_3710_, 13);
v_lintDriver_3728_ = lean_ctor_get(v_cfg_3710_, 14);
v_lintDriverArgs_3729_ = lean_ctor_get(v_cfg_3710_, 15);
v_version_3730_ = lean_ctor_get(v_cfg_3710_, 16);
v_versionTags_3731_ = lean_ctor_get(v_cfg_3710_, 17);
v_description_3732_ = lean_ctor_get(v_cfg_3710_, 18);
v_keywords_3733_ = lean_ctor_get(v_cfg_3710_, 19);
v_homepage_3734_ = lean_ctor_get(v_cfg_3710_, 20);
v_license_3735_ = lean_ctor_get(v_cfg_3710_, 21);
v_licenseFiles_3736_ = lean_ctor_get(v_cfg_3710_, 22);
v_readmeFile_3737_ = lean_ctor_get(v_cfg_3710_, 23);
v_reservoir_3738_ = lean_ctor_get_uint8(v_cfg_3710_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3739_ = lean_ctor_get(v_cfg_3710_, 24);
v_restoreAllArtifacts_x3f_3740_ = lean_ctor_get(v_cfg_3710_, 25);
v_libPrefixOnWindows_3741_ = lean_ctor_get_uint8(v_cfg_3710_, sizeof(void*)*28 + 4);
v_allowImportAll_3742_ = lean_ctor_get_uint8(v_cfg_3710_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3743_ = lean_ctor_get(v_cfg_3710_, 26);
v_checks_3744_ = lean_ctor_get(v_cfg_3710_, 27);
v_fixedToolchain_3745_ = lean_ctor_get_uint8(v_cfg_3710_, sizeof(void*)*28 + 6);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_cfg_3710_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3747_ = v_cfg_3710_;
v_isShared_3748_ = v_isSharedCheck_3755_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_checks_3744_);
lean_inc(v_builtinLint_x3f_3743_);
lean_inc(v_restoreAllArtifacts_x3f_3740_);
lean_inc(v_enableArtifactCache_x3f_3739_);
lean_inc(v_readmeFile_3737_);
lean_inc(v_licenseFiles_3736_);
lean_inc(v_license_3735_);
lean_inc(v_homepage_3734_);
lean_inc(v_keywords_3733_);
lean_inc(v_description_3732_);
lean_inc(v_versionTags_3731_);
lean_inc(v_version_3730_);
lean_inc(v_lintDriverArgs_3729_);
lean_inc(v_lintDriver_3728_);
lean_inc(v_testDriverArgs_3727_);
lean_inc(v_testDriver_3726_);
lean_inc(v_buildArchive_3724_);
lean_inc(v_releaseRepo_3723_);
lean_inc(v_irDir_3722_);
lean_inc(v_binDir_3721_);
lean_inc(v_nativeLibDir_3720_);
lean_inc(v_leanLibDir_3719_);
lean_inc(v_buildDir_3718_);
lean_inc(v_srcDir_3717_);
lean_inc(v_moreGlobalServerArgs_3716_);
lean_inc(v_extraDepTargets_3714_);
lean_inc(v_toLeanConfig_3712_);
lean_inc(v_toWorkspaceConfig_3711_);
lean_dec(v_cfg_3710_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3755_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3749_ = lean_box(v_libPrefixOnWindows_3741_);
v___x_3750_ = lean_apply_1(v_f_3709_, v___x_3749_);
if (v_isShared_3748_ == 0)
{
v___x_3752_ = v___x_3747_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_toWorkspaceConfig_3711_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v_toLeanConfig_3712_);
lean_ctor_set(v_reuseFailAlloc_3754_, 2, v_extraDepTargets_3714_);
lean_ctor_set(v_reuseFailAlloc_3754_, 3, v_moreGlobalServerArgs_3716_);
lean_ctor_set(v_reuseFailAlloc_3754_, 4, v_srcDir_3717_);
lean_ctor_set(v_reuseFailAlloc_3754_, 5, v_buildDir_3718_);
lean_ctor_set(v_reuseFailAlloc_3754_, 6, v_leanLibDir_3719_);
lean_ctor_set(v_reuseFailAlloc_3754_, 7, v_nativeLibDir_3720_);
lean_ctor_set(v_reuseFailAlloc_3754_, 8, v_binDir_3721_);
lean_ctor_set(v_reuseFailAlloc_3754_, 9, v_irDir_3722_);
lean_ctor_set(v_reuseFailAlloc_3754_, 10, v_releaseRepo_3723_);
lean_ctor_set(v_reuseFailAlloc_3754_, 11, v_buildArchive_3724_);
lean_ctor_set(v_reuseFailAlloc_3754_, 12, v_testDriver_3726_);
lean_ctor_set(v_reuseFailAlloc_3754_, 13, v_testDriverArgs_3727_);
lean_ctor_set(v_reuseFailAlloc_3754_, 14, v_lintDriver_3728_);
lean_ctor_set(v_reuseFailAlloc_3754_, 15, v_lintDriverArgs_3729_);
lean_ctor_set(v_reuseFailAlloc_3754_, 16, v_version_3730_);
lean_ctor_set(v_reuseFailAlloc_3754_, 17, v_versionTags_3731_);
lean_ctor_set(v_reuseFailAlloc_3754_, 18, v_description_3732_);
lean_ctor_set(v_reuseFailAlloc_3754_, 19, v_keywords_3733_);
lean_ctor_set(v_reuseFailAlloc_3754_, 20, v_homepage_3734_);
lean_ctor_set(v_reuseFailAlloc_3754_, 21, v_license_3735_);
lean_ctor_set(v_reuseFailAlloc_3754_, 22, v_licenseFiles_3736_);
lean_ctor_set(v_reuseFailAlloc_3754_, 23, v_readmeFile_3737_);
lean_ctor_set(v_reuseFailAlloc_3754_, 24, v_enableArtifactCache_x3f_3739_);
lean_ctor_set(v_reuseFailAlloc_3754_, 25, v_restoreAllArtifacts_x3f_3740_);
lean_ctor_set(v_reuseFailAlloc_3754_, 26, v_builtinLint_x3f_3743_);
lean_ctor_set(v_reuseFailAlloc_3754_, 27, v_checks_3744_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, sizeof(void*)*28, v_bootstrap_3713_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, sizeof(void*)*28 + 1, v_precompileModules_3715_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3725_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, sizeof(void*)*28 + 3, v_reservoir_3738_);
v___x_3752_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
uint8_t v___x_3753_; 
v___x_3753_ = lean_unbox(v___x_3750_);
lean_ctor_set_uint8(v___x_3752_, sizeof(void*)*28 + 4, v___x_3753_);
lean_ctor_set_uint8(v___x_3752_, sizeof(void*)*28 + 5, v_allowImportAll_3742_);
lean_ctor_set_uint8(v___x_3752_, sizeof(void*)*28 + 6, v_fixedToolchain_3745_);
return v___x_3752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg(){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = ((lean_object*)(l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__3));
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___boxed(lean_object* v___dummy_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg();
return v_res_3767_;
}
}
static lean_object* _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0(void){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg();
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object* v_p_3769_, lean_object* v_n_3770_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_obj_once(&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object* v_p_3772_, lean_object* v_n_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3772_, v_n_3773_);
lean_dec(v_n_3773_);
lean_dec(v_p_3772_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg(){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = lean_obj_once(&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg___boxed(lean_object* v___dummy_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg();
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object* v_p_3779_, lean_object* v_n_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_obj_once(&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_p_3782_, lean_object* v_n_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(v_p_3782_, v_n_3783_);
lean_dec(v_n_3783_);
lean_dec(v_p_3782_);
return v_res_3784_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0(lean_object* v_cfg_3785_){
_start:
{
uint8_t v_allowImportAll_3786_; 
v_allowImportAll_3786_ = lean_ctor_get_uint8(v_cfg_3785_, sizeof(void*)*28 + 5);
return v_allowImportAll_3786_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0___boxed(lean_object* v_cfg_3787_){
_start:
{
uint8_t v_res_3788_; lean_object* v_r_3789_; 
v_res_3788_ = l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0(v_cfg_3787_);
lean_dec_ref(v_cfg_3787_);
v_r_3789_ = lean_box(v_res_3788_);
return v_r_3789_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1(uint8_t v_val_3790_, lean_object* v_cfg_3791_){
_start:
{
lean_object* v_toWorkspaceConfig_3792_; lean_object* v_toLeanConfig_3793_; uint8_t v_bootstrap_3794_; lean_object* v_extraDepTargets_3795_; uint8_t v_precompileModules_3796_; lean_object* v_moreGlobalServerArgs_3797_; lean_object* v_srcDir_3798_; lean_object* v_buildDir_3799_; lean_object* v_leanLibDir_3800_; lean_object* v_nativeLibDir_3801_; lean_object* v_binDir_3802_; lean_object* v_irDir_3803_; lean_object* v_releaseRepo_3804_; lean_object* v_buildArchive_3805_; uint8_t v_preferReleaseBuild_3806_; lean_object* v_testDriver_3807_; lean_object* v_testDriverArgs_3808_; lean_object* v_lintDriver_3809_; lean_object* v_lintDriverArgs_3810_; lean_object* v_version_3811_; lean_object* v_versionTags_3812_; lean_object* v_description_3813_; lean_object* v_keywords_3814_; lean_object* v_homepage_3815_; lean_object* v_license_3816_; lean_object* v_licenseFiles_3817_; lean_object* v_readmeFile_3818_; uint8_t v_reservoir_3819_; lean_object* v_enableArtifactCache_x3f_3820_; lean_object* v_restoreAllArtifacts_x3f_3821_; uint8_t v_libPrefixOnWindows_3822_; lean_object* v_builtinLint_x3f_3823_; lean_object* v_checks_3824_; uint8_t v_fixedToolchain_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_toWorkspaceConfig_3792_ = lean_ctor_get(v_cfg_3791_, 0);
v_toLeanConfig_3793_ = lean_ctor_get(v_cfg_3791_, 1);
v_bootstrap_3794_ = lean_ctor_get_uint8(v_cfg_3791_, sizeof(void*)*28);
v_extraDepTargets_3795_ = lean_ctor_get(v_cfg_3791_, 2);
v_precompileModules_3796_ = lean_ctor_get_uint8(v_cfg_3791_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3797_ = lean_ctor_get(v_cfg_3791_, 3);
v_srcDir_3798_ = lean_ctor_get(v_cfg_3791_, 4);
v_buildDir_3799_ = lean_ctor_get(v_cfg_3791_, 5);
v_leanLibDir_3800_ = lean_ctor_get(v_cfg_3791_, 6);
v_nativeLibDir_3801_ = lean_ctor_get(v_cfg_3791_, 7);
v_binDir_3802_ = lean_ctor_get(v_cfg_3791_, 8);
v_irDir_3803_ = lean_ctor_get(v_cfg_3791_, 9);
v_releaseRepo_3804_ = lean_ctor_get(v_cfg_3791_, 10);
v_buildArchive_3805_ = lean_ctor_get(v_cfg_3791_, 11);
v_preferReleaseBuild_3806_ = lean_ctor_get_uint8(v_cfg_3791_, sizeof(void*)*28 + 2);
v_testDriver_3807_ = lean_ctor_get(v_cfg_3791_, 12);
v_testDriverArgs_3808_ = lean_ctor_get(v_cfg_3791_, 13);
v_lintDriver_3809_ = lean_ctor_get(v_cfg_3791_, 14);
v_lintDriverArgs_3810_ = lean_ctor_get(v_cfg_3791_, 15);
v_version_3811_ = lean_ctor_get(v_cfg_3791_, 16);
v_versionTags_3812_ = lean_ctor_get(v_cfg_3791_, 17);
v_description_3813_ = lean_ctor_get(v_cfg_3791_, 18);
v_keywords_3814_ = lean_ctor_get(v_cfg_3791_, 19);
v_homepage_3815_ = lean_ctor_get(v_cfg_3791_, 20);
v_license_3816_ = lean_ctor_get(v_cfg_3791_, 21);
v_licenseFiles_3817_ = lean_ctor_get(v_cfg_3791_, 22);
v_readmeFile_3818_ = lean_ctor_get(v_cfg_3791_, 23);
v_reservoir_3819_ = lean_ctor_get_uint8(v_cfg_3791_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3820_ = lean_ctor_get(v_cfg_3791_, 24);
v_restoreAllArtifacts_x3f_3821_ = lean_ctor_get(v_cfg_3791_, 25);
v_libPrefixOnWindows_3822_ = lean_ctor_get_uint8(v_cfg_3791_, sizeof(void*)*28 + 4);
v_builtinLint_x3f_3823_ = lean_ctor_get(v_cfg_3791_, 26);
v_checks_3824_ = lean_ctor_get(v_cfg_3791_, 27);
v_fixedToolchain_3825_ = lean_ctor_get_uint8(v_cfg_3791_, sizeof(void*)*28 + 6);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_cfg_3791_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v_cfg_3791_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_checks_3824_);
lean_inc(v_builtinLint_x3f_3823_);
lean_inc(v_restoreAllArtifacts_x3f_3821_);
lean_inc(v_enableArtifactCache_x3f_3820_);
lean_inc(v_readmeFile_3818_);
lean_inc(v_licenseFiles_3817_);
lean_inc(v_license_3816_);
lean_inc(v_homepage_3815_);
lean_inc(v_keywords_3814_);
lean_inc(v_description_3813_);
lean_inc(v_versionTags_3812_);
lean_inc(v_version_3811_);
lean_inc(v_lintDriverArgs_3810_);
lean_inc(v_lintDriver_3809_);
lean_inc(v_testDriverArgs_3808_);
lean_inc(v_testDriver_3807_);
lean_inc(v_buildArchive_3805_);
lean_inc(v_releaseRepo_3804_);
lean_inc(v_irDir_3803_);
lean_inc(v_binDir_3802_);
lean_inc(v_nativeLibDir_3801_);
lean_inc(v_leanLibDir_3800_);
lean_inc(v_buildDir_3799_);
lean_inc(v_srcDir_3798_);
lean_inc(v_moreGlobalServerArgs_3797_);
lean_inc(v_extraDepTargets_3795_);
lean_inc(v_toLeanConfig_3793_);
lean_inc(v_toWorkspaceConfig_3792_);
lean_dec(v_cfg_3791_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_toWorkspaceConfig_3792_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_toLeanConfig_3793_);
lean_ctor_set(v_reuseFailAlloc_3831_, 2, v_extraDepTargets_3795_);
lean_ctor_set(v_reuseFailAlloc_3831_, 3, v_moreGlobalServerArgs_3797_);
lean_ctor_set(v_reuseFailAlloc_3831_, 4, v_srcDir_3798_);
lean_ctor_set(v_reuseFailAlloc_3831_, 5, v_buildDir_3799_);
lean_ctor_set(v_reuseFailAlloc_3831_, 6, v_leanLibDir_3800_);
lean_ctor_set(v_reuseFailAlloc_3831_, 7, v_nativeLibDir_3801_);
lean_ctor_set(v_reuseFailAlloc_3831_, 8, v_binDir_3802_);
lean_ctor_set(v_reuseFailAlloc_3831_, 9, v_irDir_3803_);
lean_ctor_set(v_reuseFailAlloc_3831_, 10, v_releaseRepo_3804_);
lean_ctor_set(v_reuseFailAlloc_3831_, 11, v_buildArchive_3805_);
lean_ctor_set(v_reuseFailAlloc_3831_, 12, v_testDriver_3807_);
lean_ctor_set(v_reuseFailAlloc_3831_, 13, v_testDriverArgs_3808_);
lean_ctor_set(v_reuseFailAlloc_3831_, 14, v_lintDriver_3809_);
lean_ctor_set(v_reuseFailAlloc_3831_, 15, v_lintDriverArgs_3810_);
lean_ctor_set(v_reuseFailAlloc_3831_, 16, v_version_3811_);
lean_ctor_set(v_reuseFailAlloc_3831_, 17, v_versionTags_3812_);
lean_ctor_set(v_reuseFailAlloc_3831_, 18, v_description_3813_);
lean_ctor_set(v_reuseFailAlloc_3831_, 19, v_keywords_3814_);
lean_ctor_set(v_reuseFailAlloc_3831_, 20, v_homepage_3815_);
lean_ctor_set(v_reuseFailAlloc_3831_, 21, v_license_3816_);
lean_ctor_set(v_reuseFailAlloc_3831_, 22, v_licenseFiles_3817_);
lean_ctor_set(v_reuseFailAlloc_3831_, 23, v_readmeFile_3818_);
lean_ctor_set(v_reuseFailAlloc_3831_, 24, v_enableArtifactCache_x3f_3820_);
lean_ctor_set(v_reuseFailAlloc_3831_, 25, v_restoreAllArtifacts_x3f_3821_);
lean_ctor_set(v_reuseFailAlloc_3831_, 26, v_builtinLint_x3f_3823_);
lean_ctor_set(v_reuseFailAlloc_3831_, 27, v_checks_3824_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*28, v_bootstrap_3794_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*28 + 1, v_precompileModules_3796_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3806_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*28 + 3, v_reservoir_3819_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3822_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*28 + 6, v_fixedToolchain_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_ctor_set_uint8(v___x_3830_, sizeof(void*)*28 + 5, v_val_3790_);
return v___x_3830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1___boxed(lean_object* v_val_3833_, lean_object* v_cfg_3834_){
_start:
{
uint8_t v_val_141__boxed_3835_; lean_object* v_res_3836_; 
v_val_141__boxed_3835_ = lean_unbox(v_val_3833_);
v_res_3836_ = l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1(v_val_141__boxed_3835_, v_cfg_3834_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__2(lean_object* v_f_3837_, lean_object* v_cfg_3838_){
_start:
{
lean_object* v_toWorkspaceConfig_3839_; lean_object* v_toLeanConfig_3840_; uint8_t v_bootstrap_3841_; lean_object* v_extraDepTargets_3842_; uint8_t v_precompileModules_3843_; lean_object* v_moreGlobalServerArgs_3844_; lean_object* v_srcDir_3845_; lean_object* v_buildDir_3846_; lean_object* v_leanLibDir_3847_; lean_object* v_nativeLibDir_3848_; lean_object* v_binDir_3849_; lean_object* v_irDir_3850_; lean_object* v_releaseRepo_3851_; lean_object* v_buildArchive_3852_; uint8_t v_preferReleaseBuild_3853_; lean_object* v_testDriver_3854_; lean_object* v_testDriverArgs_3855_; lean_object* v_lintDriver_3856_; lean_object* v_lintDriverArgs_3857_; lean_object* v_version_3858_; lean_object* v_versionTags_3859_; lean_object* v_description_3860_; lean_object* v_keywords_3861_; lean_object* v_homepage_3862_; lean_object* v_license_3863_; lean_object* v_licenseFiles_3864_; lean_object* v_readmeFile_3865_; uint8_t v_reservoir_3866_; lean_object* v_enableArtifactCache_x3f_3867_; lean_object* v_restoreAllArtifacts_x3f_3868_; uint8_t v_libPrefixOnWindows_3869_; uint8_t v_allowImportAll_3870_; lean_object* v_builtinLint_x3f_3871_; lean_object* v_checks_3872_; uint8_t v_fixedToolchain_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3883_; 
v_toWorkspaceConfig_3839_ = lean_ctor_get(v_cfg_3838_, 0);
v_toLeanConfig_3840_ = lean_ctor_get(v_cfg_3838_, 1);
v_bootstrap_3841_ = lean_ctor_get_uint8(v_cfg_3838_, sizeof(void*)*28);
v_extraDepTargets_3842_ = lean_ctor_get(v_cfg_3838_, 2);
v_precompileModules_3843_ = lean_ctor_get_uint8(v_cfg_3838_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3844_ = lean_ctor_get(v_cfg_3838_, 3);
v_srcDir_3845_ = lean_ctor_get(v_cfg_3838_, 4);
v_buildDir_3846_ = lean_ctor_get(v_cfg_3838_, 5);
v_leanLibDir_3847_ = lean_ctor_get(v_cfg_3838_, 6);
v_nativeLibDir_3848_ = lean_ctor_get(v_cfg_3838_, 7);
v_binDir_3849_ = lean_ctor_get(v_cfg_3838_, 8);
v_irDir_3850_ = lean_ctor_get(v_cfg_3838_, 9);
v_releaseRepo_3851_ = lean_ctor_get(v_cfg_3838_, 10);
v_buildArchive_3852_ = lean_ctor_get(v_cfg_3838_, 11);
v_preferReleaseBuild_3853_ = lean_ctor_get_uint8(v_cfg_3838_, sizeof(void*)*28 + 2);
v_testDriver_3854_ = lean_ctor_get(v_cfg_3838_, 12);
v_testDriverArgs_3855_ = lean_ctor_get(v_cfg_3838_, 13);
v_lintDriver_3856_ = lean_ctor_get(v_cfg_3838_, 14);
v_lintDriverArgs_3857_ = lean_ctor_get(v_cfg_3838_, 15);
v_version_3858_ = lean_ctor_get(v_cfg_3838_, 16);
v_versionTags_3859_ = lean_ctor_get(v_cfg_3838_, 17);
v_description_3860_ = lean_ctor_get(v_cfg_3838_, 18);
v_keywords_3861_ = lean_ctor_get(v_cfg_3838_, 19);
v_homepage_3862_ = lean_ctor_get(v_cfg_3838_, 20);
v_license_3863_ = lean_ctor_get(v_cfg_3838_, 21);
v_licenseFiles_3864_ = lean_ctor_get(v_cfg_3838_, 22);
v_readmeFile_3865_ = lean_ctor_get(v_cfg_3838_, 23);
v_reservoir_3866_ = lean_ctor_get_uint8(v_cfg_3838_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3867_ = lean_ctor_get(v_cfg_3838_, 24);
v_restoreAllArtifacts_x3f_3868_ = lean_ctor_get(v_cfg_3838_, 25);
v_libPrefixOnWindows_3869_ = lean_ctor_get_uint8(v_cfg_3838_, sizeof(void*)*28 + 4);
v_allowImportAll_3870_ = lean_ctor_get_uint8(v_cfg_3838_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3871_ = lean_ctor_get(v_cfg_3838_, 26);
v_checks_3872_ = lean_ctor_get(v_cfg_3838_, 27);
v_fixedToolchain_3873_ = lean_ctor_get_uint8(v_cfg_3838_, sizeof(void*)*28 + 6);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_cfg_3838_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3875_ = v_cfg_3838_;
v_isShared_3876_ = v_isSharedCheck_3883_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_checks_3872_);
lean_inc(v_builtinLint_x3f_3871_);
lean_inc(v_restoreAllArtifacts_x3f_3868_);
lean_inc(v_enableArtifactCache_x3f_3867_);
lean_inc(v_readmeFile_3865_);
lean_inc(v_licenseFiles_3864_);
lean_inc(v_license_3863_);
lean_inc(v_homepage_3862_);
lean_inc(v_keywords_3861_);
lean_inc(v_description_3860_);
lean_inc(v_versionTags_3859_);
lean_inc(v_version_3858_);
lean_inc(v_lintDriverArgs_3857_);
lean_inc(v_lintDriver_3856_);
lean_inc(v_testDriverArgs_3855_);
lean_inc(v_testDriver_3854_);
lean_inc(v_buildArchive_3852_);
lean_inc(v_releaseRepo_3851_);
lean_inc(v_irDir_3850_);
lean_inc(v_binDir_3849_);
lean_inc(v_nativeLibDir_3848_);
lean_inc(v_leanLibDir_3847_);
lean_inc(v_buildDir_3846_);
lean_inc(v_srcDir_3845_);
lean_inc(v_moreGlobalServerArgs_3844_);
lean_inc(v_extraDepTargets_3842_);
lean_inc(v_toLeanConfig_3840_);
lean_inc(v_toWorkspaceConfig_3839_);
lean_dec(v_cfg_3838_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3883_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3880_; 
v___x_3877_ = lean_box(v_allowImportAll_3870_);
v___x_3878_ = lean_apply_1(v_f_3837_, v___x_3877_);
if (v_isShared_3876_ == 0)
{
v___x_3880_ = v___x_3875_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_toWorkspaceConfig_3839_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_toLeanConfig_3840_);
lean_ctor_set(v_reuseFailAlloc_3882_, 2, v_extraDepTargets_3842_);
lean_ctor_set(v_reuseFailAlloc_3882_, 3, v_moreGlobalServerArgs_3844_);
lean_ctor_set(v_reuseFailAlloc_3882_, 4, v_srcDir_3845_);
lean_ctor_set(v_reuseFailAlloc_3882_, 5, v_buildDir_3846_);
lean_ctor_set(v_reuseFailAlloc_3882_, 6, v_leanLibDir_3847_);
lean_ctor_set(v_reuseFailAlloc_3882_, 7, v_nativeLibDir_3848_);
lean_ctor_set(v_reuseFailAlloc_3882_, 8, v_binDir_3849_);
lean_ctor_set(v_reuseFailAlloc_3882_, 9, v_irDir_3850_);
lean_ctor_set(v_reuseFailAlloc_3882_, 10, v_releaseRepo_3851_);
lean_ctor_set(v_reuseFailAlloc_3882_, 11, v_buildArchive_3852_);
lean_ctor_set(v_reuseFailAlloc_3882_, 12, v_testDriver_3854_);
lean_ctor_set(v_reuseFailAlloc_3882_, 13, v_testDriverArgs_3855_);
lean_ctor_set(v_reuseFailAlloc_3882_, 14, v_lintDriver_3856_);
lean_ctor_set(v_reuseFailAlloc_3882_, 15, v_lintDriverArgs_3857_);
lean_ctor_set(v_reuseFailAlloc_3882_, 16, v_version_3858_);
lean_ctor_set(v_reuseFailAlloc_3882_, 17, v_versionTags_3859_);
lean_ctor_set(v_reuseFailAlloc_3882_, 18, v_description_3860_);
lean_ctor_set(v_reuseFailAlloc_3882_, 19, v_keywords_3861_);
lean_ctor_set(v_reuseFailAlloc_3882_, 20, v_homepage_3862_);
lean_ctor_set(v_reuseFailAlloc_3882_, 21, v_license_3863_);
lean_ctor_set(v_reuseFailAlloc_3882_, 22, v_licenseFiles_3864_);
lean_ctor_set(v_reuseFailAlloc_3882_, 23, v_readmeFile_3865_);
lean_ctor_set(v_reuseFailAlloc_3882_, 24, v_enableArtifactCache_x3f_3867_);
lean_ctor_set(v_reuseFailAlloc_3882_, 25, v_restoreAllArtifacts_x3f_3868_);
lean_ctor_set(v_reuseFailAlloc_3882_, 26, v_builtinLint_x3f_3871_);
lean_ctor_set(v_reuseFailAlloc_3882_, 27, v_checks_3872_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*28, v_bootstrap_3841_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*28 + 1, v_precompileModules_3843_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3853_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*28 + 3, v_reservoir_3866_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3869_);
v___x_3880_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
uint8_t v___x_3881_; 
v___x_3881_ = lean_unbox(v___x_3878_);
lean_ctor_set_uint8(v___x_3880_, sizeof(void*)*28 + 5, v___x_3881_);
lean_ctor_set_uint8(v___x_3880_, sizeof(void*)*28 + 6, v_fixedToolchain_3873_);
return v___x_3880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg(){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = ((lean_object*)(l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__3));
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___boxed(lean_object* v___dummy_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_Lake_PackageConfig_allowImportAll___proj___redArg();
return v_res_3895_;
}
}
static lean_object* _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0(void){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Lake_PackageConfig_allowImportAll___proj___redArg();
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object* v_p_3897_, lean_object* v_n_3898_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_obj_once(&l_Lake_PackageConfig_allowImportAll___proj___closed__0, &l_Lake_PackageConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object* v_p_3900_, lean_object* v_n_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3900_, v_n_3901_);
lean_dec(v_n_3901_);
lean_dec(v_p_3900_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___redArg(){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = lean_obj_once(&l_Lake_PackageConfig_allowImportAll___proj___closed__0, &l_Lake_PackageConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___redArg___boxed(lean_object* v___dummy_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_Lake_PackageConfig_allowImportAll_instConfigField___redArg();
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object* v_p_3907_, lean_object* v_n_3908_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = lean_obj_once(&l_Lake_PackageConfig_allowImportAll___proj___closed__0, &l_Lake_PackageConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object* v_p_3910_, lean_object* v_n_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lake_PackageConfig_allowImportAll_instConfigField(v_p_3910_, v_n_3911_);
lean_dec(v_n_3911_);
lean_dec(v_p_3910_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0(lean_object* v_cfg_3913_){
_start:
{
lean_object* v_builtinLint_x3f_3914_; 
v_builtinLint_x3f_3914_ = lean_ctor_get(v_cfg_3913_, 26);
lean_inc(v_builtinLint_x3f_3914_);
return v_builtinLint_x3f_3914_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0___boxed(lean_object* v_cfg_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0(v_cfg_3915_);
lean_dec_ref(v_cfg_3915_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__1(lean_object* v_val_3917_, lean_object* v_cfg_3918_){
_start:
{
lean_object* v_toWorkspaceConfig_3919_; lean_object* v_toLeanConfig_3920_; uint8_t v_bootstrap_3921_; lean_object* v_extraDepTargets_3922_; uint8_t v_precompileModules_3923_; lean_object* v_moreGlobalServerArgs_3924_; lean_object* v_srcDir_3925_; lean_object* v_buildDir_3926_; lean_object* v_leanLibDir_3927_; lean_object* v_nativeLibDir_3928_; lean_object* v_binDir_3929_; lean_object* v_irDir_3930_; lean_object* v_releaseRepo_3931_; lean_object* v_buildArchive_3932_; uint8_t v_preferReleaseBuild_3933_; lean_object* v_testDriver_3934_; lean_object* v_testDriverArgs_3935_; lean_object* v_lintDriver_3936_; lean_object* v_lintDriverArgs_3937_; lean_object* v_version_3938_; lean_object* v_versionTags_3939_; lean_object* v_description_3940_; lean_object* v_keywords_3941_; lean_object* v_homepage_3942_; lean_object* v_license_3943_; lean_object* v_licenseFiles_3944_; lean_object* v_readmeFile_3945_; uint8_t v_reservoir_3946_; lean_object* v_enableArtifactCache_x3f_3947_; lean_object* v_restoreAllArtifacts_x3f_3948_; uint8_t v_libPrefixOnWindows_3949_; uint8_t v_allowImportAll_3950_; lean_object* v_checks_3951_; uint8_t v_fixedToolchain_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3959_; 
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
v_checks_3951_ = lean_ctor_get(v_cfg_3918_, 27);
v_fixedToolchain_3952_ = lean_ctor_get_uint8(v_cfg_3918_, sizeof(void*)*28 + 6);
v_isSharedCheck_3959_ = !lean_is_exclusive(v_cfg_3918_);
if (v_isSharedCheck_3959_ == 0)
{
lean_object* v_unused_3960_; 
v_unused_3960_ = lean_ctor_get(v_cfg_3918_, 26);
lean_dec(v_unused_3960_);
v___x_3954_ = v_cfg_3918_;
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_checks_3951_);
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
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 26, v_val_3917_);
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_toWorkspaceConfig_3919_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v_toLeanConfig_3920_);
lean_ctor_set(v_reuseFailAlloc_3958_, 2, v_extraDepTargets_3922_);
lean_ctor_set(v_reuseFailAlloc_3958_, 3, v_moreGlobalServerArgs_3924_);
lean_ctor_set(v_reuseFailAlloc_3958_, 4, v_srcDir_3925_);
lean_ctor_set(v_reuseFailAlloc_3958_, 5, v_buildDir_3926_);
lean_ctor_set(v_reuseFailAlloc_3958_, 6, v_leanLibDir_3927_);
lean_ctor_set(v_reuseFailAlloc_3958_, 7, v_nativeLibDir_3928_);
lean_ctor_set(v_reuseFailAlloc_3958_, 8, v_binDir_3929_);
lean_ctor_set(v_reuseFailAlloc_3958_, 9, v_irDir_3930_);
lean_ctor_set(v_reuseFailAlloc_3958_, 10, v_releaseRepo_3931_);
lean_ctor_set(v_reuseFailAlloc_3958_, 11, v_buildArchive_3932_);
lean_ctor_set(v_reuseFailAlloc_3958_, 12, v_testDriver_3934_);
lean_ctor_set(v_reuseFailAlloc_3958_, 13, v_testDriverArgs_3935_);
lean_ctor_set(v_reuseFailAlloc_3958_, 14, v_lintDriver_3936_);
lean_ctor_set(v_reuseFailAlloc_3958_, 15, v_lintDriverArgs_3937_);
lean_ctor_set(v_reuseFailAlloc_3958_, 16, v_version_3938_);
lean_ctor_set(v_reuseFailAlloc_3958_, 17, v_versionTags_3939_);
lean_ctor_set(v_reuseFailAlloc_3958_, 18, v_description_3940_);
lean_ctor_set(v_reuseFailAlloc_3958_, 19, v_keywords_3941_);
lean_ctor_set(v_reuseFailAlloc_3958_, 20, v_homepage_3942_);
lean_ctor_set(v_reuseFailAlloc_3958_, 21, v_license_3943_);
lean_ctor_set(v_reuseFailAlloc_3958_, 22, v_licenseFiles_3944_);
lean_ctor_set(v_reuseFailAlloc_3958_, 23, v_readmeFile_3945_);
lean_ctor_set(v_reuseFailAlloc_3958_, 24, v_enableArtifactCache_x3f_3947_);
lean_ctor_set(v_reuseFailAlloc_3958_, 25, v_restoreAllArtifacts_x3f_3948_);
lean_ctor_set(v_reuseFailAlloc_3958_, 26, v_val_3917_);
lean_ctor_set(v_reuseFailAlloc_3958_, 27, v_checks_3951_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, sizeof(void*)*28, v_bootstrap_3921_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, sizeof(void*)*28 + 1, v_precompileModules_3923_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3933_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, sizeof(void*)*28 + 3, v_reservoir_3946_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3949_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, sizeof(void*)*28 + 5, v_allowImportAll_3950_);
lean_ctor_set_uint8(v_reuseFailAlloc_3958_, sizeof(void*)*28 + 6, v_fixedToolchain_3952_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__2(lean_object* v_f_3961_, lean_object* v_cfg_3962_){
_start:
{
lean_object* v_toWorkspaceConfig_3963_; lean_object* v_toLeanConfig_3964_; uint8_t v_bootstrap_3965_; lean_object* v_extraDepTargets_3966_; uint8_t v_precompileModules_3967_; lean_object* v_moreGlobalServerArgs_3968_; lean_object* v_srcDir_3969_; lean_object* v_buildDir_3970_; lean_object* v_leanLibDir_3971_; lean_object* v_nativeLibDir_3972_; lean_object* v_binDir_3973_; lean_object* v_irDir_3974_; lean_object* v_releaseRepo_3975_; lean_object* v_buildArchive_3976_; uint8_t v_preferReleaseBuild_3977_; lean_object* v_testDriver_3978_; lean_object* v_testDriverArgs_3979_; lean_object* v_lintDriver_3980_; lean_object* v_lintDriverArgs_3981_; lean_object* v_version_3982_; lean_object* v_versionTags_3983_; lean_object* v_description_3984_; lean_object* v_keywords_3985_; lean_object* v_homepage_3986_; lean_object* v_license_3987_; lean_object* v_licenseFiles_3988_; lean_object* v_readmeFile_3989_; uint8_t v_reservoir_3990_; lean_object* v_enableArtifactCache_x3f_3991_; lean_object* v_restoreAllArtifacts_x3f_3992_; uint8_t v_libPrefixOnWindows_3993_; uint8_t v_allowImportAll_3994_; lean_object* v_builtinLint_x3f_3995_; lean_object* v_checks_3996_; uint8_t v_fixedToolchain_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4005_; 
v_toWorkspaceConfig_3963_ = lean_ctor_get(v_cfg_3962_, 0);
v_toLeanConfig_3964_ = lean_ctor_get(v_cfg_3962_, 1);
v_bootstrap_3965_ = lean_ctor_get_uint8(v_cfg_3962_, sizeof(void*)*28);
v_extraDepTargets_3966_ = lean_ctor_get(v_cfg_3962_, 2);
v_precompileModules_3967_ = lean_ctor_get_uint8(v_cfg_3962_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3968_ = lean_ctor_get(v_cfg_3962_, 3);
v_srcDir_3969_ = lean_ctor_get(v_cfg_3962_, 4);
v_buildDir_3970_ = lean_ctor_get(v_cfg_3962_, 5);
v_leanLibDir_3971_ = lean_ctor_get(v_cfg_3962_, 6);
v_nativeLibDir_3972_ = lean_ctor_get(v_cfg_3962_, 7);
v_binDir_3973_ = lean_ctor_get(v_cfg_3962_, 8);
v_irDir_3974_ = lean_ctor_get(v_cfg_3962_, 9);
v_releaseRepo_3975_ = lean_ctor_get(v_cfg_3962_, 10);
v_buildArchive_3976_ = lean_ctor_get(v_cfg_3962_, 11);
v_preferReleaseBuild_3977_ = lean_ctor_get_uint8(v_cfg_3962_, sizeof(void*)*28 + 2);
v_testDriver_3978_ = lean_ctor_get(v_cfg_3962_, 12);
v_testDriverArgs_3979_ = lean_ctor_get(v_cfg_3962_, 13);
v_lintDriver_3980_ = lean_ctor_get(v_cfg_3962_, 14);
v_lintDriverArgs_3981_ = lean_ctor_get(v_cfg_3962_, 15);
v_version_3982_ = lean_ctor_get(v_cfg_3962_, 16);
v_versionTags_3983_ = lean_ctor_get(v_cfg_3962_, 17);
v_description_3984_ = lean_ctor_get(v_cfg_3962_, 18);
v_keywords_3985_ = lean_ctor_get(v_cfg_3962_, 19);
v_homepage_3986_ = lean_ctor_get(v_cfg_3962_, 20);
v_license_3987_ = lean_ctor_get(v_cfg_3962_, 21);
v_licenseFiles_3988_ = lean_ctor_get(v_cfg_3962_, 22);
v_readmeFile_3989_ = lean_ctor_get(v_cfg_3962_, 23);
v_reservoir_3990_ = lean_ctor_get_uint8(v_cfg_3962_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3991_ = lean_ctor_get(v_cfg_3962_, 24);
v_restoreAllArtifacts_x3f_3992_ = lean_ctor_get(v_cfg_3962_, 25);
v_libPrefixOnWindows_3993_ = lean_ctor_get_uint8(v_cfg_3962_, sizeof(void*)*28 + 4);
v_allowImportAll_3994_ = lean_ctor_get_uint8(v_cfg_3962_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3995_ = lean_ctor_get(v_cfg_3962_, 26);
v_checks_3996_ = lean_ctor_get(v_cfg_3962_, 27);
v_fixedToolchain_3997_ = lean_ctor_get_uint8(v_cfg_3962_, sizeof(void*)*28 + 6);
v_isSharedCheck_4005_ = !lean_is_exclusive(v_cfg_3962_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3999_ = v_cfg_3962_;
v_isShared_4000_ = v_isSharedCheck_4005_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_checks_3996_);
lean_inc(v_builtinLint_x3f_3995_);
lean_inc(v_restoreAllArtifacts_x3f_3992_);
lean_inc(v_enableArtifactCache_x3f_3991_);
lean_inc(v_readmeFile_3989_);
lean_inc(v_licenseFiles_3988_);
lean_inc(v_license_3987_);
lean_inc(v_homepage_3986_);
lean_inc(v_keywords_3985_);
lean_inc(v_description_3984_);
lean_inc(v_versionTags_3983_);
lean_inc(v_version_3982_);
lean_inc(v_lintDriverArgs_3981_);
lean_inc(v_lintDriver_3980_);
lean_inc(v_testDriverArgs_3979_);
lean_inc(v_testDriver_3978_);
lean_inc(v_buildArchive_3976_);
lean_inc(v_releaseRepo_3975_);
lean_inc(v_irDir_3974_);
lean_inc(v_binDir_3973_);
lean_inc(v_nativeLibDir_3972_);
lean_inc(v_leanLibDir_3971_);
lean_inc(v_buildDir_3970_);
lean_inc(v_srcDir_3969_);
lean_inc(v_moreGlobalServerArgs_3968_);
lean_inc(v_extraDepTargets_3966_);
lean_inc(v_toLeanConfig_3964_);
lean_inc(v_toWorkspaceConfig_3963_);
lean_dec(v_cfg_3962_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4005_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4001_; lean_object* v___x_4003_; 
v___x_4001_ = lean_apply_1(v_f_3961_, v_builtinLint_x3f_3995_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 26, v___x_4001_);
v___x_4003_ = v___x_3999_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_toWorkspaceConfig_3963_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_toLeanConfig_3964_);
lean_ctor_set(v_reuseFailAlloc_4004_, 2, v_extraDepTargets_3966_);
lean_ctor_set(v_reuseFailAlloc_4004_, 3, v_moreGlobalServerArgs_3968_);
lean_ctor_set(v_reuseFailAlloc_4004_, 4, v_srcDir_3969_);
lean_ctor_set(v_reuseFailAlloc_4004_, 5, v_buildDir_3970_);
lean_ctor_set(v_reuseFailAlloc_4004_, 6, v_leanLibDir_3971_);
lean_ctor_set(v_reuseFailAlloc_4004_, 7, v_nativeLibDir_3972_);
lean_ctor_set(v_reuseFailAlloc_4004_, 8, v_binDir_3973_);
lean_ctor_set(v_reuseFailAlloc_4004_, 9, v_irDir_3974_);
lean_ctor_set(v_reuseFailAlloc_4004_, 10, v_releaseRepo_3975_);
lean_ctor_set(v_reuseFailAlloc_4004_, 11, v_buildArchive_3976_);
lean_ctor_set(v_reuseFailAlloc_4004_, 12, v_testDriver_3978_);
lean_ctor_set(v_reuseFailAlloc_4004_, 13, v_testDriverArgs_3979_);
lean_ctor_set(v_reuseFailAlloc_4004_, 14, v_lintDriver_3980_);
lean_ctor_set(v_reuseFailAlloc_4004_, 15, v_lintDriverArgs_3981_);
lean_ctor_set(v_reuseFailAlloc_4004_, 16, v_version_3982_);
lean_ctor_set(v_reuseFailAlloc_4004_, 17, v_versionTags_3983_);
lean_ctor_set(v_reuseFailAlloc_4004_, 18, v_description_3984_);
lean_ctor_set(v_reuseFailAlloc_4004_, 19, v_keywords_3985_);
lean_ctor_set(v_reuseFailAlloc_4004_, 20, v_homepage_3986_);
lean_ctor_set(v_reuseFailAlloc_4004_, 21, v_license_3987_);
lean_ctor_set(v_reuseFailAlloc_4004_, 22, v_licenseFiles_3988_);
lean_ctor_set(v_reuseFailAlloc_4004_, 23, v_readmeFile_3989_);
lean_ctor_set(v_reuseFailAlloc_4004_, 24, v_enableArtifactCache_x3f_3991_);
lean_ctor_set(v_reuseFailAlloc_4004_, 25, v_restoreAllArtifacts_x3f_3992_);
lean_ctor_set(v_reuseFailAlloc_4004_, 26, v___x_4001_);
lean_ctor_set(v_reuseFailAlloc_4004_, 27, v_checks_3996_);
lean_ctor_set_uint8(v_reuseFailAlloc_4004_, sizeof(void*)*28, v_bootstrap_3965_);
lean_ctor_set_uint8(v_reuseFailAlloc_4004_, sizeof(void*)*28 + 1, v_precompileModules_3967_);
lean_ctor_set_uint8(v_reuseFailAlloc_4004_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3977_);
lean_ctor_set_uint8(v_reuseFailAlloc_4004_, sizeof(void*)*28 + 3, v_reservoir_3990_);
lean_ctor_set_uint8(v_reuseFailAlloc_4004_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3993_);
lean_ctor_set_uint8(v_reuseFailAlloc_4004_, sizeof(void*)*28 + 5, v_allowImportAll_3994_);
lean_ctor_set_uint8(v_reuseFailAlloc_4004_, sizeof(void*)*28 + 6, v_fixedToolchain_3997_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg(){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = ((lean_object*)(l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__3));
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___boxed(lean_object* v___dummy_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lake_PackageConfig_builtinLint_x3f___proj___redArg();
return v_res_4017_;
}
}
static lean_object* _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0(void){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l_Lake_PackageConfig_builtinLint_x3f___proj___redArg();
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj(lean_object* v_p_4019_, lean_object* v_n_4020_){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___boxed(lean_object* v_p_4022_, lean_object* v_n_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Lake_PackageConfig_builtinLint_x3f___proj(v_p_4022_, v_n_4023_);
lean_dec(v_n_4023_);
lean_dec(v_p_4022_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg();
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField(lean_object* v_p_4029_, lean_object* v_n_4030_){
_start:
{
lean_object* v___x_4031_; 
v___x_4031_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___boxed(lean_object* v_p_4032_, lean_object* v_n_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Lake_PackageConfig_builtinLint_x3f_instConfigField(v_p_4032_, v_n_4033_);
lean_dec(v_n_4033_);
lean_dec(v_p_4032_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___redArg(){
_start:
{
lean_object* v___x_4036_; 
v___x_4036_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___redArg___boxed(lean_object* v___dummy_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lake_PackageConfig_builtinLint_instConfigField___redArg();
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField(lean_object* v_p_4039_, lean_object* v_n_4040_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___boxed(lean_object* v_p_4042_, lean_object* v_n_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lake_PackageConfig_builtinLint_instConfigField(v_p_4042_, v_n_4043_);
lean_dec(v_n_4043_);
lean_dec(v_p_4042_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__0(lean_object* v_cfg_4045_){
_start:
{
lean_object* v_checks_4046_; 
v_checks_4046_ = lean_ctor_get(v_cfg_4045_, 27);
lean_inc_ref(v_checks_4046_);
return v_checks_4046_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__0___boxed(lean_object* v_cfg_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l_Lake_PackageConfig_checks___proj___redArg___lam__0(v_cfg_4047_);
lean_dec_ref(v_cfg_4047_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__1(lean_object* v_val_4049_, lean_object* v_cfg_4050_){
_start:
{
lean_object* v_toWorkspaceConfig_4051_; lean_object* v_toLeanConfig_4052_; uint8_t v_bootstrap_4053_; lean_object* v_extraDepTargets_4054_; uint8_t v_precompileModules_4055_; lean_object* v_moreGlobalServerArgs_4056_; lean_object* v_srcDir_4057_; lean_object* v_buildDir_4058_; lean_object* v_leanLibDir_4059_; lean_object* v_nativeLibDir_4060_; lean_object* v_binDir_4061_; lean_object* v_irDir_4062_; lean_object* v_releaseRepo_4063_; lean_object* v_buildArchive_4064_; uint8_t v_preferReleaseBuild_4065_; lean_object* v_testDriver_4066_; lean_object* v_testDriverArgs_4067_; lean_object* v_lintDriver_4068_; lean_object* v_lintDriverArgs_4069_; lean_object* v_version_4070_; lean_object* v_versionTags_4071_; lean_object* v_description_4072_; lean_object* v_keywords_4073_; lean_object* v_homepage_4074_; lean_object* v_license_4075_; lean_object* v_licenseFiles_4076_; lean_object* v_readmeFile_4077_; uint8_t v_reservoir_4078_; lean_object* v_enableArtifactCache_x3f_4079_; lean_object* v_restoreAllArtifacts_x3f_4080_; uint8_t v_libPrefixOnWindows_4081_; uint8_t v_allowImportAll_4082_; lean_object* v_builtinLint_x3f_4083_; uint8_t v_fixedToolchain_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
v_toWorkspaceConfig_4051_ = lean_ctor_get(v_cfg_4050_, 0);
v_toLeanConfig_4052_ = lean_ctor_get(v_cfg_4050_, 1);
v_bootstrap_4053_ = lean_ctor_get_uint8(v_cfg_4050_, sizeof(void*)*28);
v_extraDepTargets_4054_ = lean_ctor_get(v_cfg_4050_, 2);
v_precompileModules_4055_ = lean_ctor_get_uint8(v_cfg_4050_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4056_ = lean_ctor_get(v_cfg_4050_, 3);
v_srcDir_4057_ = lean_ctor_get(v_cfg_4050_, 4);
v_buildDir_4058_ = lean_ctor_get(v_cfg_4050_, 5);
v_leanLibDir_4059_ = lean_ctor_get(v_cfg_4050_, 6);
v_nativeLibDir_4060_ = lean_ctor_get(v_cfg_4050_, 7);
v_binDir_4061_ = lean_ctor_get(v_cfg_4050_, 8);
v_irDir_4062_ = lean_ctor_get(v_cfg_4050_, 9);
v_releaseRepo_4063_ = lean_ctor_get(v_cfg_4050_, 10);
v_buildArchive_4064_ = lean_ctor_get(v_cfg_4050_, 11);
v_preferReleaseBuild_4065_ = lean_ctor_get_uint8(v_cfg_4050_, sizeof(void*)*28 + 2);
v_testDriver_4066_ = lean_ctor_get(v_cfg_4050_, 12);
v_testDriverArgs_4067_ = lean_ctor_get(v_cfg_4050_, 13);
v_lintDriver_4068_ = lean_ctor_get(v_cfg_4050_, 14);
v_lintDriverArgs_4069_ = lean_ctor_get(v_cfg_4050_, 15);
v_version_4070_ = lean_ctor_get(v_cfg_4050_, 16);
v_versionTags_4071_ = lean_ctor_get(v_cfg_4050_, 17);
v_description_4072_ = lean_ctor_get(v_cfg_4050_, 18);
v_keywords_4073_ = lean_ctor_get(v_cfg_4050_, 19);
v_homepage_4074_ = lean_ctor_get(v_cfg_4050_, 20);
v_license_4075_ = lean_ctor_get(v_cfg_4050_, 21);
v_licenseFiles_4076_ = lean_ctor_get(v_cfg_4050_, 22);
v_readmeFile_4077_ = lean_ctor_get(v_cfg_4050_, 23);
v_reservoir_4078_ = lean_ctor_get_uint8(v_cfg_4050_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4079_ = lean_ctor_get(v_cfg_4050_, 24);
v_restoreAllArtifacts_x3f_4080_ = lean_ctor_get(v_cfg_4050_, 25);
v_libPrefixOnWindows_4081_ = lean_ctor_get_uint8(v_cfg_4050_, sizeof(void*)*28 + 4);
v_allowImportAll_4082_ = lean_ctor_get_uint8(v_cfg_4050_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4083_ = lean_ctor_get(v_cfg_4050_, 26);
v_fixedToolchain_4084_ = lean_ctor_get_uint8(v_cfg_4050_, sizeof(void*)*28 + 6);
v_isSharedCheck_4091_ = !lean_is_exclusive(v_cfg_4050_);
if (v_isSharedCheck_4091_ == 0)
{
lean_object* v_unused_4092_; 
v_unused_4092_ = lean_ctor_get(v_cfg_4050_, 27);
lean_dec(v_unused_4092_);
v___x_4086_ = v_cfg_4050_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_builtinLint_x3f_4083_);
lean_inc(v_restoreAllArtifacts_x3f_4080_);
lean_inc(v_enableArtifactCache_x3f_4079_);
lean_inc(v_readmeFile_4077_);
lean_inc(v_licenseFiles_4076_);
lean_inc(v_license_4075_);
lean_inc(v_homepage_4074_);
lean_inc(v_keywords_4073_);
lean_inc(v_description_4072_);
lean_inc(v_versionTags_4071_);
lean_inc(v_version_4070_);
lean_inc(v_lintDriverArgs_4069_);
lean_inc(v_lintDriver_4068_);
lean_inc(v_testDriverArgs_4067_);
lean_inc(v_testDriver_4066_);
lean_inc(v_buildArchive_4064_);
lean_inc(v_releaseRepo_4063_);
lean_inc(v_irDir_4062_);
lean_inc(v_binDir_4061_);
lean_inc(v_nativeLibDir_4060_);
lean_inc(v_leanLibDir_4059_);
lean_inc(v_buildDir_4058_);
lean_inc(v_srcDir_4057_);
lean_inc(v_moreGlobalServerArgs_4056_);
lean_inc(v_extraDepTargets_4054_);
lean_inc(v_toLeanConfig_4052_);
lean_inc(v_toWorkspaceConfig_4051_);
lean_dec(v_cfg_4050_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
lean_ctor_set(v___x_4086_, 27, v_val_4049_);
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_toWorkspaceConfig_4051_);
lean_ctor_set(v_reuseFailAlloc_4090_, 1, v_toLeanConfig_4052_);
lean_ctor_set(v_reuseFailAlloc_4090_, 2, v_extraDepTargets_4054_);
lean_ctor_set(v_reuseFailAlloc_4090_, 3, v_moreGlobalServerArgs_4056_);
lean_ctor_set(v_reuseFailAlloc_4090_, 4, v_srcDir_4057_);
lean_ctor_set(v_reuseFailAlloc_4090_, 5, v_buildDir_4058_);
lean_ctor_set(v_reuseFailAlloc_4090_, 6, v_leanLibDir_4059_);
lean_ctor_set(v_reuseFailAlloc_4090_, 7, v_nativeLibDir_4060_);
lean_ctor_set(v_reuseFailAlloc_4090_, 8, v_binDir_4061_);
lean_ctor_set(v_reuseFailAlloc_4090_, 9, v_irDir_4062_);
lean_ctor_set(v_reuseFailAlloc_4090_, 10, v_releaseRepo_4063_);
lean_ctor_set(v_reuseFailAlloc_4090_, 11, v_buildArchive_4064_);
lean_ctor_set(v_reuseFailAlloc_4090_, 12, v_testDriver_4066_);
lean_ctor_set(v_reuseFailAlloc_4090_, 13, v_testDriverArgs_4067_);
lean_ctor_set(v_reuseFailAlloc_4090_, 14, v_lintDriver_4068_);
lean_ctor_set(v_reuseFailAlloc_4090_, 15, v_lintDriverArgs_4069_);
lean_ctor_set(v_reuseFailAlloc_4090_, 16, v_version_4070_);
lean_ctor_set(v_reuseFailAlloc_4090_, 17, v_versionTags_4071_);
lean_ctor_set(v_reuseFailAlloc_4090_, 18, v_description_4072_);
lean_ctor_set(v_reuseFailAlloc_4090_, 19, v_keywords_4073_);
lean_ctor_set(v_reuseFailAlloc_4090_, 20, v_homepage_4074_);
lean_ctor_set(v_reuseFailAlloc_4090_, 21, v_license_4075_);
lean_ctor_set(v_reuseFailAlloc_4090_, 22, v_licenseFiles_4076_);
lean_ctor_set(v_reuseFailAlloc_4090_, 23, v_readmeFile_4077_);
lean_ctor_set(v_reuseFailAlloc_4090_, 24, v_enableArtifactCache_x3f_4079_);
lean_ctor_set(v_reuseFailAlloc_4090_, 25, v_restoreAllArtifacts_x3f_4080_);
lean_ctor_set(v_reuseFailAlloc_4090_, 26, v_builtinLint_x3f_4083_);
lean_ctor_set(v_reuseFailAlloc_4090_, 27, v_val_4049_);
lean_ctor_set_uint8(v_reuseFailAlloc_4090_, sizeof(void*)*28, v_bootstrap_4053_);
lean_ctor_set_uint8(v_reuseFailAlloc_4090_, sizeof(void*)*28 + 1, v_precompileModules_4055_);
lean_ctor_set_uint8(v_reuseFailAlloc_4090_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4065_);
lean_ctor_set_uint8(v_reuseFailAlloc_4090_, sizeof(void*)*28 + 3, v_reservoir_4078_);
lean_ctor_set_uint8(v_reuseFailAlloc_4090_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4081_);
lean_ctor_set_uint8(v_reuseFailAlloc_4090_, sizeof(void*)*28 + 5, v_allowImportAll_4082_);
lean_ctor_set_uint8(v_reuseFailAlloc_4090_, sizeof(void*)*28 + 6, v_fixedToolchain_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__2(lean_object* v_f_4093_, lean_object* v_cfg_4094_){
_start:
{
lean_object* v_toWorkspaceConfig_4095_; lean_object* v_toLeanConfig_4096_; uint8_t v_bootstrap_4097_; lean_object* v_extraDepTargets_4098_; uint8_t v_precompileModules_4099_; lean_object* v_moreGlobalServerArgs_4100_; lean_object* v_srcDir_4101_; lean_object* v_buildDir_4102_; lean_object* v_leanLibDir_4103_; lean_object* v_nativeLibDir_4104_; lean_object* v_binDir_4105_; lean_object* v_irDir_4106_; lean_object* v_releaseRepo_4107_; lean_object* v_buildArchive_4108_; uint8_t v_preferReleaseBuild_4109_; lean_object* v_testDriver_4110_; lean_object* v_testDriverArgs_4111_; lean_object* v_lintDriver_4112_; lean_object* v_lintDriverArgs_4113_; lean_object* v_version_4114_; lean_object* v_versionTags_4115_; lean_object* v_description_4116_; lean_object* v_keywords_4117_; lean_object* v_homepage_4118_; lean_object* v_license_4119_; lean_object* v_licenseFiles_4120_; lean_object* v_readmeFile_4121_; uint8_t v_reservoir_4122_; lean_object* v_enableArtifactCache_x3f_4123_; lean_object* v_restoreAllArtifacts_x3f_4124_; uint8_t v_libPrefixOnWindows_4125_; uint8_t v_allowImportAll_4126_; lean_object* v_builtinLint_x3f_4127_; lean_object* v_checks_4128_; uint8_t v_fixedToolchain_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4137_; 
v_toWorkspaceConfig_4095_ = lean_ctor_get(v_cfg_4094_, 0);
v_toLeanConfig_4096_ = lean_ctor_get(v_cfg_4094_, 1);
v_bootstrap_4097_ = lean_ctor_get_uint8(v_cfg_4094_, sizeof(void*)*28);
v_extraDepTargets_4098_ = lean_ctor_get(v_cfg_4094_, 2);
v_precompileModules_4099_ = lean_ctor_get_uint8(v_cfg_4094_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4100_ = lean_ctor_get(v_cfg_4094_, 3);
v_srcDir_4101_ = lean_ctor_get(v_cfg_4094_, 4);
v_buildDir_4102_ = lean_ctor_get(v_cfg_4094_, 5);
v_leanLibDir_4103_ = lean_ctor_get(v_cfg_4094_, 6);
v_nativeLibDir_4104_ = lean_ctor_get(v_cfg_4094_, 7);
v_binDir_4105_ = lean_ctor_get(v_cfg_4094_, 8);
v_irDir_4106_ = lean_ctor_get(v_cfg_4094_, 9);
v_releaseRepo_4107_ = lean_ctor_get(v_cfg_4094_, 10);
v_buildArchive_4108_ = lean_ctor_get(v_cfg_4094_, 11);
v_preferReleaseBuild_4109_ = lean_ctor_get_uint8(v_cfg_4094_, sizeof(void*)*28 + 2);
v_testDriver_4110_ = lean_ctor_get(v_cfg_4094_, 12);
v_testDriverArgs_4111_ = lean_ctor_get(v_cfg_4094_, 13);
v_lintDriver_4112_ = lean_ctor_get(v_cfg_4094_, 14);
v_lintDriverArgs_4113_ = lean_ctor_get(v_cfg_4094_, 15);
v_version_4114_ = lean_ctor_get(v_cfg_4094_, 16);
v_versionTags_4115_ = lean_ctor_get(v_cfg_4094_, 17);
v_description_4116_ = lean_ctor_get(v_cfg_4094_, 18);
v_keywords_4117_ = lean_ctor_get(v_cfg_4094_, 19);
v_homepage_4118_ = lean_ctor_get(v_cfg_4094_, 20);
v_license_4119_ = lean_ctor_get(v_cfg_4094_, 21);
v_licenseFiles_4120_ = lean_ctor_get(v_cfg_4094_, 22);
v_readmeFile_4121_ = lean_ctor_get(v_cfg_4094_, 23);
v_reservoir_4122_ = lean_ctor_get_uint8(v_cfg_4094_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4123_ = lean_ctor_get(v_cfg_4094_, 24);
v_restoreAllArtifacts_x3f_4124_ = lean_ctor_get(v_cfg_4094_, 25);
v_libPrefixOnWindows_4125_ = lean_ctor_get_uint8(v_cfg_4094_, sizeof(void*)*28 + 4);
v_allowImportAll_4126_ = lean_ctor_get_uint8(v_cfg_4094_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4127_ = lean_ctor_get(v_cfg_4094_, 26);
v_checks_4128_ = lean_ctor_get(v_cfg_4094_, 27);
v_fixedToolchain_4129_ = lean_ctor_get_uint8(v_cfg_4094_, sizeof(void*)*28 + 6);
v_isSharedCheck_4137_ = !lean_is_exclusive(v_cfg_4094_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4131_ = v_cfg_4094_;
v_isShared_4132_ = v_isSharedCheck_4137_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_checks_4128_);
lean_inc(v_builtinLint_x3f_4127_);
lean_inc(v_restoreAllArtifacts_x3f_4124_);
lean_inc(v_enableArtifactCache_x3f_4123_);
lean_inc(v_readmeFile_4121_);
lean_inc(v_licenseFiles_4120_);
lean_inc(v_license_4119_);
lean_inc(v_homepage_4118_);
lean_inc(v_keywords_4117_);
lean_inc(v_description_4116_);
lean_inc(v_versionTags_4115_);
lean_inc(v_version_4114_);
lean_inc(v_lintDriverArgs_4113_);
lean_inc(v_lintDriver_4112_);
lean_inc(v_testDriverArgs_4111_);
lean_inc(v_testDriver_4110_);
lean_inc(v_buildArchive_4108_);
lean_inc(v_releaseRepo_4107_);
lean_inc(v_irDir_4106_);
lean_inc(v_binDir_4105_);
lean_inc(v_nativeLibDir_4104_);
lean_inc(v_leanLibDir_4103_);
lean_inc(v_buildDir_4102_);
lean_inc(v_srcDir_4101_);
lean_inc(v_moreGlobalServerArgs_4100_);
lean_inc(v_extraDepTargets_4098_);
lean_inc(v_toLeanConfig_4096_);
lean_inc(v_toWorkspaceConfig_4095_);
lean_dec(v_cfg_4094_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4137_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4133_; lean_object* v___x_4135_; 
v___x_4133_ = lean_apply_1(v_f_4093_, v_checks_4128_);
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 27, v___x_4133_);
v___x_4135_ = v___x_4131_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_toWorkspaceConfig_4095_);
lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_toLeanConfig_4096_);
lean_ctor_set(v_reuseFailAlloc_4136_, 2, v_extraDepTargets_4098_);
lean_ctor_set(v_reuseFailAlloc_4136_, 3, v_moreGlobalServerArgs_4100_);
lean_ctor_set(v_reuseFailAlloc_4136_, 4, v_srcDir_4101_);
lean_ctor_set(v_reuseFailAlloc_4136_, 5, v_buildDir_4102_);
lean_ctor_set(v_reuseFailAlloc_4136_, 6, v_leanLibDir_4103_);
lean_ctor_set(v_reuseFailAlloc_4136_, 7, v_nativeLibDir_4104_);
lean_ctor_set(v_reuseFailAlloc_4136_, 8, v_binDir_4105_);
lean_ctor_set(v_reuseFailAlloc_4136_, 9, v_irDir_4106_);
lean_ctor_set(v_reuseFailAlloc_4136_, 10, v_releaseRepo_4107_);
lean_ctor_set(v_reuseFailAlloc_4136_, 11, v_buildArchive_4108_);
lean_ctor_set(v_reuseFailAlloc_4136_, 12, v_testDriver_4110_);
lean_ctor_set(v_reuseFailAlloc_4136_, 13, v_testDriverArgs_4111_);
lean_ctor_set(v_reuseFailAlloc_4136_, 14, v_lintDriver_4112_);
lean_ctor_set(v_reuseFailAlloc_4136_, 15, v_lintDriverArgs_4113_);
lean_ctor_set(v_reuseFailAlloc_4136_, 16, v_version_4114_);
lean_ctor_set(v_reuseFailAlloc_4136_, 17, v_versionTags_4115_);
lean_ctor_set(v_reuseFailAlloc_4136_, 18, v_description_4116_);
lean_ctor_set(v_reuseFailAlloc_4136_, 19, v_keywords_4117_);
lean_ctor_set(v_reuseFailAlloc_4136_, 20, v_homepage_4118_);
lean_ctor_set(v_reuseFailAlloc_4136_, 21, v_license_4119_);
lean_ctor_set(v_reuseFailAlloc_4136_, 22, v_licenseFiles_4120_);
lean_ctor_set(v_reuseFailAlloc_4136_, 23, v_readmeFile_4121_);
lean_ctor_set(v_reuseFailAlloc_4136_, 24, v_enableArtifactCache_x3f_4123_);
lean_ctor_set(v_reuseFailAlloc_4136_, 25, v_restoreAllArtifacts_x3f_4124_);
lean_ctor_set(v_reuseFailAlloc_4136_, 26, v_builtinLint_x3f_4127_);
lean_ctor_set(v_reuseFailAlloc_4136_, 27, v___x_4133_);
lean_ctor_set_uint8(v_reuseFailAlloc_4136_, sizeof(void*)*28, v_bootstrap_4097_);
lean_ctor_set_uint8(v_reuseFailAlloc_4136_, sizeof(void*)*28 + 1, v_precompileModules_4099_);
lean_ctor_set_uint8(v_reuseFailAlloc_4136_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4109_);
lean_ctor_set_uint8(v_reuseFailAlloc_4136_, sizeof(void*)*28 + 3, v_reservoir_4122_);
lean_ctor_set_uint8(v_reuseFailAlloc_4136_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4125_);
lean_ctor_set_uint8(v_reuseFailAlloc_4136_, sizeof(void*)*28 + 5, v_allowImportAll_4126_);
lean_ctor_set_uint8(v_reuseFailAlloc_4136_, sizeof(void*)*28 + 6, v_fixedToolchain_4129_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg(){
_start:
{
lean_object* v___x_4147_; 
v___x_4147_ = ((lean_object*)(l_Lake_PackageConfig_checks___proj___redArg___closed__3));
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___boxed(lean_object* v___dummy_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Lake_PackageConfig_checks___proj___redArg();
return v_res_4149_;
}
}
static lean_object* _init_l_Lake_PackageConfig_checks___proj___closed__0(void){
_start:
{
lean_object* v___x_4150_; 
v___x_4150_ = l_Lake_PackageConfig_checks___proj___redArg();
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj(lean_object* v_p_4151_, lean_object* v_n_4152_){
_start:
{
lean_object* v___x_4153_; 
v___x_4153_ = lean_obj_once(&l_Lake_PackageConfig_checks___proj___closed__0, &l_Lake_PackageConfig_checks___proj___closed__0_once, _init_l_Lake_PackageConfig_checks___proj___closed__0);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___boxed(lean_object* v_p_4154_, lean_object* v_n_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l_Lake_PackageConfig_checks___proj(v_p_4154_, v_n_4155_);
lean_dec(v_n_4155_);
lean_dec(v_p_4154_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___redArg(){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = lean_obj_once(&l_Lake_PackageConfig_checks___proj___closed__0, &l_Lake_PackageConfig_checks___proj___closed__0_once, _init_l_Lake_PackageConfig_checks___proj___closed__0);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___redArg___boxed(lean_object* v___dummy_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lake_PackageConfig_checks_instConfigField___redArg();
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField(lean_object* v_p_4161_, lean_object* v_n_4162_){
_start:
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_obj_once(&l_Lake_PackageConfig_checks___proj___closed__0, &l_Lake_PackageConfig_checks___proj___closed__0_once, _init_l_Lake_PackageConfig_checks___proj___closed__0);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___boxed(lean_object* v_p_4164_, lean_object* v_n_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lake_PackageConfig_checks_instConfigField(v_p_4164_, v_n_4165_);
lean_dec(v_n_4165_);
lean_dec(v_p_4164_);
return v_res_4166_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0(lean_object* v_cfg_4167_){
_start:
{
uint8_t v_fixedToolchain_4168_; 
v_fixedToolchain_4168_ = lean_ctor_get_uint8(v_cfg_4167_, sizeof(void*)*28 + 6);
return v_fixedToolchain_4168_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0___boxed(lean_object* v_cfg_4169_){
_start:
{
uint8_t v_res_4170_; lean_object* v_r_4171_; 
v_res_4170_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0(v_cfg_4169_);
lean_dec_ref(v_cfg_4169_);
v_r_4171_ = lean_box(v_res_4170_);
return v_r_4171_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1(uint8_t v_val_4172_, lean_object* v_cfg_4173_){
_start:
{
lean_object* v_toWorkspaceConfig_4174_; lean_object* v_toLeanConfig_4175_; uint8_t v_bootstrap_4176_; lean_object* v_extraDepTargets_4177_; uint8_t v_precompileModules_4178_; lean_object* v_moreGlobalServerArgs_4179_; lean_object* v_srcDir_4180_; lean_object* v_buildDir_4181_; lean_object* v_leanLibDir_4182_; lean_object* v_nativeLibDir_4183_; lean_object* v_binDir_4184_; lean_object* v_irDir_4185_; lean_object* v_releaseRepo_4186_; lean_object* v_buildArchive_4187_; uint8_t v_preferReleaseBuild_4188_; lean_object* v_testDriver_4189_; lean_object* v_testDriverArgs_4190_; lean_object* v_lintDriver_4191_; lean_object* v_lintDriverArgs_4192_; lean_object* v_version_4193_; lean_object* v_versionTags_4194_; lean_object* v_description_4195_; lean_object* v_keywords_4196_; lean_object* v_homepage_4197_; lean_object* v_license_4198_; lean_object* v_licenseFiles_4199_; lean_object* v_readmeFile_4200_; uint8_t v_reservoir_4201_; lean_object* v_enableArtifactCache_x3f_4202_; lean_object* v_restoreAllArtifacts_x3f_4203_; uint8_t v_libPrefixOnWindows_4204_; uint8_t v_allowImportAll_4205_; lean_object* v_builtinLint_x3f_4206_; lean_object* v_checks_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
v_toWorkspaceConfig_4174_ = lean_ctor_get(v_cfg_4173_, 0);
v_toLeanConfig_4175_ = lean_ctor_get(v_cfg_4173_, 1);
v_bootstrap_4176_ = lean_ctor_get_uint8(v_cfg_4173_, sizeof(void*)*28);
v_extraDepTargets_4177_ = lean_ctor_get(v_cfg_4173_, 2);
v_precompileModules_4178_ = lean_ctor_get_uint8(v_cfg_4173_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4179_ = lean_ctor_get(v_cfg_4173_, 3);
v_srcDir_4180_ = lean_ctor_get(v_cfg_4173_, 4);
v_buildDir_4181_ = lean_ctor_get(v_cfg_4173_, 5);
v_leanLibDir_4182_ = lean_ctor_get(v_cfg_4173_, 6);
v_nativeLibDir_4183_ = lean_ctor_get(v_cfg_4173_, 7);
v_binDir_4184_ = lean_ctor_get(v_cfg_4173_, 8);
v_irDir_4185_ = lean_ctor_get(v_cfg_4173_, 9);
v_releaseRepo_4186_ = lean_ctor_get(v_cfg_4173_, 10);
v_buildArchive_4187_ = lean_ctor_get(v_cfg_4173_, 11);
v_preferReleaseBuild_4188_ = lean_ctor_get_uint8(v_cfg_4173_, sizeof(void*)*28 + 2);
v_testDriver_4189_ = lean_ctor_get(v_cfg_4173_, 12);
v_testDriverArgs_4190_ = lean_ctor_get(v_cfg_4173_, 13);
v_lintDriver_4191_ = lean_ctor_get(v_cfg_4173_, 14);
v_lintDriverArgs_4192_ = lean_ctor_get(v_cfg_4173_, 15);
v_version_4193_ = lean_ctor_get(v_cfg_4173_, 16);
v_versionTags_4194_ = lean_ctor_get(v_cfg_4173_, 17);
v_description_4195_ = lean_ctor_get(v_cfg_4173_, 18);
v_keywords_4196_ = lean_ctor_get(v_cfg_4173_, 19);
v_homepage_4197_ = lean_ctor_get(v_cfg_4173_, 20);
v_license_4198_ = lean_ctor_get(v_cfg_4173_, 21);
v_licenseFiles_4199_ = lean_ctor_get(v_cfg_4173_, 22);
v_readmeFile_4200_ = lean_ctor_get(v_cfg_4173_, 23);
v_reservoir_4201_ = lean_ctor_get_uint8(v_cfg_4173_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4202_ = lean_ctor_get(v_cfg_4173_, 24);
v_restoreAllArtifacts_x3f_4203_ = lean_ctor_get(v_cfg_4173_, 25);
v_libPrefixOnWindows_4204_ = lean_ctor_get_uint8(v_cfg_4173_, sizeof(void*)*28 + 4);
v_allowImportAll_4205_ = lean_ctor_get_uint8(v_cfg_4173_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4206_ = lean_ctor_get(v_cfg_4173_, 26);
v_checks_4207_ = lean_ctor_get(v_cfg_4173_, 27);
v_isSharedCheck_4214_ = !lean_is_exclusive(v_cfg_4173_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v_cfg_4173_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_checks_4207_);
lean_inc(v_builtinLint_x3f_4206_);
lean_inc(v_restoreAllArtifacts_x3f_4203_);
lean_inc(v_enableArtifactCache_x3f_4202_);
lean_inc(v_readmeFile_4200_);
lean_inc(v_licenseFiles_4199_);
lean_inc(v_license_4198_);
lean_inc(v_homepage_4197_);
lean_inc(v_keywords_4196_);
lean_inc(v_description_4195_);
lean_inc(v_versionTags_4194_);
lean_inc(v_version_4193_);
lean_inc(v_lintDriverArgs_4192_);
lean_inc(v_lintDriver_4191_);
lean_inc(v_testDriverArgs_4190_);
lean_inc(v_testDriver_4189_);
lean_inc(v_buildArchive_4187_);
lean_inc(v_releaseRepo_4186_);
lean_inc(v_irDir_4185_);
lean_inc(v_binDir_4184_);
lean_inc(v_nativeLibDir_4183_);
lean_inc(v_leanLibDir_4182_);
lean_inc(v_buildDir_4181_);
lean_inc(v_srcDir_4180_);
lean_inc(v_moreGlobalServerArgs_4179_);
lean_inc(v_extraDepTargets_4177_);
lean_inc(v_toLeanConfig_4175_);
lean_inc(v_toWorkspaceConfig_4174_);
lean_dec(v_cfg_4173_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_toWorkspaceConfig_4174_);
lean_ctor_set(v_reuseFailAlloc_4213_, 1, v_toLeanConfig_4175_);
lean_ctor_set(v_reuseFailAlloc_4213_, 2, v_extraDepTargets_4177_);
lean_ctor_set(v_reuseFailAlloc_4213_, 3, v_moreGlobalServerArgs_4179_);
lean_ctor_set(v_reuseFailAlloc_4213_, 4, v_srcDir_4180_);
lean_ctor_set(v_reuseFailAlloc_4213_, 5, v_buildDir_4181_);
lean_ctor_set(v_reuseFailAlloc_4213_, 6, v_leanLibDir_4182_);
lean_ctor_set(v_reuseFailAlloc_4213_, 7, v_nativeLibDir_4183_);
lean_ctor_set(v_reuseFailAlloc_4213_, 8, v_binDir_4184_);
lean_ctor_set(v_reuseFailAlloc_4213_, 9, v_irDir_4185_);
lean_ctor_set(v_reuseFailAlloc_4213_, 10, v_releaseRepo_4186_);
lean_ctor_set(v_reuseFailAlloc_4213_, 11, v_buildArchive_4187_);
lean_ctor_set(v_reuseFailAlloc_4213_, 12, v_testDriver_4189_);
lean_ctor_set(v_reuseFailAlloc_4213_, 13, v_testDriverArgs_4190_);
lean_ctor_set(v_reuseFailAlloc_4213_, 14, v_lintDriver_4191_);
lean_ctor_set(v_reuseFailAlloc_4213_, 15, v_lintDriverArgs_4192_);
lean_ctor_set(v_reuseFailAlloc_4213_, 16, v_version_4193_);
lean_ctor_set(v_reuseFailAlloc_4213_, 17, v_versionTags_4194_);
lean_ctor_set(v_reuseFailAlloc_4213_, 18, v_description_4195_);
lean_ctor_set(v_reuseFailAlloc_4213_, 19, v_keywords_4196_);
lean_ctor_set(v_reuseFailAlloc_4213_, 20, v_homepage_4197_);
lean_ctor_set(v_reuseFailAlloc_4213_, 21, v_license_4198_);
lean_ctor_set(v_reuseFailAlloc_4213_, 22, v_licenseFiles_4199_);
lean_ctor_set(v_reuseFailAlloc_4213_, 23, v_readmeFile_4200_);
lean_ctor_set(v_reuseFailAlloc_4213_, 24, v_enableArtifactCache_x3f_4202_);
lean_ctor_set(v_reuseFailAlloc_4213_, 25, v_restoreAllArtifacts_x3f_4203_);
lean_ctor_set(v_reuseFailAlloc_4213_, 26, v_builtinLint_x3f_4206_);
lean_ctor_set(v_reuseFailAlloc_4213_, 27, v_checks_4207_);
lean_ctor_set_uint8(v_reuseFailAlloc_4213_, sizeof(void*)*28, v_bootstrap_4176_);
lean_ctor_set_uint8(v_reuseFailAlloc_4213_, sizeof(void*)*28 + 1, v_precompileModules_4178_);
lean_ctor_set_uint8(v_reuseFailAlloc_4213_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4188_);
lean_ctor_set_uint8(v_reuseFailAlloc_4213_, sizeof(void*)*28 + 3, v_reservoir_4201_);
lean_ctor_set_uint8(v_reuseFailAlloc_4213_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4204_);
lean_ctor_set_uint8(v_reuseFailAlloc_4213_, sizeof(void*)*28 + 5, v_allowImportAll_4205_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_ctor_set_uint8(v___x_4212_, sizeof(void*)*28 + 6, v_val_4172_);
return v___x_4212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1___boxed(lean_object* v_val_4215_, lean_object* v_cfg_4216_){
_start:
{
uint8_t v_val_141__boxed_4217_; lean_object* v_res_4218_; 
v_val_141__boxed_4217_ = lean_unbox(v_val_4215_);
v_res_4218_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1(v_val_141__boxed_4217_, v_cfg_4216_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__2(lean_object* v_f_4219_, lean_object* v_cfg_4220_){
_start:
{
lean_object* v_toWorkspaceConfig_4221_; lean_object* v_toLeanConfig_4222_; uint8_t v_bootstrap_4223_; lean_object* v_extraDepTargets_4224_; uint8_t v_precompileModules_4225_; lean_object* v_moreGlobalServerArgs_4226_; lean_object* v_srcDir_4227_; lean_object* v_buildDir_4228_; lean_object* v_leanLibDir_4229_; lean_object* v_nativeLibDir_4230_; lean_object* v_binDir_4231_; lean_object* v_irDir_4232_; lean_object* v_releaseRepo_4233_; lean_object* v_buildArchive_4234_; uint8_t v_preferReleaseBuild_4235_; lean_object* v_testDriver_4236_; lean_object* v_testDriverArgs_4237_; lean_object* v_lintDriver_4238_; lean_object* v_lintDriverArgs_4239_; lean_object* v_version_4240_; lean_object* v_versionTags_4241_; lean_object* v_description_4242_; lean_object* v_keywords_4243_; lean_object* v_homepage_4244_; lean_object* v_license_4245_; lean_object* v_licenseFiles_4246_; lean_object* v_readmeFile_4247_; uint8_t v_reservoir_4248_; lean_object* v_enableArtifactCache_x3f_4249_; lean_object* v_restoreAllArtifacts_x3f_4250_; uint8_t v_libPrefixOnWindows_4251_; uint8_t v_allowImportAll_4252_; lean_object* v_builtinLint_x3f_4253_; lean_object* v_checks_4254_; uint8_t v_fixedToolchain_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4265_; 
v_toWorkspaceConfig_4221_ = lean_ctor_get(v_cfg_4220_, 0);
v_toLeanConfig_4222_ = lean_ctor_get(v_cfg_4220_, 1);
v_bootstrap_4223_ = lean_ctor_get_uint8(v_cfg_4220_, sizeof(void*)*28);
v_extraDepTargets_4224_ = lean_ctor_get(v_cfg_4220_, 2);
v_precompileModules_4225_ = lean_ctor_get_uint8(v_cfg_4220_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4226_ = lean_ctor_get(v_cfg_4220_, 3);
v_srcDir_4227_ = lean_ctor_get(v_cfg_4220_, 4);
v_buildDir_4228_ = lean_ctor_get(v_cfg_4220_, 5);
v_leanLibDir_4229_ = lean_ctor_get(v_cfg_4220_, 6);
v_nativeLibDir_4230_ = lean_ctor_get(v_cfg_4220_, 7);
v_binDir_4231_ = lean_ctor_get(v_cfg_4220_, 8);
v_irDir_4232_ = lean_ctor_get(v_cfg_4220_, 9);
v_releaseRepo_4233_ = lean_ctor_get(v_cfg_4220_, 10);
v_buildArchive_4234_ = lean_ctor_get(v_cfg_4220_, 11);
v_preferReleaseBuild_4235_ = lean_ctor_get_uint8(v_cfg_4220_, sizeof(void*)*28 + 2);
v_testDriver_4236_ = lean_ctor_get(v_cfg_4220_, 12);
v_testDriverArgs_4237_ = lean_ctor_get(v_cfg_4220_, 13);
v_lintDriver_4238_ = lean_ctor_get(v_cfg_4220_, 14);
v_lintDriverArgs_4239_ = lean_ctor_get(v_cfg_4220_, 15);
v_version_4240_ = lean_ctor_get(v_cfg_4220_, 16);
v_versionTags_4241_ = lean_ctor_get(v_cfg_4220_, 17);
v_description_4242_ = lean_ctor_get(v_cfg_4220_, 18);
v_keywords_4243_ = lean_ctor_get(v_cfg_4220_, 19);
v_homepage_4244_ = lean_ctor_get(v_cfg_4220_, 20);
v_license_4245_ = lean_ctor_get(v_cfg_4220_, 21);
v_licenseFiles_4246_ = lean_ctor_get(v_cfg_4220_, 22);
v_readmeFile_4247_ = lean_ctor_get(v_cfg_4220_, 23);
v_reservoir_4248_ = lean_ctor_get_uint8(v_cfg_4220_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4249_ = lean_ctor_get(v_cfg_4220_, 24);
v_restoreAllArtifacts_x3f_4250_ = lean_ctor_get(v_cfg_4220_, 25);
v_libPrefixOnWindows_4251_ = lean_ctor_get_uint8(v_cfg_4220_, sizeof(void*)*28 + 4);
v_allowImportAll_4252_ = lean_ctor_get_uint8(v_cfg_4220_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4253_ = lean_ctor_get(v_cfg_4220_, 26);
v_checks_4254_ = lean_ctor_get(v_cfg_4220_, 27);
v_fixedToolchain_4255_ = lean_ctor_get_uint8(v_cfg_4220_, sizeof(void*)*28 + 6);
v_isSharedCheck_4265_ = !lean_is_exclusive(v_cfg_4220_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4257_ = v_cfg_4220_;
v_isShared_4258_ = v_isSharedCheck_4265_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_checks_4254_);
lean_inc(v_builtinLint_x3f_4253_);
lean_inc(v_restoreAllArtifacts_x3f_4250_);
lean_inc(v_enableArtifactCache_x3f_4249_);
lean_inc(v_readmeFile_4247_);
lean_inc(v_licenseFiles_4246_);
lean_inc(v_license_4245_);
lean_inc(v_homepage_4244_);
lean_inc(v_keywords_4243_);
lean_inc(v_description_4242_);
lean_inc(v_versionTags_4241_);
lean_inc(v_version_4240_);
lean_inc(v_lintDriverArgs_4239_);
lean_inc(v_lintDriver_4238_);
lean_inc(v_testDriverArgs_4237_);
lean_inc(v_testDriver_4236_);
lean_inc(v_buildArchive_4234_);
lean_inc(v_releaseRepo_4233_);
lean_inc(v_irDir_4232_);
lean_inc(v_binDir_4231_);
lean_inc(v_nativeLibDir_4230_);
lean_inc(v_leanLibDir_4229_);
lean_inc(v_buildDir_4228_);
lean_inc(v_srcDir_4227_);
lean_inc(v_moreGlobalServerArgs_4226_);
lean_inc(v_extraDepTargets_4224_);
lean_inc(v_toLeanConfig_4222_);
lean_inc(v_toWorkspaceConfig_4221_);
lean_dec(v_cfg_4220_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4265_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4262_; 
v___x_4259_ = lean_box(v_fixedToolchain_4255_);
v___x_4260_ = lean_apply_1(v_f_4219_, v___x_4259_);
if (v_isShared_4258_ == 0)
{
v___x_4262_ = v___x_4257_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_toWorkspaceConfig_4221_);
lean_ctor_set(v_reuseFailAlloc_4264_, 1, v_toLeanConfig_4222_);
lean_ctor_set(v_reuseFailAlloc_4264_, 2, v_extraDepTargets_4224_);
lean_ctor_set(v_reuseFailAlloc_4264_, 3, v_moreGlobalServerArgs_4226_);
lean_ctor_set(v_reuseFailAlloc_4264_, 4, v_srcDir_4227_);
lean_ctor_set(v_reuseFailAlloc_4264_, 5, v_buildDir_4228_);
lean_ctor_set(v_reuseFailAlloc_4264_, 6, v_leanLibDir_4229_);
lean_ctor_set(v_reuseFailAlloc_4264_, 7, v_nativeLibDir_4230_);
lean_ctor_set(v_reuseFailAlloc_4264_, 8, v_binDir_4231_);
lean_ctor_set(v_reuseFailAlloc_4264_, 9, v_irDir_4232_);
lean_ctor_set(v_reuseFailAlloc_4264_, 10, v_releaseRepo_4233_);
lean_ctor_set(v_reuseFailAlloc_4264_, 11, v_buildArchive_4234_);
lean_ctor_set(v_reuseFailAlloc_4264_, 12, v_testDriver_4236_);
lean_ctor_set(v_reuseFailAlloc_4264_, 13, v_testDriverArgs_4237_);
lean_ctor_set(v_reuseFailAlloc_4264_, 14, v_lintDriver_4238_);
lean_ctor_set(v_reuseFailAlloc_4264_, 15, v_lintDriverArgs_4239_);
lean_ctor_set(v_reuseFailAlloc_4264_, 16, v_version_4240_);
lean_ctor_set(v_reuseFailAlloc_4264_, 17, v_versionTags_4241_);
lean_ctor_set(v_reuseFailAlloc_4264_, 18, v_description_4242_);
lean_ctor_set(v_reuseFailAlloc_4264_, 19, v_keywords_4243_);
lean_ctor_set(v_reuseFailAlloc_4264_, 20, v_homepage_4244_);
lean_ctor_set(v_reuseFailAlloc_4264_, 21, v_license_4245_);
lean_ctor_set(v_reuseFailAlloc_4264_, 22, v_licenseFiles_4246_);
lean_ctor_set(v_reuseFailAlloc_4264_, 23, v_readmeFile_4247_);
lean_ctor_set(v_reuseFailAlloc_4264_, 24, v_enableArtifactCache_x3f_4249_);
lean_ctor_set(v_reuseFailAlloc_4264_, 25, v_restoreAllArtifacts_x3f_4250_);
lean_ctor_set(v_reuseFailAlloc_4264_, 26, v_builtinLint_x3f_4253_);
lean_ctor_set(v_reuseFailAlloc_4264_, 27, v_checks_4254_);
lean_ctor_set_uint8(v_reuseFailAlloc_4264_, sizeof(void*)*28, v_bootstrap_4223_);
lean_ctor_set_uint8(v_reuseFailAlloc_4264_, sizeof(void*)*28 + 1, v_precompileModules_4225_);
lean_ctor_set_uint8(v_reuseFailAlloc_4264_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4235_);
lean_ctor_set_uint8(v_reuseFailAlloc_4264_, sizeof(void*)*28 + 3, v_reservoir_4248_);
lean_ctor_set_uint8(v_reuseFailAlloc_4264_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4251_);
lean_ctor_set_uint8(v_reuseFailAlloc_4264_, sizeof(void*)*28 + 5, v_allowImportAll_4252_);
v___x_4262_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
uint8_t v___x_4263_; 
v___x_4263_ = lean_unbox(v___x_4260_);
lean_ctor_set_uint8(v___x_4262_, sizeof(void*)*28 + 6, v___x_4263_);
return v___x_4262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg(){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = ((lean_object*)(l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__3));
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___boxed(lean_object* v___dummy_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg();
return v_res_4277_;
}
}
static lean_object* _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0(void){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg();
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj(lean_object* v_p_4279_, lean_object* v_n_4280_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = lean_obj_once(&l_Lake_PackageConfig_fixedToolchain___proj___closed__0, &l_Lake_PackageConfig_fixedToolchain___proj___closed__0_once, _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___boxed(lean_object* v_p_4282_, lean_object* v_n_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_4282_, v_n_4283_);
lean_dec(v_n_4283_);
lean_dec(v_p_4282_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg(){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = lean_obj_once(&l_Lake_PackageConfig_fixedToolchain___proj___closed__0, &l_Lake_PackageConfig_fixedToolchain___proj___closed__0_once, _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg___boxed(lean_object* v___dummy_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg();
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField(lean_object* v_p_4289_, lean_object* v_n_4290_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = lean_obj_once(&l_Lake_PackageConfig_fixedToolchain___proj___closed__0, &l_Lake_PackageConfig_fixedToolchain___proj___closed__0_once, _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___boxed(lean_object* v_p_4292_, lean_object* v_n_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lake_PackageConfig_fixedToolchain_instConfigField(v_p_4292_, v_n_4293_);
lean_dec(v_n_4293_);
lean_dec(v_p_4292_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0(lean_object* v_cfg_4295_){
_start:
{
lean_object* v_toWorkspaceConfig_4296_; 
v_toWorkspaceConfig_4296_ = lean_ctor_get(v_cfg_4295_, 0);
lean_inc_ref(v_toWorkspaceConfig_4296_);
return v_toWorkspaceConfig_4296_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0___boxed(lean_object* v_cfg_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0(v_cfg_4297_);
lean_dec_ref(v_cfg_4297_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__1(lean_object* v_val_4299_, lean_object* v_cfg_4300_){
_start:
{
lean_object* v_toLeanConfig_4301_; uint8_t v_bootstrap_4302_; lean_object* v_extraDepTargets_4303_; uint8_t v_precompileModules_4304_; lean_object* v_moreGlobalServerArgs_4305_; lean_object* v_srcDir_4306_; lean_object* v_buildDir_4307_; lean_object* v_leanLibDir_4308_; lean_object* v_nativeLibDir_4309_; lean_object* v_binDir_4310_; lean_object* v_irDir_4311_; lean_object* v_releaseRepo_4312_; lean_object* v_buildArchive_4313_; uint8_t v_preferReleaseBuild_4314_; lean_object* v_testDriver_4315_; lean_object* v_testDriverArgs_4316_; lean_object* v_lintDriver_4317_; lean_object* v_lintDriverArgs_4318_; lean_object* v_version_4319_; lean_object* v_versionTags_4320_; lean_object* v_description_4321_; lean_object* v_keywords_4322_; lean_object* v_homepage_4323_; lean_object* v_license_4324_; lean_object* v_licenseFiles_4325_; lean_object* v_readmeFile_4326_; uint8_t v_reservoir_4327_; lean_object* v_enableArtifactCache_x3f_4328_; lean_object* v_restoreAllArtifacts_x3f_4329_; uint8_t v_libPrefixOnWindows_4330_; uint8_t v_allowImportAll_4331_; lean_object* v_builtinLint_x3f_4332_; lean_object* v_checks_4333_; uint8_t v_fixedToolchain_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
v_toLeanConfig_4301_ = lean_ctor_get(v_cfg_4300_, 1);
v_bootstrap_4302_ = lean_ctor_get_uint8(v_cfg_4300_, sizeof(void*)*28);
v_extraDepTargets_4303_ = lean_ctor_get(v_cfg_4300_, 2);
v_precompileModules_4304_ = lean_ctor_get_uint8(v_cfg_4300_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4305_ = lean_ctor_get(v_cfg_4300_, 3);
v_srcDir_4306_ = lean_ctor_get(v_cfg_4300_, 4);
v_buildDir_4307_ = lean_ctor_get(v_cfg_4300_, 5);
v_leanLibDir_4308_ = lean_ctor_get(v_cfg_4300_, 6);
v_nativeLibDir_4309_ = lean_ctor_get(v_cfg_4300_, 7);
v_binDir_4310_ = lean_ctor_get(v_cfg_4300_, 8);
v_irDir_4311_ = lean_ctor_get(v_cfg_4300_, 9);
v_releaseRepo_4312_ = lean_ctor_get(v_cfg_4300_, 10);
v_buildArchive_4313_ = lean_ctor_get(v_cfg_4300_, 11);
v_preferReleaseBuild_4314_ = lean_ctor_get_uint8(v_cfg_4300_, sizeof(void*)*28 + 2);
v_testDriver_4315_ = lean_ctor_get(v_cfg_4300_, 12);
v_testDriverArgs_4316_ = lean_ctor_get(v_cfg_4300_, 13);
v_lintDriver_4317_ = lean_ctor_get(v_cfg_4300_, 14);
v_lintDriverArgs_4318_ = lean_ctor_get(v_cfg_4300_, 15);
v_version_4319_ = lean_ctor_get(v_cfg_4300_, 16);
v_versionTags_4320_ = lean_ctor_get(v_cfg_4300_, 17);
v_description_4321_ = lean_ctor_get(v_cfg_4300_, 18);
v_keywords_4322_ = lean_ctor_get(v_cfg_4300_, 19);
v_homepage_4323_ = lean_ctor_get(v_cfg_4300_, 20);
v_license_4324_ = lean_ctor_get(v_cfg_4300_, 21);
v_licenseFiles_4325_ = lean_ctor_get(v_cfg_4300_, 22);
v_readmeFile_4326_ = lean_ctor_get(v_cfg_4300_, 23);
v_reservoir_4327_ = lean_ctor_get_uint8(v_cfg_4300_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4328_ = lean_ctor_get(v_cfg_4300_, 24);
v_restoreAllArtifacts_x3f_4329_ = lean_ctor_get(v_cfg_4300_, 25);
v_libPrefixOnWindows_4330_ = lean_ctor_get_uint8(v_cfg_4300_, sizeof(void*)*28 + 4);
v_allowImportAll_4331_ = lean_ctor_get_uint8(v_cfg_4300_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4332_ = lean_ctor_get(v_cfg_4300_, 26);
v_checks_4333_ = lean_ctor_get(v_cfg_4300_, 27);
v_fixedToolchain_4334_ = lean_ctor_get_uint8(v_cfg_4300_, sizeof(void*)*28 + 6);
v_isSharedCheck_4341_ = !lean_is_exclusive(v_cfg_4300_);
if (v_isSharedCheck_4341_ == 0)
{
lean_object* v_unused_4342_; 
v_unused_4342_ = lean_ctor_get(v_cfg_4300_, 0);
lean_dec(v_unused_4342_);
v___x_4336_ = v_cfg_4300_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_checks_4333_);
lean_inc(v_builtinLint_x3f_4332_);
lean_inc(v_restoreAllArtifacts_x3f_4329_);
lean_inc(v_enableArtifactCache_x3f_4328_);
lean_inc(v_readmeFile_4326_);
lean_inc(v_licenseFiles_4325_);
lean_inc(v_license_4324_);
lean_inc(v_homepage_4323_);
lean_inc(v_keywords_4322_);
lean_inc(v_description_4321_);
lean_inc(v_versionTags_4320_);
lean_inc(v_version_4319_);
lean_inc(v_lintDriverArgs_4318_);
lean_inc(v_lintDriver_4317_);
lean_inc(v_testDriverArgs_4316_);
lean_inc(v_testDriver_4315_);
lean_inc(v_buildArchive_4313_);
lean_inc(v_releaseRepo_4312_);
lean_inc(v_irDir_4311_);
lean_inc(v_binDir_4310_);
lean_inc(v_nativeLibDir_4309_);
lean_inc(v_leanLibDir_4308_);
lean_inc(v_buildDir_4307_);
lean_inc(v_srcDir_4306_);
lean_inc(v_moreGlobalServerArgs_4305_);
lean_inc(v_extraDepTargets_4303_);
lean_inc(v_toLeanConfig_4301_);
lean_dec(v_cfg_4300_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
lean_ctor_set(v___x_4336_, 0, v_val_4299_);
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_val_4299_);
lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_toLeanConfig_4301_);
lean_ctor_set(v_reuseFailAlloc_4340_, 2, v_extraDepTargets_4303_);
lean_ctor_set(v_reuseFailAlloc_4340_, 3, v_moreGlobalServerArgs_4305_);
lean_ctor_set(v_reuseFailAlloc_4340_, 4, v_srcDir_4306_);
lean_ctor_set(v_reuseFailAlloc_4340_, 5, v_buildDir_4307_);
lean_ctor_set(v_reuseFailAlloc_4340_, 6, v_leanLibDir_4308_);
lean_ctor_set(v_reuseFailAlloc_4340_, 7, v_nativeLibDir_4309_);
lean_ctor_set(v_reuseFailAlloc_4340_, 8, v_binDir_4310_);
lean_ctor_set(v_reuseFailAlloc_4340_, 9, v_irDir_4311_);
lean_ctor_set(v_reuseFailAlloc_4340_, 10, v_releaseRepo_4312_);
lean_ctor_set(v_reuseFailAlloc_4340_, 11, v_buildArchive_4313_);
lean_ctor_set(v_reuseFailAlloc_4340_, 12, v_testDriver_4315_);
lean_ctor_set(v_reuseFailAlloc_4340_, 13, v_testDriverArgs_4316_);
lean_ctor_set(v_reuseFailAlloc_4340_, 14, v_lintDriver_4317_);
lean_ctor_set(v_reuseFailAlloc_4340_, 15, v_lintDriverArgs_4318_);
lean_ctor_set(v_reuseFailAlloc_4340_, 16, v_version_4319_);
lean_ctor_set(v_reuseFailAlloc_4340_, 17, v_versionTags_4320_);
lean_ctor_set(v_reuseFailAlloc_4340_, 18, v_description_4321_);
lean_ctor_set(v_reuseFailAlloc_4340_, 19, v_keywords_4322_);
lean_ctor_set(v_reuseFailAlloc_4340_, 20, v_homepage_4323_);
lean_ctor_set(v_reuseFailAlloc_4340_, 21, v_license_4324_);
lean_ctor_set(v_reuseFailAlloc_4340_, 22, v_licenseFiles_4325_);
lean_ctor_set(v_reuseFailAlloc_4340_, 23, v_readmeFile_4326_);
lean_ctor_set(v_reuseFailAlloc_4340_, 24, v_enableArtifactCache_x3f_4328_);
lean_ctor_set(v_reuseFailAlloc_4340_, 25, v_restoreAllArtifacts_x3f_4329_);
lean_ctor_set(v_reuseFailAlloc_4340_, 26, v_builtinLint_x3f_4332_);
lean_ctor_set(v_reuseFailAlloc_4340_, 27, v_checks_4333_);
lean_ctor_set_uint8(v_reuseFailAlloc_4340_, sizeof(void*)*28, v_bootstrap_4302_);
lean_ctor_set_uint8(v_reuseFailAlloc_4340_, sizeof(void*)*28 + 1, v_precompileModules_4304_);
lean_ctor_set_uint8(v_reuseFailAlloc_4340_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4314_);
lean_ctor_set_uint8(v_reuseFailAlloc_4340_, sizeof(void*)*28 + 3, v_reservoir_4327_);
lean_ctor_set_uint8(v_reuseFailAlloc_4340_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4330_);
lean_ctor_set_uint8(v_reuseFailAlloc_4340_, sizeof(void*)*28 + 5, v_allowImportAll_4331_);
lean_ctor_set_uint8(v_reuseFailAlloc_4340_, sizeof(void*)*28 + 6, v_fixedToolchain_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__2(lean_object* v_f_4343_, lean_object* v_cfg_4344_){
_start:
{
lean_object* v_toWorkspaceConfig_4345_; lean_object* v_toLeanConfig_4346_; uint8_t v_bootstrap_4347_; lean_object* v_extraDepTargets_4348_; uint8_t v_precompileModules_4349_; lean_object* v_moreGlobalServerArgs_4350_; lean_object* v_srcDir_4351_; lean_object* v_buildDir_4352_; lean_object* v_leanLibDir_4353_; lean_object* v_nativeLibDir_4354_; lean_object* v_binDir_4355_; lean_object* v_irDir_4356_; lean_object* v_releaseRepo_4357_; lean_object* v_buildArchive_4358_; uint8_t v_preferReleaseBuild_4359_; lean_object* v_testDriver_4360_; lean_object* v_testDriverArgs_4361_; lean_object* v_lintDriver_4362_; lean_object* v_lintDriverArgs_4363_; lean_object* v_version_4364_; lean_object* v_versionTags_4365_; lean_object* v_description_4366_; lean_object* v_keywords_4367_; lean_object* v_homepage_4368_; lean_object* v_license_4369_; lean_object* v_licenseFiles_4370_; lean_object* v_readmeFile_4371_; uint8_t v_reservoir_4372_; lean_object* v_enableArtifactCache_x3f_4373_; lean_object* v_restoreAllArtifacts_x3f_4374_; uint8_t v_libPrefixOnWindows_4375_; uint8_t v_allowImportAll_4376_; lean_object* v_builtinLint_x3f_4377_; lean_object* v_checks_4378_; uint8_t v_fixedToolchain_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4387_; 
v_toWorkspaceConfig_4345_ = lean_ctor_get(v_cfg_4344_, 0);
v_toLeanConfig_4346_ = lean_ctor_get(v_cfg_4344_, 1);
v_bootstrap_4347_ = lean_ctor_get_uint8(v_cfg_4344_, sizeof(void*)*28);
v_extraDepTargets_4348_ = lean_ctor_get(v_cfg_4344_, 2);
v_precompileModules_4349_ = lean_ctor_get_uint8(v_cfg_4344_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4350_ = lean_ctor_get(v_cfg_4344_, 3);
v_srcDir_4351_ = lean_ctor_get(v_cfg_4344_, 4);
v_buildDir_4352_ = lean_ctor_get(v_cfg_4344_, 5);
v_leanLibDir_4353_ = lean_ctor_get(v_cfg_4344_, 6);
v_nativeLibDir_4354_ = lean_ctor_get(v_cfg_4344_, 7);
v_binDir_4355_ = lean_ctor_get(v_cfg_4344_, 8);
v_irDir_4356_ = lean_ctor_get(v_cfg_4344_, 9);
v_releaseRepo_4357_ = lean_ctor_get(v_cfg_4344_, 10);
v_buildArchive_4358_ = lean_ctor_get(v_cfg_4344_, 11);
v_preferReleaseBuild_4359_ = lean_ctor_get_uint8(v_cfg_4344_, sizeof(void*)*28 + 2);
v_testDriver_4360_ = lean_ctor_get(v_cfg_4344_, 12);
v_testDriverArgs_4361_ = lean_ctor_get(v_cfg_4344_, 13);
v_lintDriver_4362_ = lean_ctor_get(v_cfg_4344_, 14);
v_lintDriverArgs_4363_ = lean_ctor_get(v_cfg_4344_, 15);
v_version_4364_ = lean_ctor_get(v_cfg_4344_, 16);
v_versionTags_4365_ = lean_ctor_get(v_cfg_4344_, 17);
v_description_4366_ = lean_ctor_get(v_cfg_4344_, 18);
v_keywords_4367_ = lean_ctor_get(v_cfg_4344_, 19);
v_homepage_4368_ = lean_ctor_get(v_cfg_4344_, 20);
v_license_4369_ = lean_ctor_get(v_cfg_4344_, 21);
v_licenseFiles_4370_ = lean_ctor_get(v_cfg_4344_, 22);
v_readmeFile_4371_ = lean_ctor_get(v_cfg_4344_, 23);
v_reservoir_4372_ = lean_ctor_get_uint8(v_cfg_4344_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4373_ = lean_ctor_get(v_cfg_4344_, 24);
v_restoreAllArtifacts_x3f_4374_ = lean_ctor_get(v_cfg_4344_, 25);
v_libPrefixOnWindows_4375_ = lean_ctor_get_uint8(v_cfg_4344_, sizeof(void*)*28 + 4);
v_allowImportAll_4376_ = lean_ctor_get_uint8(v_cfg_4344_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4377_ = lean_ctor_get(v_cfg_4344_, 26);
v_checks_4378_ = lean_ctor_get(v_cfg_4344_, 27);
v_fixedToolchain_4379_ = lean_ctor_get_uint8(v_cfg_4344_, sizeof(void*)*28 + 6);
v_isSharedCheck_4387_ = !lean_is_exclusive(v_cfg_4344_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4381_ = v_cfg_4344_;
v_isShared_4382_ = v_isSharedCheck_4387_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_checks_4378_);
lean_inc(v_builtinLint_x3f_4377_);
lean_inc(v_restoreAllArtifacts_x3f_4374_);
lean_inc(v_enableArtifactCache_x3f_4373_);
lean_inc(v_readmeFile_4371_);
lean_inc(v_licenseFiles_4370_);
lean_inc(v_license_4369_);
lean_inc(v_homepage_4368_);
lean_inc(v_keywords_4367_);
lean_inc(v_description_4366_);
lean_inc(v_versionTags_4365_);
lean_inc(v_version_4364_);
lean_inc(v_lintDriverArgs_4363_);
lean_inc(v_lintDriver_4362_);
lean_inc(v_testDriverArgs_4361_);
lean_inc(v_testDriver_4360_);
lean_inc(v_buildArchive_4358_);
lean_inc(v_releaseRepo_4357_);
lean_inc(v_irDir_4356_);
lean_inc(v_binDir_4355_);
lean_inc(v_nativeLibDir_4354_);
lean_inc(v_leanLibDir_4353_);
lean_inc(v_buildDir_4352_);
lean_inc(v_srcDir_4351_);
lean_inc(v_moreGlobalServerArgs_4350_);
lean_inc(v_extraDepTargets_4348_);
lean_inc(v_toLeanConfig_4346_);
lean_inc(v_toWorkspaceConfig_4345_);
lean_dec(v_cfg_4344_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4387_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4383_; lean_object* v___x_4385_; 
v___x_4383_ = lean_apply_1(v_f_4343_, v_toWorkspaceConfig_4345_);
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 0, v___x_4383_);
v___x_4385_ = v___x_4381_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4383_);
lean_ctor_set(v_reuseFailAlloc_4386_, 1, v_toLeanConfig_4346_);
lean_ctor_set(v_reuseFailAlloc_4386_, 2, v_extraDepTargets_4348_);
lean_ctor_set(v_reuseFailAlloc_4386_, 3, v_moreGlobalServerArgs_4350_);
lean_ctor_set(v_reuseFailAlloc_4386_, 4, v_srcDir_4351_);
lean_ctor_set(v_reuseFailAlloc_4386_, 5, v_buildDir_4352_);
lean_ctor_set(v_reuseFailAlloc_4386_, 6, v_leanLibDir_4353_);
lean_ctor_set(v_reuseFailAlloc_4386_, 7, v_nativeLibDir_4354_);
lean_ctor_set(v_reuseFailAlloc_4386_, 8, v_binDir_4355_);
lean_ctor_set(v_reuseFailAlloc_4386_, 9, v_irDir_4356_);
lean_ctor_set(v_reuseFailAlloc_4386_, 10, v_releaseRepo_4357_);
lean_ctor_set(v_reuseFailAlloc_4386_, 11, v_buildArchive_4358_);
lean_ctor_set(v_reuseFailAlloc_4386_, 12, v_testDriver_4360_);
lean_ctor_set(v_reuseFailAlloc_4386_, 13, v_testDriverArgs_4361_);
lean_ctor_set(v_reuseFailAlloc_4386_, 14, v_lintDriver_4362_);
lean_ctor_set(v_reuseFailAlloc_4386_, 15, v_lintDriverArgs_4363_);
lean_ctor_set(v_reuseFailAlloc_4386_, 16, v_version_4364_);
lean_ctor_set(v_reuseFailAlloc_4386_, 17, v_versionTags_4365_);
lean_ctor_set(v_reuseFailAlloc_4386_, 18, v_description_4366_);
lean_ctor_set(v_reuseFailAlloc_4386_, 19, v_keywords_4367_);
lean_ctor_set(v_reuseFailAlloc_4386_, 20, v_homepage_4368_);
lean_ctor_set(v_reuseFailAlloc_4386_, 21, v_license_4369_);
lean_ctor_set(v_reuseFailAlloc_4386_, 22, v_licenseFiles_4370_);
lean_ctor_set(v_reuseFailAlloc_4386_, 23, v_readmeFile_4371_);
lean_ctor_set(v_reuseFailAlloc_4386_, 24, v_enableArtifactCache_x3f_4373_);
lean_ctor_set(v_reuseFailAlloc_4386_, 25, v_restoreAllArtifacts_x3f_4374_);
lean_ctor_set(v_reuseFailAlloc_4386_, 26, v_builtinLint_x3f_4377_);
lean_ctor_set(v_reuseFailAlloc_4386_, 27, v_checks_4378_);
lean_ctor_set_uint8(v_reuseFailAlloc_4386_, sizeof(void*)*28, v_bootstrap_4347_);
lean_ctor_set_uint8(v_reuseFailAlloc_4386_, sizeof(void*)*28 + 1, v_precompileModules_4349_);
lean_ctor_set_uint8(v_reuseFailAlloc_4386_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4359_);
lean_ctor_set_uint8(v_reuseFailAlloc_4386_, sizeof(void*)*28 + 3, v_reservoir_4372_);
lean_ctor_set_uint8(v_reuseFailAlloc_4386_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4375_);
lean_ctor_set_uint8(v_reuseFailAlloc_4386_, sizeof(void*)*28 + 5, v_allowImportAll_4376_);
lean_ctor_set_uint8(v_reuseFailAlloc_4386_, sizeof(void*)*28 + 6, v_fixedToolchain_4379_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3(lean_object* v_x_4388_){
_start:
{
lean_object* v___x_4389_; 
v___x_4389_ = l_Lake_defaultPackagesDir;
return v___x_4389_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3___boxed(lean_object* v_x_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3(v_x_4390_);
lean_dec_ref(v_x_4390_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg(){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = ((lean_object*)(l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__4));
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___boxed(lean_object* v___dummy_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg();
return v_res_4404_;
}
}
static lean_object* _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0(void){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg();
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object* v_p_4406_, lean_object* v_n_4407_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = lean_obj_once(&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0, &l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object* v_p_4409_, lean_object* v_n_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_4409_, v_n_4410_);
lean_dec(v_n_4410_);
lean_dec(v_p_4409_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg(){
_start:
{
lean_object* v___x_4413_; 
v___x_4413_ = lean_obj_once(&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0, &l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg___boxed(lean_object* v___dummy_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg();
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object* v_p_4416_, lean_object* v_n_4417_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = lean_obj_once(&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0, &l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object* v_p_4419_, lean_object* v_n_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(v_p_4419_, v_n_4420_);
lean_dec(v_n_4420_);
lean_dec(v_p_4419_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0(lean_object* v_cfg_4422_){
_start:
{
lean_object* v_toLeanConfig_4423_; 
v_toLeanConfig_4423_ = lean_ctor_get(v_cfg_4422_, 1);
lean_inc_ref(v_toLeanConfig_4423_);
return v_toLeanConfig_4423_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0___boxed(lean_object* v_cfg_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0(v_cfg_4424_);
lean_dec_ref(v_cfg_4424_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__1(lean_object* v_val_4426_, lean_object* v_cfg_4427_){
_start:
{
lean_object* v_toWorkspaceConfig_4428_; uint8_t v_bootstrap_4429_; lean_object* v_extraDepTargets_4430_; uint8_t v_precompileModules_4431_; lean_object* v_moreGlobalServerArgs_4432_; lean_object* v_srcDir_4433_; lean_object* v_buildDir_4434_; lean_object* v_leanLibDir_4435_; lean_object* v_nativeLibDir_4436_; lean_object* v_binDir_4437_; lean_object* v_irDir_4438_; lean_object* v_releaseRepo_4439_; lean_object* v_buildArchive_4440_; uint8_t v_preferReleaseBuild_4441_; lean_object* v_testDriver_4442_; lean_object* v_testDriverArgs_4443_; lean_object* v_lintDriver_4444_; lean_object* v_lintDriverArgs_4445_; lean_object* v_version_4446_; lean_object* v_versionTags_4447_; lean_object* v_description_4448_; lean_object* v_keywords_4449_; lean_object* v_homepage_4450_; lean_object* v_license_4451_; lean_object* v_licenseFiles_4452_; lean_object* v_readmeFile_4453_; uint8_t v_reservoir_4454_; lean_object* v_enableArtifactCache_x3f_4455_; lean_object* v_restoreAllArtifacts_x3f_4456_; uint8_t v_libPrefixOnWindows_4457_; uint8_t v_allowImportAll_4458_; lean_object* v_builtinLint_x3f_4459_; lean_object* v_checks_4460_; uint8_t v_fixedToolchain_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
v_toWorkspaceConfig_4428_ = lean_ctor_get(v_cfg_4427_, 0);
v_bootstrap_4429_ = lean_ctor_get_uint8(v_cfg_4427_, sizeof(void*)*28);
v_extraDepTargets_4430_ = lean_ctor_get(v_cfg_4427_, 2);
v_precompileModules_4431_ = lean_ctor_get_uint8(v_cfg_4427_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4432_ = lean_ctor_get(v_cfg_4427_, 3);
v_srcDir_4433_ = lean_ctor_get(v_cfg_4427_, 4);
v_buildDir_4434_ = lean_ctor_get(v_cfg_4427_, 5);
v_leanLibDir_4435_ = lean_ctor_get(v_cfg_4427_, 6);
v_nativeLibDir_4436_ = lean_ctor_get(v_cfg_4427_, 7);
v_binDir_4437_ = lean_ctor_get(v_cfg_4427_, 8);
v_irDir_4438_ = lean_ctor_get(v_cfg_4427_, 9);
v_releaseRepo_4439_ = lean_ctor_get(v_cfg_4427_, 10);
v_buildArchive_4440_ = lean_ctor_get(v_cfg_4427_, 11);
v_preferReleaseBuild_4441_ = lean_ctor_get_uint8(v_cfg_4427_, sizeof(void*)*28 + 2);
v_testDriver_4442_ = lean_ctor_get(v_cfg_4427_, 12);
v_testDriverArgs_4443_ = lean_ctor_get(v_cfg_4427_, 13);
v_lintDriver_4444_ = lean_ctor_get(v_cfg_4427_, 14);
v_lintDriverArgs_4445_ = lean_ctor_get(v_cfg_4427_, 15);
v_version_4446_ = lean_ctor_get(v_cfg_4427_, 16);
v_versionTags_4447_ = lean_ctor_get(v_cfg_4427_, 17);
v_description_4448_ = lean_ctor_get(v_cfg_4427_, 18);
v_keywords_4449_ = lean_ctor_get(v_cfg_4427_, 19);
v_homepage_4450_ = lean_ctor_get(v_cfg_4427_, 20);
v_license_4451_ = lean_ctor_get(v_cfg_4427_, 21);
v_licenseFiles_4452_ = lean_ctor_get(v_cfg_4427_, 22);
v_readmeFile_4453_ = lean_ctor_get(v_cfg_4427_, 23);
v_reservoir_4454_ = lean_ctor_get_uint8(v_cfg_4427_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4455_ = lean_ctor_get(v_cfg_4427_, 24);
v_restoreAllArtifacts_x3f_4456_ = lean_ctor_get(v_cfg_4427_, 25);
v_libPrefixOnWindows_4457_ = lean_ctor_get_uint8(v_cfg_4427_, sizeof(void*)*28 + 4);
v_allowImportAll_4458_ = lean_ctor_get_uint8(v_cfg_4427_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4459_ = lean_ctor_get(v_cfg_4427_, 26);
v_checks_4460_ = lean_ctor_get(v_cfg_4427_, 27);
v_fixedToolchain_4461_ = lean_ctor_get_uint8(v_cfg_4427_, sizeof(void*)*28 + 6);
v_isSharedCheck_4468_ = !lean_is_exclusive(v_cfg_4427_);
if (v_isSharedCheck_4468_ == 0)
{
lean_object* v_unused_4469_; 
v_unused_4469_ = lean_ctor_get(v_cfg_4427_, 1);
lean_dec(v_unused_4469_);
v___x_4463_ = v_cfg_4427_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_checks_4460_);
lean_inc(v_builtinLint_x3f_4459_);
lean_inc(v_restoreAllArtifacts_x3f_4456_);
lean_inc(v_enableArtifactCache_x3f_4455_);
lean_inc(v_readmeFile_4453_);
lean_inc(v_licenseFiles_4452_);
lean_inc(v_license_4451_);
lean_inc(v_homepage_4450_);
lean_inc(v_keywords_4449_);
lean_inc(v_description_4448_);
lean_inc(v_versionTags_4447_);
lean_inc(v_version_4446_);
lean_inc(v_lintDriverArgs_4445_);
lean_inc(v_lintDriver_4444_);
lean_inc(v_testDriverArgs_4443_);
lean_inc(v_testDriver_4442_);
lean_inc(v_buildArchive_4440_);
lean_inc(v_releaseRepo_4439_);
lean_inc(v_irDir_4438_);
lean_inc(v_binDir_4437_);
lean_inc(v_nativeLibDir_4436_);
lean_inc(v_leanLibDir_4435_);
lean_inc(v_buildDir_4434_);
lean_inc(v_srcDir_4433_);
lean_inc(v_moreGlobalServerArgs_4432_);
lean_inc(v_extraDepTargets_4430_);
lean_inc(v_toWorkspaceConfig_4428_);
lean_dec(v_cfg_4427_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 1, v_val_4426_);
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_toWorkspaceConfig_4428_);
lean_ctor_set(v_reuseFailAlloc_4467_, 1, v_val_4426_);
lean_ctor_set(v_reuseFailAlloc_4467_, 2, v_extraDepTargets_4430_);
lean_ctor_set(v_reuseFailAlloc_4467_, 3, v_moreGlobalServerArgs_4432_);
lean_ctor_set(v_reuseFailAlloc_4467_, 4, v_srcDir_4433_);
lean_ctor_set(v_reuseFailAlloc_4467_, 5, v_buildDir_4434_);
lean_ctor_set(v_reuseFailAlloc_4467_, 6, v_leanLibDir_4435_);
lean_ctor_set(v_reuseFailAlloc_4467_, 7, v_nativeLibDir_4436_);
lean_ctor_set(v_reuseFailAlloc_4467_, 8, v_binDir_4437_);
lean_ctor_set(v_reuseFailAlloc_4467_, 9, v_irDir_4438_);
lean_ctor_set(v_reuseFailAlloc_4467_, 10, v_releaseRepo_4439_);
lean_ctor_set(v_reuseFailAlloc_4467_, 11, v_buildArchive_4440_);
lean_ctor_set(v_reuseFailAlloc_4467_, 12, v_testDriver_4442_);
lean_ctor_set(v_reuseFailAlloc_4467_, 13, v_testDriverArgs_4443_);
lean_ctor_set(v_reuseFailAlloc_4467_, 14, v_lintDriver_4444_);
lean_ctor_set(v_reuseFailAlloc_4467_, 15, v_lintDriverArgs_4445_);
lean_ctor_set(v_reuseFailAlloc_4467_, 16, v_version_4446_);
lean_ctor_set(v_reuseFailAlloc_4467_, 17, v_versionTags_4447_);
lean_ctor_set(v_reuseFailAlloc_4467_, 18, v_description_4448_);
lean_ctor_set(v_reuseFailAlloc_4467_, 19, v_keywords_4449_);
lean_ctor_set(v_reuseFailAlloc_4467_, 20, v_homepage_4450_);
lean_ctor_set(v_reuseFailAlloc_4467_, 21, v_license_4451_);
lean_ctor_set(v_reuseFailAlloc_4467_, 22, v_licenseFiles_4452_);
lean_ctor_set(v_reuseFailAlloc_4467_, 23, v_readmeFile_4453_);
lean_ctor_set(v_reuseFailAlloc_4467_, 24, v_enableArtifactCache_x3f_4455_);
lean_ctor_set(v_reuseFailAlloc_4467_, 25, v_restoreAllArtifacts_x3f_4456_);
lean_ctor_set(v_reuseFailAlloc_4467_, 26, v_builtinLint_x3f_4459_);
lean_ctor_set(v_reuseFailAlloc_4467_, 27, v_checks_4460_);
lean_ctor_set_uint8(v_reuseFailAlloc_4467_, sizeof(void*)*28, v_bootstrap_4429_);
lean_ctor_set_uint8(v_reuseFailAlloc_4467_, sizeof(void*)*28 + 1, v_precompileModules_4431_);
lean_ctor_set_uint8(v_reuseFailAlloc_4467_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4441_);
lean_ctor_set_uint8(v_reuseFailAlloc_4467_, sizeof(void*)*28 + 3, v_reservoir_4454_);
lean_ctor_set_uint8(v_reuseFailAlloc_4467_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4457_);
lean_ctor_set_uint8(v_reuseFailAlloc_4467_, sizeof(void*)*28 + 5, v_allowImportAll_4458_);
lean_ctor_set_uint8(v_reuseFailAlloc_4467_, sizeof(void*)*28 + 6, v_fixedToolchain_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__2(lean_object* v_f_4470_, lean_object* v_cfg_4471_){
_start:
{
lean_object* v_toWorkspaceConfig_4472_; lean_object* v_toLeanConfig_4473_; uint8_t v_bootstrap_4474_; lean_object* v_extraDepTargets_4475_; uint8_t v_precompileModules_4476_; lean_object* v_moreGlobalServerArgs_4477_; lean_object* v_srcDir_4478_; lean_object* v_buildDir_4479_; lean_object* v_leanLibDir_4480_; lean_object* v_nativeLibDir_4481_; lean_object* v_binDir_4482_; lean_object* v_irDir_4483_; lean_object* v_releaseRepo_4484_; lean_object* v_buildArchive_4485_; uint8_t v_preferReleaseBuild_4486_; lean_object* v_testDriver_4487_; lean_object* v_testDriverArgs_4488_; lean_object* v_lintDriver_4489_; lean_object* v_lintDriverArgs_4490_; lean_object* v_version_4491_; lean_object* v_versionTags_4492_; lean_object* v_description_4493_; lean_object* v_keywords_4494_; lean_object* v_homepage_4495_; lean_object* v_license_4496_; lean_object* v_licenseFiles_4497_; lean_object* v_readmeFile_4498_; uint8_t v_reservoir_4499_; lean_object* v_enableArtifactCache_x3f_4500_; lean_object* v_restoreAllArtifacts_x3f_4501_; uint8_t v_libPrefixOnWindows_4502_; uint8_t v_allowImportAll_4503_; lean_object* v_builtinLint_x3f_4504_; lean_object* v_checks_4505_; uint8_t v_fixedToolchain_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4514_; 
v_toWorkspaceConfig_4472_ = lean_ctor_get(v_cfg_4471_, 0);
v_toLeanConfig_4473_ = lean_ctor_get(v_cfg_4471_, 1);
v_bootstrap_4474_ = lean_ctor_get_uint8(v_cfg_4471_, sizeof(void*)*28);
v_extraDepTargets_4475_ = lean_ctor_get(v_cfg_4471_, 2);
v_precompileModules_4476_ = lean_ctor_get_uint8(v_cfg_4471_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4477_ = lean_ctor_get(v_cfg_4471_, 3);
v_srcDir_4478_ = lean_ctor_get(v_cfg_4471_, 4);
v_buildDir_4479_ = lean_ctor_get(v_cfg_4471_, 5);
v_leanLibDir_4480_ = lean_ctor_get(v_cfg_4471_, 6);
v_nativeLibDir_4481_ = lean_ctor_get(v_cfg_4471_, 7);
v_binDir_4482_ = lean_ctor_get(v_cfg_4471_, 8);
v_irDir_4483_ = lean_ctor_get(v_cfg_4471_, 9);
v_releaseRepo_4484_ = lean_ctor_get(v_cfg_4471_, 10);
v_buildArchive_4485_ = lean_ctor_get(v_cfg_4471_, 11);
v_preferReleaseBuild_4486_ = lean_ctor_get_uint8(v_cfg_4471_, sizeof(void*)*28 + 2);
v_testDriver_4487_ = lean_ctor_get(v_cfg_4471_, 12);
v_testDriverArgs_4488_ = lean_ctor_get(v_cfg_4471_, 13);
v_lintDriver_4489_ = lean_ctor_get(v_cfg_4471_, 14);
v_lintDriverArgs_4490_ = lean_ctor_get(v_cfg_4471_, 15);
v_version_4491_ = lean_ctor_get(v_cfg_4471_, 16);
v_versionTags_4492_ = lean_ctor_get(v_cfg_4471_, 17);
v_description_4493_ = lean_ctor_get(v_cfg_4471_, 18);
v_keywords_4494_ = lean_ctor_get(v_cfg_4471_, 19);
v_homepage_4495_ = lean_ctor_get(v_cfg_4471_, 20);
v_license_4496_ = lean_ctor_get(v_cfg_4471_, 21);
v_licenseFiles_4497_ = lean_ctor_get(v_cfg_4471_, 22);
v_readmeFile_4498_ = lean_ctor_get(v_cfg_4471_, 23);
v_reservoir_4499_ = lean_ctor_get_uint8(v_cfg_4471_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4500_ = lean_ctor_get(v_cfg_4471_, 24);
v_restoreAllArtifacts_x3f_4501_ = lean_ctor_get(v_cfg_4471_, 25);
v_libPrefixOnWindows_4502_ = lean_ctor_get_uint8(v_cfg_4471_, sizeof(void*)*28 + 4);
v_allowImportAll_4503_ = lean_ctor_get_uint8(v_cfg_4471_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4504_ = lean_ctor_get(v_cfg_4471_, 26);
v_checks_4505_ = lean_ctor_get(v_cfg_4471_, 27);
v_fixedToolchain_4506_ = lean_ctor_get_uint8(v_cfg_4471_, sizeof(void*)*28 + 6);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_cfg_4471_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4508_ = v_cfg_4471_;
v_isShared_4509_ = v_isSharedCheck_4514_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_checks_4505_);
lean_inc(v_builtinLint_x3f_4504_);
lean_inc(v_restoreAllArtifacts_x3f_4501_);
lean_inc(v_enableArtifactCache_x3f_4500_);
lean_inc(v_readmeFile_4498_);
lean_inc(v_licenseFiles_4497_);
lean_inc(v_license_4496_);
lean_inc(v_homepage_4495_);
lean_inc(v_keywords_4494_);
lean_inc(v_description_4493_);
lean_inc(v_versionTags_4492_);
lean_inc(v_version_4491_);
lean_inc(v_lintDriverArgs_4490_);
lean_inc(v_lintDriver_4489_);
lean_inc(v_testDriverArgs_4488_);
lean_inc(v_testDriver_4487_);
lean_inc(v_buildArchive_4485_);
lean_inc(v_releaseRepo_4484_);
lean_inc(v_irDir_4483_);
lean_inc(v_binDir_4482_);
lean_inc(v_nativeLibDir_4481_);
lean_inc(v_leanLibDir_4480_);
lean_inc(v_buildDir_4479_);
lean_inc(v_srcDir_4478_);
lean_inc(v_moreGlobalServerArgs_4477_);
lean_inc(v_extraDepTargets_4475_);
lean_inc(v_toLeanConfig_4473_);
lean_inc(v_toWorkspaceConfig_4472_);
lean_dec(v_cfg_4471_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4514_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4510_; lean_object* v___x_4512_; 
v___x_4510_ = lean_apply_1(v_f_4470_, v_toLeanConfig_4473_);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 1, v___x_4510_);
v___x_4512_ = v___x_4508_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_toWorkspaceConfig_4472_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v___x_4510_);
lean_ctor_set(v_reuseFailAlloc_4513_, 2, v_extraDepTargets_4475_);
lean_ctor_set(v_reuseFailAlloc_4513_, 3, v_moreGlobalServerArgs_4477_);
lean_ctor_set(v_reuseFailAlloc_4513_, 4, v_srcDir_4478_);
lean_ctor_set(v_reuseFailAlloc_4513_, 5, v_buildDir_4479_);
lean_ctor_set(v_reuseFailAlloc_4513_, 6, v_leanLibDir_4480_);
lean_ctor_set(v_reuseFailAlloc_4513_, 7, v_nativeLibDir_4481_);
lean_ctor_set(v_reuseFailAlloc_4513_, 8, v_binDir_4482_);
lean_ctor_set(v_reuseFailAlloc_4513_, 9, v_irDir_4483_);
lean_ctor_set(v_reuseFailAlloc_4513_, 10, v_releaseRepo_4484_);
lean_ctor_set(v_reuseFailAlloc_4513_, 11, v_buildArchive_4485_);
lean_ctor_set(v_reuseFailAlloc_4513_, 12, v_testDriver_4487_);
lean_ctor_set(v_reuseFailAlloc_4513_, 13, v_testDriverArgs_4488_);
lean_ctor_set(v_reuseFailAlloc_4513_, 14, v_lintDriver_4489_);
lean_ctor_set(v_reuseFailAlloc_4513_, 15, v_lintDriverArgs_4490_);
lean_ctor_set(v_reuseFailAlloc_4513_, 16, v_version_4491_);
lean_ctor_set(v_reuseFailAlloc_4513_, 17, v_versionTags_4492_);
lean_ctor_set(v_reuseFailAlloc_4513_, 18, v_description_4493_);
lean_ctor_set(v_reuseFailAlloc_4513_, 19, v_keywords_4494_);
lean_ctor_set(v_reuseFailAlloc_4513_, 20, v_homepage_4495_);
lean_ctor_set(v_reuseFailAlloc_4513_, 21, v_license_4496_);
lean_ctor_set(v_reuseFailAlloc_4513_, 22, v_licenseFiles_4497_);
lean_ctor_set(v_reuseFailAlloc_4513_, 23, v_readmeFile_4498_);
lean_ctor_set(v_reuseFailAlloc_4513_, 24, v_enableArtifactCache_x3f_4500_);
lean_ctor_set(v_reuseFailAlloc_4513_, 25, v_restoreAllArtifacts_x3f_4501_);
lean_ctor_set(v_reuseFailAlloc_4513_, 26, v_builtinLint_x3f_4504_);
lean_ctor_set(v_reuseFailAlloc_4513_, 27, v_checks_4505_);
lean_ctor_set_uint8(v_reuseFailAlloc_4513_, sizeof(void*)*28, v_bootstrap_4474_);
lean_ctor_set_uint8(v_reuseFailAlloc_4513_, sizeof(void*)*28 + 1, v_precompileModules_4476_);
lean_ctor_set_uint8(v_reuseFailAlloc_4513_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4486_);
lean_ctor_set_uint8(v_reuseFailAlloc_4513_, sizeof(void*)*28 + 3, v_reservoir_4499_);
lean_ctor_set_uint8(v_reuseFailAlloc_4513_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4502_);
lean_ctor_set_uint8(v_reuseFailAlloc_4513_, sizeof(void*)*28 + 5, v_allowImportAll_4503_);
lean_ctor_set_uint8(v_reuseFailAlloc_4513_, sizeof(void*)*28 + 6, v_fixedToolchain_4506_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3(lean_object* v_x_4523_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__1));
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___boxed(lean_object* v_x_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3(v_x_4525_);
lean_dec_ref(v_x_4525_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg(){
_start:
{
lean_object* v___x_4537_; 
v___x_4537_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__4));
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___boxed(lean_object* v___dummy_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg();
return v_res_4539_;
}
}
static lean_object* _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0(void){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg();
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object* v_p_4541_, lean_object* v_n_4542_){
_start:
{
lean_object* v___x_4543_; 
v___x_4543_ = lean_obj_once(&l_Lake_PackageConfig_toLeanConfig___proj___closed__0, &l_Lake_PackageConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___boxed(lean_object* v_p_4544_, lean_object* v_n_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_4544_, v_n_4545_);
lean_dec(v_n_4545_);
lean_dec(v_p_4544_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg(){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = lean_obj_once(&l_Lake_PackageConfig_toLeanConfig___proj___closed__0, &l_Lake_PackageConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg___boxed(lean_object* v___dummy_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg();
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent(lean_object* v_p_4551_, lean_object* v_n_4552_){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = lean_obj_once(&l_Lake_PackageConfig_toLeanConfig___proj___closed__0, &l_Lake_PackageConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_p_4554_, lean_object* v_n_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent(v_p_4554_, v_n_4555_);
lean_dec(v_n_4555_);
lean_dec(v_p_4554_);
return v_res_4556_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4566_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__3));
v___x_4567_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__0));
v___x_4568_ = lean_array_push(v___x_4567_, v___x_4566_);
return v___x_4568_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4576_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__7));
v___x_4577_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__4, &l_Lake_PackageConfig___fields___closed__4_once, _init_l_Lake_PackageConfig___fields___closed__4);
v___x_4578_ = lean_array_push(v___x_4577_, v___x_4576_);
return v___x_4578_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4586_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__11));
v___x_4587_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__8, &l_Lake_PackageConfig___fields___closed__8_once, _init_l_Lake_PackageConfig___fields___closed__8);
v___x_4588_ = lean_array_push(v___x_4587_, v___x_4586_);
return v___x_4588_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4596_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__15));
v___x_4597_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__12, &l_Lake_PackageConfig___fields___closed__12_once, _init_l_Lake_PackageConfig___fields___closed__12);
v___x_4598_ = lean_array_push(v___x_4597_, v___x_4596_);
return v___x_4598_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4606_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__19));
v___x_4607_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__16, &l_Lake_PackageConfig___fields___closed__16_once, _init_l_Lake_PackageConfig___fields___closed__16);
v___x_4608_ = lean_array_push(v___x_4607_, v___x_4606_);
return v___x_4608_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4616_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__23));
v___x_4617_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__20, &l_Lake_PackageConfig___fields___closed__20_once, _init_l_Lake_PackageConfig___fields___closed__20);
v___x_4618_ = lean_array_push(v___x_4617_, v___x_4616_);
return v___x_4618_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4626_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__27));
v___x_4627_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__24, &l_Lake_PackageConfig___fields___closed__24_once, _init_l_Lake_PackageConfig___fields___closed__24);
v___x_4628_ = lean_array_push(v___x_4627_, v___x_4626_);
return v___x_4628_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4636_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__31));
v___x_4637_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__28, &l_Lake_PackageConfig___fields___closed__28_once, _init_l_Lake_PackageConfig___fields___closed__28);
v___x_4638_ = lean_array_push(v___x_4637_, v___x_4636_);
return v___x_4638_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4646_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__35));
v___x_4647_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__32, &l_Lake_PackageConfig___fields___closed__32_once, _init_l_Lake_PackageConfig___fields___closed__32);
v___x_4648_ = lean_array_push(v___x_4647_, v___x_4646_);
return v___x_4648_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4656_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__39));
v___x_4657_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__36, &l_Lake_PackageConfig___fields___closed__36_once, _init_l_Lake_PackageConfig___fields___closed__36);
v___x_4658_ = lean_array_push(v___x_4657_, v___x_4656_);
return v___x_4658_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4666_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__43));
v___x_4667_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__40, &l_Lake_PackageConfig___fields___closed__40_once, _init_l_Lake_PackageConfig___fields___closed__40);
v___x_4668_ = lean_array_push(v___x_4667_, v___x_4666_);
return v___x_4668_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4676_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__47));
v___x_4677_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__44, &l_Lake_PackageConfig___fields___closed__44_once, _init_l_Lake_PackageConfig___fields___closed__44);
v___x_4678_ = lean_array_push(v___x_4677_, v___x_4676_);
return v___x_4678_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__52(void){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4686_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__51));
v___x_4687_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__48, &l_Lake_PackageConfig___fields___closed__48_once, _init_l_Lake_PackageConfig___fields___closed__48);
v___x_4688_ = lean_array_push(v___x_4687_, v___x_4686_);
return v___x_4688_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__56(void){
_start:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4696_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__55));
v___x_4697_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__52, &l_Lake_PackageConfig___fields___closed__52_once, _init_l_Lake_PackageConfig___fields___closed__52);
v___x_4698_ = lean_array_push(v___x_4697_, v___x_4696_);
return v___x_4698_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__60(void){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4706_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__59));
v___x_4707_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__56, &l_Lake_PackageConfig___fields___closed__56_once, _init_l_Lake_PackageConfig___fields___closed__56);
v___x_4708_ = lean_array_push(v___x_4707_, v___x_4706_);
return v___x_4708_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__64(void){
_start:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4716_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__63));
v___x_4717_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__60, &l_Lake_PackageConfig___fields___closed__60_once, _init_l_Lake_PackageConfig___fields___closed__60);
v___x_4718_ = lean_array_push(v___x_4717_, v___x_4716_);
return v___x_4718_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__68(void){
_start:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4726_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__67));
v___x_4727_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__64, &l_Lake_PackageConfig___fields___closed__64_once, _init_l_Lake_PackageConfig___fields___closed__64);
v___x_4728_ = lean_array_push(v___x_4727_, v___x_4726_);
return v___x_4728_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__72(void){
_start:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4736_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__71));
v___x_4737_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__68, &l_Lake_PackageConfig___fields___closed__68_once, _init_l_Lake_PackageConfig___fields___closed__68);
v___x_4738_ = lean_array_push(v___x_4737_, v___x_4736_);
return v___x_4738_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__76(void){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4746_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__75));
v___x_4747_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__72, &l_Lake_PackageConfig___fields___closed__72_once, _init_l_Lake_PackageConfig___fields___closed__72);
v___x_4748_ = lean_array_push(v___x_4747_, v___x_4746_);
return v___x_4748_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__80(void){
_start:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4756_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__79));
v___x_4757_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__76, &l_Lake_PackageConfig___fields___closed__76_once, _init_l_Lake_PackageConfig___fields___closed__76);
v___x_4758_ = lean_array_push(v___x_4757_, v___x_4756_);
return v___x_4758_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__84(void){
_start:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4766_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__83));
v___x_4767_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__80, &l_Lake_PackageConfig___fields___closed__80_once, _init_l_Lake_PackageConfig___fields___closed__80);
v___x_4768_ = lean_array_push(v___x_4767_, v___x_4766_);
return v___x_4768_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__88(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4776_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__87));
v___x_4777_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__84, &l_Lake_PackageConfig___fields___closed__84_once, _init_l_Lake_PackageConfig___fields___closed__84);
v___x_4778_ = lean_array_push(v___x_4777_, v___x_4776_);
return v___x_4778_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__92(void){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4786_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__91));
v___x_4787_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__88, &l_Lake_PackageConfig___fields___closed__88_once, _init_l_Lake_PackageConfig___fields___closed__88);
v___x_4788_ = lean_array_push(v___x_4787_, v___x_4786_);
return v___x_4788_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__96(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4796_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__95));
v___x_4797_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__92, &l_Lake_PackageConfig___fields___closed__92_once, _init_l_Lake_PackageConfig___fields___closed__92);
v___x_4798_ = lean_array_push(v___x_4797_, v___x_4796_);
return v___x_4798_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__100(void){
_start:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4806_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__99));
v___x_4807_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__96, &l_Lake_PackageConfig___fields___closed__96_once, _init_l_Lake_PackageConfig___fields___closed__96);
v___x_4808_ = lean_array_push(v___x_4807_, v___x_4806_);
return v___x_4808_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__104(void){
_start:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4816_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__103));
v___x_4817_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__100, &l_Lake_PackageConfig___fields___closed__100_once, _init_l_Lake_PackageConfig___fields___closed__100);
v___x_4818_ = lean_array_push(v___x_4817_, v___x_4816_);
return v___x_4818_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__108(void){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4826_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__107));
v___x_4827_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__104, &l_Lake_PackageConfig___fields___closed__104_once, _init_l_Lake_PackageConfig___fields___closed__104);
v___x_4828_ = lean_array_push(v___x_4827_, v___x_4826_);
return v___x_4828_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__112(void){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4836_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__111));
v___x_4837_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__108, &l_Lake_PackageConfig___fields___closed__108_once, _init_l_Lake_PackageConfig___fields___closed__108);
v___x_4838_ = lean_array_push(v___x_4837_, v___x_4836_);
return v___x_4838_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__116(void){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4846_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__115));
v___x_4847_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__112, &l_Lake_PackageConfig___fields___closed__112_once, _init_l_Lake_PackageConfig___fields___closed__112);
v___x_4848_ = lean_array_push(v___x_4847_, v___x_4846_);
return v___x_4848_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__120(void){
_start:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4856_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__119));
v___x_4857_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__116, &l_Lake_PackageConfig___fields___closed__116_once, _init_l_Lake_PackageConfig___fields___closed__116);
v___x_4858_ = lean_array_push(v___x_4857_, v___x_4856_);
return v___x_4858_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__124(void){
_start:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4866_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__123));
v___x_4867_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__120, &l_Lake_PackageConfig___fields___closed__120_once, _init_l_Lake_PackageConfig___fields___closed__120);
v___x_4868_ = lean_array_push(v___x_4867_, v___x_4866_);
return v___x_4868_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__128(void){
_start:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4876_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__127));
v___x_4877_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__124, &l_Lake_PackageConfig___fields___closed__124_once, _init_l_Lake_PackageConfig___fields___closed__124);
v___x_4878_ = lean_array_push(v___x_4877_, v___x_4876_);
return v___x_4878_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__132(void){
_start:
{
lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4886_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__131));
v___x_4887_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__128, &l_Lake_PackageConfig___fields___closed__128_once, _init_l_Lake_PackageConfig___fields___closed__128);
v___x_4888_ = lean_array_push(v___x_4887_, v___x_4886_);
return v___x_4888_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__136(void){
_start:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4896_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__135));
v___x_4897_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__132, &l_Lake_PackageConfig___fields___closed__132_once, _init_l_Lake_PackageConfig___fields___closed__132);
v___x_4898_ = lean_array_push(v___x_4897_, v___x_4896_);
return v___x_4898_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__140(void){
_start:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4906_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__139));
v___x_4907_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__136, &l_Lake_PackageConfig___fields___closed__136_once, _init_l_Lake_PackageConfig___fields___closed__136);
v___x_4908_ = lean_array_push(v___x_4907_, v___x_4906_);
return v___x_4908_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__144(void){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4916_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__143));
v___x_4917_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__140, &l_Lake_PackageConfig___fields___closed__140_once, _init_l_Lake_PackageConfig___fields___closed__140);
v___x_4918_ = lean_array_push(v___x_4917_, v___x_4916_);
return v___x_4918_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__148(void){
_start:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4926_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__147));
v___x_4927_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__144, &l_Lake_PackageConfig___fields___closed__144_once, _init_l_Lake_PackageConfig___fields___closed__144);
v___x_4928_ = lean_array_push(v___x_4927_, v___x_4926_);
return v___x_4928_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__152(void){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4936_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__151));
v___x_4937_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__148, &l_Lake_PackageConfig___fields___closed__148_once, _init_l_Lake_PackageConfig___fields___closed__148);
v___x_4938_ = lean_array_push(v___x_4937_, v___x_4936_);
return v___x_4938_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__156(void){
_start:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4946_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__155));
v___x_4947_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__152, &l_Lake_PackageConfig___fields___closed__152_once, _init_l_Lake_PackageConfig___fields___closed__152);
v___x_4948_ = lean_array_push(v___x_4947_, v___x_4946_);
return v___x_4948_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__160(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4956_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__159));
v___x_4957_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__156, &l_Lake_PackageConfig___fields___closed__156_once, _init_l_Lake_PackageConfig___fields___closed__156);
v___x_4958_ = lean_array_push(v___x_4957_, v___x_4956_);
return v___x_4958_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__161(void){
_start:
{
lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4959_ = l_Lake_WorkspaceConfig___fields;
v___x_4960_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__160, &l_Lake_PackageConfig___fields___closed__160_once, _init_l_Lake_PackageConfig___fields___closed__160);
v___x_4961_ = l_Array_append___redArg(v___x_4960_, v___x_4959_);
return v___x_4961_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__165(void){
_start:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4969_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__164));
v___x_4970_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__161, &l_Lake_PackageConfig___fields___closed__161_once, _init_l_Lake_PackageConfig___fields___closed__161);
v___x_4971_ = lean_array_push(v___x_4970_, v___x_4969_);
return v___x_4971_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__166(void){
_start:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4972_ = l_Lake_LeanConfig___fields;
v___x_4973_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__165, &l_Lake_PackageConfig___fields___closed__165_once, _init_l_Lake_PackageConfig___fields___closed__165);
v___x_4974_ = l_Array_append___redArg(v___x_4973_, v___x_4972_);
return v___x_4974_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__170(void){
_start:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4982_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__169));
v___x_4983_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__166, &l_Lake_PackageConfig___fields___closed__166_once, _init_l_Lake_PackageConfig___fields___closed__166);
v___x_4984_ = lean_array_push(v___x_4983_, v___x_4982_);
return v___x_4984_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields(void){
_start:
{
lean_object* v___x_4985_; 
v___x_4985_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__170, &l_Lake_PackageConfig___fields___closed__170_once, _init_l_Lake_PackageConfig___fields___closed__170);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___redArg(){
_start:
{
lean_object* v___x_4987_; 
v___x_4987_ = l_Lake_PackageConfig___fields;
return v___x_4987_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___redArg___boxed(lean_object* v___dummy_4988_){
_start:
{
lean_object* v_res_4989_; 
v_res_4989_ = l_Lake_PackageConfig_instConfigFields___redArg();
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields(lean_object* v_p_4990_, lean_object* v_n_4991_){
_start:
{
lean_object* v___x_4992_; 
v___x_4992_ = l_Lake_PackageConfig___fields;
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___boxed(lean_object* v_p_4993_, lean_object* v_n_4994_){
_start:
{
lean_object* v_res_4995_; 
v_res_4995_ = l_Lake_PackageConfig_instConfigFields(v_p_4993_, v_n_4994_);
lean_dec(v_n_4994_);
lean_dec(v_p_4993_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo___lam__0(lean_object* v_x1_4996_, lean_object* v_x2_4997_){
_start:
{
lean_object* v_name_4998_; lean_object* v___x_4999_; 
v_name_4998_ = lean_ctor_get(v_x2_4997_, 0);
lean_inc(v_name_4998_);
v___x_4999_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_4998_, v_x2_4997_, v_x1_4996_);
return v___x_4999_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___x_5000_ = l_Lake_PackageConfig___fields;
v___x_5001_ = lean_array_get_size(v___x_5000_);
return v___x_5001_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; uint8_t v___x_5023_; 
v___x_5021_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_5022_ = lean_unsigned_to_nat(0u);
v___x_5023_ = lean_nat_dec_lt(v___x_5022_, v___x_5021_);
return v___x_5023_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_5025_; uint8_t v___x_5026_; 
v___x_5025_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_5026_ = lean_nat_dec_le(v___x_5025_, v___x_5025_);
return v___x_5026_;
}
}
static size_t _init_l_Lake_PackageConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_5027_; size_t v___x_5028_; 
v___x_5027_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_5028_ = lean_usize_of_nat(v___x_5027_);
return v___x_5028_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_5029_; size_t v___x_5030_; size_t v___x_5031_; lean_object* v___x_5032_; lean_object* v___f_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5029_ = lean_box(1);
v___x_5030_ = lean_usize_once(&l_Lake_PackageConfig_instConfigInfo___closed__14, &l_Lake_PackageConfig_instConfigInfo___closed__14_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__14);
v___x_5031_ = ((size_t)0ULL);
v___x_5032_ = l_Lake_PackageConfig___fields;
v___f_5033_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__12));
v___x_5034_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__10));
v___x_5035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5034_, v___f_5033_, v___x_5032_, v___x_5031_, v___x_5030_, v___x_5029_);
return v___x_5035_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_5036_; lean_object* v___y_5038_; lean_object* v___x_5041_; uint8_t v___x_5042_; 
v___x_5036_ = l_Lake_PackageConfig___fields;
v___x_5041_ = lean_box(1);
v___x_5042_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__11, &l_Lake_PackageConfig_instConfigInfo___closed__11_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__11);
if (v___x_5042_ == 0)
{
v___y_5038_ = v___x_5041_;
goto v___jp_5037_;
}
else
{
uint8_t v___x_5043_; 
v___x_5043_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__13, &l_Lake_PackageConfig_instConfigInfo___closed__13_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__13);
if (v___x_5043_ == 0)
{
if (v___x_5042_ == 0)
{
v___y_5038_ = v___x_5041_;
goto v___jp_5037_;
}
else
{
lean_object* v___x_5044_; 
v___x_5044_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_5038_ = v___x_5044_;
goto v___jp_5037_;
}
}
else
{
lean_object* v___x_5045_; 
v___x_5045_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_5038_ = v___x_5045_;
goto v___jp_5037_;
}
}
v___jp_5037_:
{
lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5039_ = lean_unsigned_to_nat(2u);
lean_inc(v___y_5038_);
v___x_5040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5036_);
lean_ctor_set(v___x_5040_, 1, v___y_5038_);
lean_ctor_set(v___x_5040_, 2, v___x_5039_);
return v___x_5040_;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0(void){
_start:
{
uint8_t v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; uint8_t v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v___x_5046_ = 1;
v___x_5047_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__7));
v___x_5048_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__6));
v___x_5049_ = l_Lake_defaultVersionTags;
v___x_5050_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__4));
v___x_5051_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__2));
v___x_5052_ = lean_box(0);
v___x_5053_ = l_Lake_defaultIrDir;
v___x_5054_ = l_Lake_defaultBinDir;
v___x_5055_ = l_Lake_defaultNativeLibDir;
v___x_5056_ = l_Lake_defaultLeanLibDir;
v___x_5057_ = l_Lake_defaultBuildDir;
v___x_5058_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__1));
v___x_5059_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0));
v___x_5060_ = 0;
v___x_5061_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__1));
v___x_5062_ = l_Lake_defaultPackagesDir;
v___x_5063_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v___x_5063_, 0, v___x_5062_);
lean_ctor_set(v___x_5063_, 1, v___x_5061_);
lean_ctor_set(v___x_5063_, 2, v___x_5059_);
lean_ctor_set(v___x_5063_, 3, v___x_5059_);
lean_ctor_set(v___x_5063_, 4, v___x_5058_);
lean_ctor_set(v___x_5063_, 5, v___x_5057_);
lean_ctor_set(v___x_5063_, 6, v___x_5056_);
lean_ctor_set(v___x_5063_, 7, v___x_5055_);
lean_ctor_set(v___x_5063_, 8, v___x_5054_);
lean_ctor_set(v___x_5063_, 9, v___x_5053_);
lean_ctor_set(v___x_5063_, 10, v___x_5052_);
lean_ctor_set(v___x_5063_, 11, v___x_5052_);
lean_ctor_set(v___x_5063_, 12, v___x_5051_);
lean_ctor_set(v___x_5063_, 13, v___x_5059_);
lean_ctor_set(v___x_5063_, 14, v___x_5051_);
lean_ctor_set(v___x_5063_, 15, v___x_5059_);
lean_ctor_set(v___x_5063_, 16, v___x_5050_);
lean_ctor_set(v___x_5063_, 17, v___x_5049_);
lean_ctor_set(v___x_5063_, 18, v___x_5051_);
lean_ctor_set(v___x_5063_, 19, v___x_5059_);
lean_ctor_set(v___x_5063_, 20, v___x_5051_);
lean_ctor_set(v___x_5063_, 21, v___x_5051_);
lean_ctor_set(v___x_5063_, 22, v___x_5048_);
lean_ctor_set(v___x_5063_, 23, v___x_5047_);
lean_ctor_set(v___x_5063_, 24, v___x_5052_);
lean_ctor_set(v___x_5063_, 25, v___x_5052_);
lean_ctor_set(v___x_5063_, 26, v___x_5052_);
lean_ctor_set(v___x_5063_, 27, v___x_5059_);
lean_ctor_set_uint8(v___x_5063_, sizeof(void*)*28, v___x_5060_);
lean_ctor_set_uint8(v___x_5063_, sizeof(void*)*28 + 1, v___x_5060_);
lean_ctor_set_uint8(v___x_5063_, sizeof(void*)*28 + 2, v___x_5060_);
lean_ctor_set_uint8(v___x_5063_, sizeof(void*)*28 + 3, v___x_5046_);
lean_ctor_set_uint8(v___x_5063_, sizeof(void*)*28 + 4, v___x_5060_);
lean_ctor_set_uint8(v___x_5063_, sizeof(void*)*28 + 5, v___x_5060_);
lean_ctor_set_uint8(v___x_5063_, sizeof(void*)*28 + 6, v___x_5060_);
return v___x_5063_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_5065_; 
v___x_5065_ = lean_obj_once(&l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0, &l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0_once, _init_l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0);
return v___x_5065_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___redArg___boxed(lean_object* v___dummy_5066_){
_start:
{
lean_object* v_res_5067_; 
v_res_5067_ = l_Lake_PackageConfig_instEmptyCollection___redArg();
return v_res_5067_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_5068_; 
v___x_5068_ = l_Lake_PackageConfig_instEmptyCollection___redArg();
return v___x_5068_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection(lean_object* v_p_5069_, lean_object* v_n_5070_){
_start:
{
lean_object* v___x_5071_; 
v___x_5071_ = lean_obj_once(&l_Lake_PackageConfig_instEmptyCollection___closed__0, &l_Lake_PackageConfig_instEmptyCollection___closed__0_once, _init_l_Lake_PackageConfig_instEmptyCollection___closed__0);
return v___x_5071_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___boxed(lean_object* v_p_5072_, lean_object* v_n_5073_){
_start:
{
lean_object* v_res_5074_; 
v_res_5074_ = l_Lake_PackageConfig_instEmptyCollection(v_p_5072_, v_n_5073_);
lean_dec(v_n_5073_);
lean_dec(v_p_5072_);
return v_res_5074_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg(lean_object* v_n_5075_){
_start:
{
lean_inc(v_n_5075_);
return v_n_5075_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg___boxed(lean_object* v_n_5076_){
_start:
{
lean_object* v_res_5077_; 
v_res_5077_ = l_Lake_PackageConfig_origName___redArg(v_n_5076_);
lean_dec(v_n_5076_);
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName(lean_object* v_p_5078_, lean_object* v_n_5079_, lean_object* v_x_5080_){
_start:
{
lean_inc(v_n_5079_);
return v_n_5079_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___boxed(lean_object* v_p_5081_, lean_object* v_n_5082_, lean_object* v_x_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_Lake_PackageConfig_origName(v_p_5081_, v_n_5082_, v_x_5083_);
lean_dec_ref(v_x_5083_);
lean_dec(v_n_5082_);
lean_dec(v_p_5081_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name(lean_object* v_self_5092_){
_start:
{
lean_object* v_keyName_5093_; 
v_keyName_5093_ = lean_ctor_get(v_self_5092_, 1);
lean_inc(v_keyName_5093_);
return v_keyName_5093_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name___boxed(lean_object* v_self_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l_Lake_PackageDecl_name(v_self_5094_);
lean_dec_ref(v_self_5094_);
return v_res_5095_;
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
