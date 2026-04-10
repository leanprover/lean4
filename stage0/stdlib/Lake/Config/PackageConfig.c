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
static const lean_ctor_object l_Lake_instInhabitedPackageConfig_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*13 + 8, .m_other = 13, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 2, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__1_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__2_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__3 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__3_value;
static const lean_ctor_object l_Lake_instInhabitedPackageConfig_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__4 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__4_value;
static const lean_ctor_object l_Lake_instInhabitedPackageConfig_default___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__4_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__3_value)}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__5 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__5_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LICENSE"};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__6 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__6_value;
static const lean_array_object l_Lake_instInhabitedPackageConfig_default___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__6_value)}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__7 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__7_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "README.md"};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__8 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__8_value;
static lean_once_cell_t l_Lake_instInhabitedPackageConfig_default___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackageConfig_default___closed__9;
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
static lean_object* _init_l_Lake_instInhabitedPackageConfig_default___closed__9(void){
_start:
{
uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_32_ = 1;
v___x_33_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__8));
v___x_34_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__7));
v___x_35_ = l_Lake_defaultVersionTags;
v___x_36_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__5));
v___x_37_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__3));
v___x_38_ = lean_box(0);
v___x_39_ = l_Lake_defaultIrDir;
v___x_40_ = l_Lake_defaultBinDir;
v___x_41_ = l_Lake_defaultNativeLibDir;
v___x_42_ = l_Lake_defaultLeanLibDir;
v___x_43_ = l_Lake_defaultBuildDir;
v___x_44_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__2));
v___x_45_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__0));
v___x_46_ = 0;
v___x_47_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
v___x_48_ = l_Lake_defaultPackagesDir;
v___x_49_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set(v___x_49_, 1, v___x_47_);
lean_ctor_set(v___x_49_, 2, v___x_45_);
lean_ctor_set(v___x_49_, 3, v___x_45_);
lean_ctor_set(v___x_49_, 4, v___x_44_);
lean_ctor_set(v___x_49_, 5, v___x_43_);
lean_ctor_set(v___x_49_, 6, v___x_42_);
lean_ctor_set(v___x_49_, 7, v___x_41_);
lean_ctor_set(v___x_49_, 8, v___x_40_);
lean_ctor_set(v___x_49_, 9, v___x_39_);
lean_ctor_set(v___x_49_, 10, v___x_38_);
lean_ctor_set(v___x_49_, 11, v___x_38_);
lean_ctor_set(v___x_49_, 12, v___x_37_);
lean_ctor_set(v___x_49_, 13, v___x_45_);
lean_ctor_set(v___x_49_, 14, v___x_37_);
lean_ctor_set(v___x_49_, 15, v___x_45_);
lean_ctor_set(v___x_49_, 16, v___x_36_);
lean_ctor_set(v___x_49_, 17, v___x_35_);
lean_ctor_set(v___x_49_, 18, v___x_37_);
lean_ctor_set(v___x_49_, 19, v___x_45_);
lean_ctor_set(v___x_49_, 20, v___x_37_);
lean_ctor_set(v___x_49_, 21, v___x_37_);
lean_ctor_set(v___x_49_, 22, v___x_34_);
lean_ctor_set(v___x_49_, 23, v___x_33_);
lean_ctor_set(v___x_49_, 24, v___x_38_);
lean_ctor_set(v___x_49_, 25, v___x_38_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*26, v___x_46_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*26 + 1, v___x_46_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*26 + 2, v___x_46_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*26 + 3, v___x_32_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*26 + 4, v___x_46_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*26 + 5, v___x_46_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*26 + 6, v___x_46_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default(lean_object* v_p_50_, lean_object* v_n_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___closed__9, &l_Lake_instInhabitedPackageConfig_default___closed__9_once, _init_l_Lake_instInhabitedPackageConfig_default___closed__9);
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
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig(lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lake_instInhabitedPackageConfig_default(v_a_56_, v_a_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___boxed(lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lake_instInhabitedPackageConfig(v_a_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec(v_a_59_);
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__0(lean_object* v_cfg_62_){
_start:
{
uint8_t v_bootstrap_63_; 
v_bootstrap_63_ = lean_ctor_get_uint8(v_cfg_62_, sizeof(void*)*26);
return v_bootstrap_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__0___boxed(lean_object* v_cfg_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Lake_PackageConfig_bootstrap___proj___lam__0(v_cfg_64_);
lean_dec_ref(v_cfg_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1(uint8_t v_val_67_, lean_object* v_cfg_68_){
_start:
{
lean_object* v_toWorkspaceConfig_69_; lean_object* v_toLeanConfig_70_; lean_object* v_extraDepTargets_71_; uint8_t v_precompileModules_72_; lean_object* v_moreGlobalServerArgs_73_; lean_object* v_srcDir_74_; lean_object* v_buildDir_75_; lean_object* v_leanLibDir_76_; lean_object* v_nativeLibDir_77_; lean_object* v_binDir_78_; lean_object* v_irDir_79_; lean_object* v_releaseRepo_80_; lean_object* v_buildArchive_81_; uint8_t v_preferReleaseBuild_82_; lean_object* v_testDriver_83_; lean_object* v_testDriverArgs_84_; lean_object* v_lintDriver_85_; lean_object* v_lintDriverArgs_86_; lean_object* v_version_87_; lean_object* v_versionTags_88_; lean_object* v_description_89_; lean_object* v_keywords_90_; lean_object* v_homepage_91_; lean_object* v_license_92_; lean_object* v_licenseFiles_93_; lean_object* v_readmeFile_94_; uint8_t v_reservoir_95_; lean_object* v_enableArtifactCache_x3f_96_; lean_object* v_restoreAllArtifacts_x3f_97_; uint8_t v_libPrefixOnWindows_98_; uint8_t v_allowImportAll_99_; uint8_t v_fixedToolchain_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
v_toWorkspaceConfig_69_ = lean_ctor_get(v_cfg_68_, 0);
v_toLeanConfig_70_ = lean_ctor_get(v_cfg_68_, 1);
v_extraDepTargets_71_ = lean_ctor_get(v_cfg_68_, 2);
v_precompileModules_72_ = lean_ctor_get_uint8(v_cfg_68_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_73_ = lean_ctor_get(v_cfg_68_, 3);
v_srcDir_74_ = lean_ctor_get(v_cfg_68_, 4);
v_buildDir_75_ = lean_ctor_get(v_cfg_68_, 5);
v_leanLibDir_76_ = lean_ctor_get(v_cfg_68_, 6);
v_nativeLibDir_77_ = lean_ctor_get(v_cfg_68_, 7);
v_binDir_78_ = lean_ctor_get(v_cfg_68_, 8);
v_irDir_79_ = lean_ctor_get(v_cfg_68_, 9);
v_releaseRepo_80_ = lean_ctor_get(v_cfg_68_, 10);
v_buildArchive_81_ = lean_ctor_get(v_cfg_68_, 11);
v_preferReleaseBuild_82_ = lean_ctor_get_uint8(v_cfg_68_, sizeof(void*)*26 + 2);
v_testDriver_83_ = lean_ctor_get(v_cfg_68_, 12);
v_testDriverArgs_84_ = lean_ctor_get(v_cfg_68_, 13);
v_lintDriver_85_ = lean_ctor_get(v_cfg_68_, 14);
v_lintDriverArgs_86_ = lean_ctor_get(v_cfg_68_, 15);
v_version_87_ = lean_ctor_get(v_cfg_68_, 16);
v_versionTags_88_ = lean_ctor_get(v_cfg_68_, 17);
v_description_89_ = lean_ctor_get(v_cfg_68_, 18);
v_keywords_90_ = lean_ctor_get(v_cfg_68_, 19);
v_homepage_91_ = lean_ctor_get(v_cfg_68_, 20);
v_license_92_ = lean_ctor_get(v_cfg_68_, 21);
v_licenseFiles_93_ = lean_ctor_get(v_cfg_68_, 22);
v_readmeFile_94_ = lean_ctor_get(v_cfg_68_, 23);
v_reservoir_95_ = lean_ctor_get_uint8(v_cfg_68_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_96_ = lean_ctor_get(v_cfg_68_, 24);
v_restoreAllArtifacts_x3f_97_ = lean_ctor_get(v_cfg_68_, 25);
v_libPrefixOnWindows_98_ = lean_ctor_get_uint8(v_cfg_68_, sizeof(void*)*26 + 4);
v_allowImportAll_99_ = lean_ctor_get_uint8(v_cfg_68_, sizeof(void*)*26 + 5);
v_fixedToolchain_100_ = lean_ctor_get_uint8(v_cfg_68_, sizeof(void*)*26 + 6);
v_isSharedCheck_107_ = !lean_is_exclusive(v_cfg_68_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v_cfg_68_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_97_);
lean_inc(v_enableArtifactCache_x3f_96_);
lean_inc(v_readmeFile_94_);
lean_inc(v_licenseFiles_93_);
lean_inc(v_license_92_);
lean_inc(v_homepage_91_);
lean_inc(v_keywords_90_);
lean_inc(v_description_89_);
lean_inc(v_versionTags_88_);
lean_inc(v_version_87_);
lean_inc(v_lintDriverArgs_86_);
lean_inc(v_lintDriver_85_);
lean_inc(v_testDriverArgs_84_);
lean_inc(v_testDriver_83_);
lean_inc(v_buildArchive_81_);
lean_inc(v_releaseRepo_80_);
lean_inc(v_irDir_79_);
lean_inc(v_binDir_78_);
lean_inc(v_nativeLibDir_77_);
lean_inc(v_leanLibDir_76_);
lean_inc(v_buildDir_75_);
lean_inc(v_srcDir_74_);
lean_inc(v_moreGlobalServerArgs_73_);
lean_inc(v_extraDepTargets_71_);
lean_inc(v_toLeanConfig_70_);
lean_inc(v_toWorkspaceConfig_69_);
lean_dec(v_cfg_68_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_toWorkspaceConfig_69_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_toLeanConfig_70_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_extraDepTargets_71_);
lean_ctor_set(v_reuseFailAlloc_106_, 3, v_moreGlobalServerArgs_73_);
lean_ctor_set(v_reuseFailAlloc_106_, 4, v_srcDir_74_);
lean_ctor_set(v_reuseFailAlloc_106_, 5, v_buildDir_75_);
lean_ctor_set(v_reuseFailAlloc_106_, 6, v_leanLibDir_76_);
lean_ctor_set(v_reuseFailAlloc_106_, 7, v_nativeLibDir_77_);
lean_ctor_set(v_reuseFailAlloc_106_, 8, v_binDir_78_);
lean_ctor_set(v_reuseFailAlloc_106_, 9, v_irDir_79_);
lean_ctor_set(v_reuseFailAlloc_106_, 10, v_releaseRepo_80_);
lean_ctor_set(v_reuseFailAlloc_106_, 11, v_buildArchive_81_);
lean_ctor_set(v_reuseFailAlloc_106_, 12, v_testDriver_83_);
lean_ctor_set(v_reuseFailAlloc_106_, 13, v_testDriverArgs_84_);
lean_ctor_set(v_reuseFailAlloc_106_, 14, v_lintDriver_85_);
lean_ctor_set(v_reuseFailAlloc_106_, 15, v_lintDriverArgs_86_);
lean_ctor_set(v_reuseFailAlloc_106_, 16, v_version_87_);
lean_ctor_set(v_reuseFailAlloc_106_, 17, v_versionTags_88_);
lean_ctor_set(v_reuseFailAlloc_106_, 18, v_description_89_);
lean_ctor_set(v_reuseFailAlloc_106_, 19, v_keywords_90_);
lean_ctor_set(v_reuseFailAlloc_106_, 20, v_homepage_91_);
lean_ctor_set(v_reuseFailAlloc_106_, 21, v_license_92_);
lean_ctor_set(v_reuseFailAlloc_106_, 22, v_licenseFiles_93_);
lean_ctor_set(v_reuseFailAlloc_106_, 23, v_readmeFile_94_);
lean_ctor_set(v_reuseFailAlloc_106_, 24, v_enableArtifactCache_x3f_96_);
lean_ctor_set(v_reuseFailAlloc_106_, 25, v_restoreAllArtifacts_x3f_97_);
lean_ctor_set_uint8(v_reuseFailAlloc_106_, sizeof(void*)*26 + 1, v_precompileModules_72_);
lean_ctor_set_uint8(v_reuseFailAlloc_106_, sizeof(void*)*26 + 2, v_preferReleaseBuild_82_);
lean_ctor_set_uint8(v_reuseFailAlloc_106_, sizeof(void*)*26 + 3, v_reservoir_95_);
lean_ctor_set_uint8(v_reuseFailAlloc_106_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_98_);
lean_ctor_set_uint8(v_reuseFailAlloc_106_, sizeof(void*)*26 + 5, v_allowImportAll_99_);
lean_ctor_set_uint8(v_reuseFailAlloc_106_, sizeof(void*)*26 + 6, v_fixedToolchain_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*26, v_val_67_);
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1___boxed(lean_object* v_val_108_, lean_object* v_cfg_109_){
_start:
{
uint8_t v_val_134__boxed_110_; lean_object* v_res_111_; 
v_val_134__boxed_110_ = lean_unbox(v_val_108_);
v_res_111_ = l_Lake_PackageConfig_bootstrap___proj___lam__1(v_val_134__boxed_110_, v_cfg_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__2(lean_object* v_f_112_, lean_object* v_cfg_113_){
_start:
{
lean_object* v_toWorkspaceConfig_114_; lean_object* v_toLeanConfig_115_; uint8_t v_bootstrap_116_; lean_object* v_extraDepTargets_117_; uint8_t v_precompileModules_118_; lean_object* v_moreGlobalServerArgs_119_; lean_object* v_srcDir_120_; lean_object* v_buildDir_121_; lean_object* v_leanLibDir_122_; lean_object* v_nativeLibDir_123_; lean_object* v_binDir_124_; lean_object* v_irDir_125_; lean_object* v_releaseRepo_126_; lean_object* v_buildArchive_127_; uint8_t v_preferReleaseBuild_128_; lean_object* v_testDriver_129_; lean_object* v_testDriverArgs_130_; lean_object* v_lintDriver_131_; lean_object* v_lintDriverArgs_132_; lean_object* v_version_133_; lean_object* v_versionTags_134_; lean_object* v_description_135_; lean_object* v_keywords_136_; lean_object* v_homepage_137_; lean_object* v_license_138_; lean_object* v_licenseFiles_139_; lean_object* v_readmeFile_140_; uint8_t v_reservoir_141_; lean_object* v_enableArtifactCache_x3f_142_; lean_object* v_restoreAllArtifacts_x3f_143_; uint8_t v_libPrefixOnWindows_144_; uint8_t v_allowImportAll_145_; uint8_t v_fixedToolchain_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_156_; 
v_toWorkspaceConfig_114_ = lean_ctor_get(v_cfg_113_, 0);
v_toLeanConfig_115_ = lean_ctor_get(v_cfg_113_, 1);
v_bootstrap_116_ = lean_ctor_get_uint8(v_cfg_113_, sizeof(void*)*26);
v_extraDepTargets_117_ = lean_ctor_get(v_cfg_113_, 2);
v_precompileModules_118_ = lean_ctor_get_uint8(v_cfg_113_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_119_ = lean_ctor_get(v_cfg_113_, 3);
v_srcDir_120_ = lean_ctor_get(v_cfg_113_, 4);
v_buildDir_121_ = lean_ctor_get(v_cfg_113_, 5);
v_leanLibDir_122_ = lean_ctor_get(v_cfg_113_, 6);
v_nativeLibDir_123_ = lean_ctor_get(v_cfg_113_, 7);
v_binDir_124_ = lean_ctor_get(v_cfg_113_, 8);
v_irDir_125_ = lean_ctor_get(v_cfg_113_, 9);
v_releaseRepo_126_ = lean_ctor_get(v_cfg_113_, 10);
v_buildArchive_127_ = lean_ctor_get(v_cfg_113_, 11);
v_preferReleaseBuild_128_ = lean_ctor_get_uint8(v_cfg_113_, sizeof(void*)*26 + 2);
v_testDriver_129_ = lean_ctor_get(v_cfg_113_, 12);
v_testDriverArgs_130_ = lean_ctor_get(v_cfg_113_, 13);
v_lintDriver_131_ = lean_ctor_get(v_cfg_113_, 14);
v_lintDriverArgs_132_ = lean_ctor_get(v_cfg_113_, 15);
v_version_133_ = lean_ctor_get(v_cfg_113_, 16);
v_versionTags_134_ = lean_ctor_get(v_cfg_113_, 17);
v_description_135_ = lean_ctor_get(v_cfg_113_, 18);
v_keywords_136_ = lean_ctor_get(v_cfg_113_, 19);
v_homepage_137_ = lean_ctor_get(v_cfg_113_, 20);
v_license_138_ = lean_ctor_get(v_cfg_113_, 21);
v_licenseFiles_139_ = lean_ctor_get(v_cfg_113_, 22);
v_readmeFile_140_ = lean_ctor_get(v_cfg_113_, 23);
v_reservoir_141_ = lean_ctor_get_uint8(v_cfg_113_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_142_ = lean_ctor_get(v_cfg_113_, 24);
v_restoreAllArtifacts_x3f_143_ = lean_ctor_get(v_cfg_113_, 25);
v_libPrefixOnWindows_144_ = lean_ctor_get_uint8(v_cfg_113_, sizeof(void*)*26 + 4);
v_allowImportAll_145_ = lean_ctor_get_uint8(v_cfg_113_, sizeof(void*)*26 + 5);
v_fixedToolchain_146_ = lean_ctor_get_uint8(v_cfg_113_, sizeof(void*)*26 + 6);
v_isSharedCheck_156_ = !lean_is_exclusive(v_cfg_113_);
if (v_isSharedCheck_156_ == 0)
{
v___x_148_ = v_cfg_113_;
v_isShared_149_ = v_isSharedCheck_156_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_143_);
lean_inc(v_enableArtifactCache_x3f_142_);
lean_inc(v_readmeFile_140_);
lean_inc(v_licenseFiles_139_);
lean_inc(v_license_138_);
lean_inc(v_homepage_137_);
lean_inc(v_keywords_136_);
lean_inc(v_description_135_);
lean_inc(v_versionTags_134_);
lean_inc(v_version_133_);
lean_inc(v_lintDriverArgs_132_);
lean_inc(v_lintDriver_131_);
lean_inc(v_testDriverArgs_130_);
lean_inc(v_testDriver_129_);
lean_inc(v_buildArchive_127_);
lean_inc(v_releaseRepo_126_);
lean_inc(v_irDir_125_);
lean_inc(v_binDir_124_);
lean_inc(v_nativeLibDir_123_);
lean_inc(v_leanLibDir_122_);
lean_inc(v_buildDir_121_);
lean_inc(v_srcDir_120_);
lean_inc(v_moreGlobalServerArgs_119_);
lean_inc(v_extraDepTargets_117_);
lean_inc(v_toLeanConfig_115_);
lean_inc(v_toWorkspaceConfig_114_);
lean_dec(v_cfg_113_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_156_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_150_ = lean_box(v_bootstrap_116_);
v___x_151_ = lean_apply_1(v_f_112_, v___x_150_);
if (v_isShared_149_ == 0)
{
v___x_153_ = v___x_148_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_toWorkspaceConfig_114_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_toLeanConfig_115_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_extraDepTargets_117_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v_moreGlobalServerArgs_119_);
lean_ctor_set(v_reuseFailAlloc_155_, 4, v_srcDir_120_);
lean_ctor_set(v_reuseFailAlloc_155_, 5, v_buildDir_121_);
lean_ctor_set(v_reuseFailAlloc_155_, 6, v_leanLibDir_122_);
lean_ctor_set(v_reuseFailAlloc_155_, 7, v_nativeLibDir_123_);
lean_ctor_set(v_reuseFailAlloc_155_, 8, v_binDir_124_);
lean_ctor_set(v_reuseFailAlloc_155_, 9, v_irDir_125_);
lean_ctor_set(v_reuseFailAlloc_155_, 10, v_releaseRepo_126_);
lean_ctor_set(v_reuseFailAlloc_155_, 11, v_buildArchive_127_);
lean_ctor_set(v_reuseFailAlloc_155_, 12, v_testDriver_129_);
lean_ctor_set(v_reuseFailAlloc_155_, 13, v_testDriverArgs_130_);
lean_ctor_set(v_reuseFailAlloc_155_, 14, v_lintDriver_131_);
lean_ctor_set(v_reuseFailAlloc_155_, 15, v_lintDriverArgs_132_);
lean_ctor_set(v_reuseFailAlloc_155_, 16, v_version_133_);
lean_ctor_set(v_reuseFailAlloc_155_, 17, v_versionTags_134_);
lean_ctor_set(v_reuseFailAlloc_155_, 18, v_description_135_);
lean_ctor_set(v_reuseFailAlloc_155_, 19, v_keywords_136_);
lean_ctor_set(v_reuseFailAlloc_155_, 20, v_homepage_137_);
lean_ctor_set(v_reuseFailAlloc_155_, 21, v_license_138_);
lean_ctor_set(v_reuseFailAlloc_155_, 22, v_licenseFiles_139_);
lean_ctor_set(v_reuseFailAlloc_155_, 23, v_readmeFile_140_);
lean_ctor_set(v_reuseFailAlloc_155_, 24, v_enableArtifactCache_x3f_142_);
lean_ctor_set(v_reuseFailAlloc_155_, 25, v_restoreAllArtifacts_x3f_143_);
v___x_153_ = v_reuseFailAlloc_155_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
uint8_t v___x_154_; 
v___x_154_ = lean_unbox(v___x_151_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*26, v___x_154_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*26 + 1, v_precompileModules_118_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*26 + 2, v_preferReleaseBuild_128_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*26 + 3, v_reservoir_141_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_144_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*26 + 5, v_allowImportAll_145_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*26 + 6, v_fixedToolchain_146_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__3(lean_object* v_x_157_){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__3___boxed(lean_object* v_x_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Lake_PackageConfig_bootstrap___proj___lam__3(v_x_159_);
lean_dec_ref(v_x_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object* v_p_171_, lean_object* v_n_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = ((lean_object*)(l_Lake_PackageConfig_bootstrap___proj___closed__4));
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___boxed(lean_object* v_p_174_, lean_object* v_n_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lake_PackageConfig_bootstrap___proj(v_p_174_, v_n_175_);
lean_dec(v_n_175_);
lean_dec(v_p_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField(lean_object* v_p_177_, lean_object* v_n_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lake_PackageConfig_bootstrap___proj(v_p_177_, v_n_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___boxed(lean_object* v_p_180_, lean_object* v_n_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lake_PackageConfig_bootstrap_instConfigField(v_p_180_, v_n_181_);
lean_dec(v_n_181_);
lean_dec(v_p_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0(lean_object* v_cfg_183_){
_start:
{
lean_object* v_extraDepTargets_184_; 
v_extraDepTargets_184_ = lean_ctor_get(v_cfg_183_, 2);
lean_inc_ref(v_extraDepTargets_184_);
return v_extraDepTargets_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0___boxed(lean_object* v_cfg_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__0(v_cfg_185_);
lean_dec_ref(v_cfg_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__1(lean_object* v_val_187_, lean_object* v_cfg_188_){
_start:
{
lean_object* v_toWorkspaceConfig_189_; lean_object* v_toLeanConfig_190_; uint8_t v_bootstrap_191_; uint8_t v_precompileModules_192_; lean_object* v_moreGlobalServerArgs_193_; lean_object* v_srcDir_194_; lean_object* v_buildDir_195_; lean_object* v_leanLibDir_196_; lean_object* v_nativeLibDir_197_; lean_object* v_binDir_198_; lean_object* v_irDir_199_; lean_object* v_releaseRepo_200_; lean_object* v_buildArchive_201_; uint8_t v_preferReleaseBuild_202_; lean_object* v_testDriver_203_; lean_object* v_testDriverArgs_204_; lean_object* v_lintDriver_205_; lean_object* v_lintDriverArgs_206_; lean_object* v_version_207_; lean_object* v_versionTags_208_; lean_object* v_description_209_; lean_object* v_keywords_210_; lean_object* v_homepage_211_; lean_object* v_license_212_; lean_object* v_licenseFiles_213_; lean_object* v_readmeFile_214_; uint8_t v_reservoir_215_; lean_object* v_enableArtifactCache_x3f_216_; lean_object* v_restoreAllArtifacts_x3f_217_; uint8_t v_libPrefixOnWindows_218_; uint8_t v_allowImportAll_219_; uint8_t v_fixedToolchain_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
v_toWorkspaceConfig_189_ = lean_ctor_get(v_cfg_188_, 0);
v_toLeanConfig_190_ = lean_ctor_get(v_cfg_188_, 1);
v_bootstrap_191_ = lean_ctor_get_uint8(v_cfg_188_, sizeof(void*)*26);
v_precompileModules_192_ = lean_ctor_get_uint8(v_cfg_188_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_193_ = lean_ctor_get(v_cfg_188_, 3);
v_srcDir_194_ = lean_ctor_get(v_cfg_188_, 4);
v_buildDir_195_ = lean_ctor_get(v_cfg_188_, 5);
v_leanLibDir_196_ = lean_ctor_get(v_cfg_188_, 6);
v_nativeLibDir_197_ = lean_ctor_get(v_cfg_188_, 7);
v_binDir_198_ = lean_ctor_get(v_cfg_188_, 8);
v_irDir_199_ = lean_ctor_get(v_cfg_188_, 9);
v_releaseRepo_200_ = lean_ctor_get(v_cfg_188_, 10);
v_buildArchive_201_ = lean_ctor_get(v_cfg_188_, 11);
v_preferReleaseBuild_202_ = lean_ctor_get_uint8(v_cfg_188_, sizeof(void*)*26 + 2);
v_testDriver_203_ = lean_ctor_get(v_cfg_188_, 12);
v_testDriverArgs_204_ = lean_ctor_get(v_cfg_188_, 13);
v_lintDriver_205_ = lean_ctor_get(v_cfg_188_, 14);
v_lintDriverArgs_206_ = lean_ctor_get(v_cfg_188_, 15);
v_version_207_ = lean_ctor_get(v_cfg_188_, 16);
v_versionTags_208_ = lean_ctor_get(v_cfg_188_, 17);
v_description_209_ = lean_ctor_get(v_cfg_188_, 18);
v_keywords_210_ = lean_ctor_get(v_cfg_188_, 19);
v_homepage_211_ = lean_ctor_get(v_cfg_188_, 20);
v_license_212_ = lean_ctor_get(v_cfg_188_, 21);
v_licenseFiles_213_ = lean_ctor_get(v_cfg_188_, 22);
v_readmeFile_214_ = lean_ctor_get(v_cfg_188_, 23);
v_reservoir_215_ = lean_ctor_get_uint8(v_cfg_188_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_216_ = lean_ctor_get(v_cfg_188_, 24);
v_restoreAllArtifacts_x3f_217_ = lean_ctor_get(v_cfg_188_, 25);
v_libPrefixOnWindows_218_ = lean_ctor_get_uint8(v_cfg_188_, sizeof(void*)*26 + 4);
v_allowImportAll_219_ = lean_ctor_get_uint8(v_cfg_188_, sizeof(void*)*26 + 5);
v_fixedToolchain_220_ = lean_ctor_get_uint8(v_cfg_188_, sizeof(void*)*26 + 6);
v_isSharedCheck_227_ = !lean_is_exclusive(v_cfg_188_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; 
v_unused_228_ = lean_ctor_get(v_cfg_188_, 2);
lean_dec(v_unused_228_);
v___x_222_ = v_cfg_188_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_217_);
lean_inc(v_enableArtifactCache_x3f_216_);
lean_inc(v_readmeFile_214_);
lean_inc(v_licenseFiles_213_);
lean_inc(v_license_212_);
lean_inc(v_homepage_211_);
lean_inc(v_keywords_210_);
lean_inc(v_description_209_);
lean_inc(v_versionTags_208_);
lean_inc(v_version_207_);
lean_inc(v_lintDriverArgs_206_);
lean_inc(v_lintDriver_205_);
lean_inc(v_testDriverArgs_204_);
lean_inc(v_testDriver_203_);
lean_inc(v_buildArchive_201_);
lean_inc(v_releaseRepo_200_);
lean_inc(v_irDir_199_);
lean_inc(v_binDir_198_);
lean_inc(v_nativeLibDir_197_);
lean_inc(v_leanLibDir_196_);
lean_inc(v_buildDir_195_);
lean_inc(v_srcDir_194_);
lean_inc(v_moreGlobalServerArgs_193_);
lean_inc(v_toLeanConfig_190_);
lean_inc(v_toWorkspaceConfig_189_);
lean_dec(v_cfg_188_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 2, v_val_187_);
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_toWorkspaceConfig_189_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_toLeanConfig_190_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v_val_187_);
lean_ctor_set(v_reuseFailAlloc_226_, 3, v_moreGlobalServerArgs_193_);
lean_ctor_set(v_reuseFailAlloc_226_, 4, v_srcDir_194_);
lean_ctor_set(v_reuseFailAlloc_226_, 5, v_buildDir_195_);
lean_ctor_set(v_reuseFailAlloc_226_, 6, v_leanLibDir_196_);
lean_ctor_set(v_reuseFailAlloc_226_, 7, v_nativeLibDir_197_);
lean_ctor_set(v_reuseFailAlloc_226_, 8, v_binDir_198_);
lean_ctor_set(v_reuseFailAlloc_226_, 9, v_irDir_199_);
lean_ctor_set(v_reuseFailAlloc_226_, 10, v_releaseRepo_200_);
lean_ctor_set(v_reuseFailAlloc_226_, 11, v_buildArchive_201_);
lean_ctor_set(v_reuseFailAlloc_226_, 12, v_testDriver_203_);
lean_ctor_set(v_reuseFailAlloc_226_, 13, v_testDriverArgs_204_);
lean_ctor_set(v_reuseFailAlloc_226_, 14, v_lintDriver_205_);
lean_ctor_set(v_reuseFailAlloc_226_, 15, v_lintDriverArgs_206_);
lean_ctor_set(v_reuseFailAlloc_226_, 16, v_version_207_);
lean_ctor_set(v_reuseFailAlloc_226_, 17, v_versionTags_208_);
lean_ctor_set(v_reuseFailAlloc_226_, 18, v_description_209_);
lean_ctor_set(v_reuseFailAlloc_226_, 19, v_keywords_210_);
lean_ctor_set(v_reuseFailAlloc_226_, 20, v_homepage_211_);
lean_ctor_set(v_reuseFailAlloc_226_, 21, v_license_212_);
lean_ctor_set(v_reuseFailAlloc_226_, 22, v_licenseFiles_213_);
lean_ctor_set(v_reuseFailAlloc_226_, 23, v_readmeFile_214_);
lean_ctor_set(v_reuseFailAlloc_226_, 24, v_enableArtifactCache_x3f_216_);
lean_ctor_set(v_reuseFailAlloc_226_, 25, v_restoreAllArtifacts_x3f_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*26, v_bootstrap_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*26 + 1, v_precompileModules_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*26 + 2, v_preferReleaseBuild_202_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*26 + 3, v_reservoir_215_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_218_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*26 + 5, v_allowImportAll_219_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*26 + 6, v_fixedToolchain_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__2(lean_object* v_f_229_, lean_object* v_cfg_230_){
_start:
{
lean_object* v_toWorkspaceConfig_231_; lean_object* v_toLeanConfig_232_; uint8_t v_bootstrap_233_; lean_object* v_extraDepTargets_234_; uint8_t v_precompileModules_235_; lean_object* v_moreGlobalServerArgs_236_; lean_object* v_srcDir_237_; lean_object* v_buildDir_238_; lean_object* v_leanLibDir_239_; lean_object* v_nativeLibDir_240_; lean_object* v_binDir_241_; lean_object* v_irDir_242_; lean_object* v_releaseRepo_243_; lean_object* v_buildArchive_244_; uint8_t v_preferReleaseBuild_245_; lean_object* v_testDriver_246_; lean_object* v_testDriverArgs_247_; lean_object* v_lintDriver_248_; lean_object* v_lintDriverArgs_249_; lean_object* v_version_250_; lean_object* v_versionTags_251_; lean_object* v_description_252_; lean_object* v_keywords_253_; lean_object* v_homepage_254_; lean_object* v_license_255_; lean_object* v_licenseFiles_256_; lean_object* v_readmeFile_257_; uint8_t v_reservoir_258_; lean_object* v_enableArtifactCache_x3f_259_; lean_object* v_restoreAllArtifacts_x3f_260_; uint8_t v_libPrefixOnWindows_261_; uint8_t v_allowImportAll_262_; uint8_t v_fixedToolchain_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_271_; 
v_toWorkspaceConfig_231_ = lean_ctor_get(v_cfg_230_, 0);
v_toLeanConfig_232_ = lean_ctor_get(v_cfg_230_, 1);
v_bootstrap_233_ = lean_ctor_get_uint8(v_cfg_230_, sizeof(void*)*26);
v_extraDepTargets_234_ = lean_ctor_get(v_cfg_230_, 2);
v_precompileModules_235_ = lean_ctor_get_uint8(v_cfg_230_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_236_ = lean_ctor_get(v_cfg_230_, 3);
v_srcDir_237_ = lean_ctor_get(v_cfg_230_, 4);
v_buildDir_238_ = lean_ctor_get(v_cfg_230_, 5);
v_leanLibDir_239_ = lean_ctor_get(v_cfg_230_, 6);
v_nativeLibDir_240_ = lean_ctor_get(v_cfg_230_, 7);
v_binDir_241_ = lean_ctor_get(v_cfg_230_, 8);
v_irDir_242_ = lean_ctor_get(v_cfg_230_, 9);
v_releaseRepo_243_ = lean_ctor_get(v_cfg_230_, 10);
v_buildArchive_244_ = lean_ctor_get(v_cfg_230_, 11);
v_preferReleaseBuild_245_ = lean_ctor_get_uint8(v_cfg_230_, sizeof(void*)*26 + 2);
v_testDriver_246_ = lean_ctor_get(v_cfg_230_, 12);
v_testDriverArgs_247_ = lean_ctor_get(v_cfg_230_, 13);
v_lintDriver_248_ = lean_ctor_get(v_cfg_230_, 14);
v_lintDriverArgs_249_ = lean_ctor_get(v_cfg_230_, 15);
v_version_250_ = lean_ctor_get(v_cfg_230_, 16);
v_versionTags_251_ = lean_ctor_get(v_cfg_230_, 17);
v_description_252_ = lean_ctor_get(v_cfg_230_, 18);
v_keywords_253_ = lean_ctor_get(v_cfg_230_, 19);
v_homepage_254_ = lean_ctor_get(v_cfg_230_, 20);
v_license_255_ = lean_ctor_get(v_cfg_230_, 21);
v_licenseFiles_256_ = lean_ctor_get(v_cfg_230_, 22);
v_readmeFile_257_ = lean_ctor_get(v_cfg_230_, 23);
v_reservoir_258_ = lean_ctor_get_uint8(v_cfg_230_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_259_ = lean_ctor_get(v_cfg_230_, 24);
v_restoreAllArtifacts_x3f_260_ = lean_ctor_get(v_cfg_230_, 25);
v_libPrefixOnWindows_261_ = lean_ctor_get_uint8(v_cfg_230_, sizeof(void*)*26 + 4);
v_allowImportAll_262_ = lean_ctor_get_uint8(v_cfg_230_, sizeof(void*)*26 + 5);
v_fixedToolchain_263_ = lean_ctor_get_uint8(v_cfg_230_, sizeof(void*)*26 + 6);
v_isSharedCheck_271_ = !lean_is_exclusive(v_cfg_230_);
if (v_isSharedCheck_271_ == 0)
{
v___x_265_ = v_cfg_230_;
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_260_);
lean_inc(v_enableArtifactCache_x3f_259_);
lean_inc(v_readmeFile_257_);
lean_inc(v_licenseFiles_256_);
lean_inc(v_license_255_);
lean_inc(v_homepage_254_);
lean_inc(v_keywords_253_);
lean_inc(v_description_252_);
lean_inc(v_versionTags_251_);
lean_inc(v_version_250_);
lean_inc(v_lintDriverArgs_249_);
lean_inc(v_lintDriver_248_);
lean_inc(v_testDriverArgs_247_);
lean_inc(v_testDriver_246_);
lean_inc(v_buildArchive_244_);
lean_inc(v_releaseRepo_243_);
lean_inc(v_irDir_242_);
lean_inc(v_binDir_241_);
lean_inc(v_nativeLibDir_240_);
lean_inc(v_leanLibDir_239_);
lean_inc(v_buildDir_238_);
lean_inc(v_srcDir_237_);
lean_inc(v_moreGlobalServerArgs_236_);
lean_inc(v_extraDepTargets_234_);
lean_inc(v_toLeanConfig_232_);
lean_inc(v_toWorkspaceConfig_231_);
lean_dec(v_cfg_230_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_apply_1(v_f_229_, v_extraDepTargets_234_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 2, v___x_267_);
v___x_269_ = v___x_265_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_toWorkspaceConfig_231_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_toLeanConfig_232_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_270_, 3, v_moreGlobalServerArgs_236_);
lean_ctor_set(v_reuseFailAlloc_270_, 4, v_srcDir_237_);
lean_ctor_set(v_reuseFailAlloc_270_, 5, v_buildDir_238_);
lean_ctor_set(v_reuseFailAlloc_270_, 6, v_leanLibDir_239_);
lean_ctor_set(v_reuseFailAlloc_270_, 7, v_nativeLibDir_240_);
lean_ctor_set(v_reuseFailAlloc_270_, 8, v_binDir_241_);
lean_ctor_set(v_reuseFailAlloc_270_, 9, v_irDir_242_);
lean_ctor_set(v_reuseFailAlloc_270_, 10, v_releaseRepo_243_);
lean_ctor_set(v_reuseFailAlloc_270_, 11, v_buildArchive_244_);
lean_ctor_set(v_reuseFailAlloc_270_, 12, v_testDriver_246_);
lean_ctor_set(v_reuseFailAlloc_270_, 13, v_testDriverArgs_247_);
lean_ctor_set(v_reuseFailAlloc_270_, 14, v_lintDriver_248_);
lean_ctor_set(v_reuseFailAlloc_270_, 15, v_lintDriverArgs_249_);
lean_ctor_set(v_reuseFailAlloc_270_, 16, v_version_250_);
lean_ctor_set(v_reuseFailAlloc_270_, 17, v_versionTags_251_);
lean_ctor_set(v_reuseFailAlloc_270_, 18, v_description_252_);
lean_ctor_set(v_reuseFailAlloc_270_, 19, v_keywords_253_);
lean_ctor_set(v_reuseFailAlloc_270_, 20, v_homepage_254_);
lean_ctor_set(v_reuseFailAlloc_270_, 21, v_license_255_);
lean_ctor_set(v_reuseFailAlloc_270_, 22, v_licenseFiles_256_);
lean_ctor_set(v_reuseFailAlloc_270_, 23, v_readmeFile_257_);
lean_ctor_set(v_reuseFailAlloc_270_, 24, v_enableArtifactCache_x3f_259_);
lean_ctor_set(v_reuseFailAlloc_270_, 25, v_restoreAllArtifacts_x3f_260_);
lean_ctor_set_uint8(v_reuseFailAlloc_270_, sizeof(void*)*26, v_bootstrap_233_);
lean_ctor_set_uint8(v_reuseFailAlloc_270_, sizeof(void*)*26 + 1, v_precompileModules_235_);
lean_ctor_set_uint8(v_reuseFailAlloc_270_, sizeof(void*)*26 + 2, v_preferReleaseBuild_245_);
lean_ctor_set_uint8(v_reuseFailAlloc_270_, sizeof(void*)*26 + 3, v_reservoir_258_);
lean_ctor_set_uint8(v_reuseFailAlloc_270_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_261_);
lean_ctor_set_uint8(v_reuseFailAlloc_270_, sizeof(void*)*26 + 5, v_allowImportAll_262_);
lean_ctor_set_uint8(v_reuseFailAlloc_270_, sizeof(void*)*26 + 6, v_fixedToolchain_263_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3(lean_object* v_x_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0));
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3___boxed(lean_object* v_x_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__3(v_x_276_);
lean_dec_ref(v_x_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object* v_p_287_, lean_object* v_n_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___closed__4));
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object* v_p_290_, lean_object* v_n_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_290_, v_n_291_);
lean_dec(v_n_291_);
lean_dec(v_p_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object* v_p_293_, lean_object* v_n_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_293_, v_n_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object* v_p_296_, lean_object* v_n_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lake_PackageConfig_extraDepTargets_instConfigField(v_p_296_, v_n_297_);
lean_dec(v_n_297_);
lean_dec(v_p_296_);
return v_res_298_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___proj___lam__0(lean_object* v_cfg_299_){
_start:
{
uint8_t v_precompileModules_300_; 
v_precompileModules_300_ = lean_ctor_get_uint8(v_cfg_299_, sizeof(void*)*26 + 1);
return v_precompileModules_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__0___boxed(lean_object* v_cfg_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Lake_PackageConfig_precompileModules___proj___lam__0(v_cfg_301_);
lean_dec_ref(v_cfg_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1(uint8_t v_val_304_, lean_object* v_cfg_305_){
_start:
{
lean_object* v_toWorkspaceConfig_306_; lean_object* v_toLeanConfig_307_; uint8_t v_bootstrap_308_; lean_object* v_extraDepTargets_309_; lean_object* v_moreGlobalServerArgs_310_; lean_object* v_srcDir_311_; lean_object* v_buildDir_312_; lean_object* v_leanLibDir_313_; lean_object* v_nativeLibDir_314_; lean_object* v_binDir_315_; lean_object* v_irDir_316_; lean_object* v_releaseRepo_317_; lean_object* v_buildArchive_318_; uint8_t v_preferReleaseBuild_319_; lean_object* v_testDriver_320_; lean_object* v_testDriverArgs_321_; lean_object* v_lintDriver_322_; lean_object* v_lintDriverArgs_323_; lean_object* v_version_324_; lean_object* v_versionTags_325_; lean_object* v_description_326_; lean_object* v_keywords_327_; lean_object* v_homepage_328_; lean_object* v_license_329_; lean_object* v_licenseFiles_330_; lean_object* v_readmeFile_331_; uint8_t v_reservoir_332_; lean_object* v_enableArtifactCache_x3f_333_; lean_object* v_restoreAllArtifacts_x3f_334_; uint8_t v_libPrefixOnWindows_335_; uint8_t v_allowImportAll_336_; uint8_t v_fixedToolchain_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_toWorkspaceConfig_306_ = lean_ctor_get(v_cfg_305_, 0);
v_toLeanConfig_307_ = lean_ctor_get(v_cfg_305_, 1);
v_bootstrap_308_ = lean_ctor_get_uint8(v_cfg_305_, sizeof(void*)*26);
v_extraDepTargets_309_ = lean_ctor_get(v_cfg_305_, 2);
v_moreGlobalServerArgs_310_ = lean_ctor_get(v_cfg_305_, 3);
v_srcDir_311_ = lean_ctor_get(v_cfg_305_, 4);
v_buildDir_312_ = lean_ctor_get(v_cfg_305_, 5);
v_leanLibDir_313_ = lean_ctor_get(v_cfg_305_, 6);
v_nativeLibDir_314_ = lean_ctor_get(v_cfg_305_, 7);
v_binDir_315_ = lean_ctor_get(v_cfg_305_, 8);
v_irDir_316_ = lean_ctor_get(v_cfg_305_, 9);
v_releaseRepo_317_ = lean_ctor_get(v_cfg_305_, 10);
v_buildArchive_318_ = lean_ctor_get(v_cfg_305_, 11);
v_preferReleaseBuild_319_ = lean_ctor_get_uint8(v_cfg_305_, sizeof(void*)*26 + 2);
v_testDriver_320_ = lean_ctor_get(v_cfg_305_, 12);
v_testDriverArgs_321_ = lean_ctor_get(v_cfg_305_, 13);
v_lintDriver_322_ = lean_ctor_get(v_cfg_305_, 14);
v_lintDriverArgs_323_ = lean_ctor_get(v_cfg_305_, 15);
v_version_324_ = lean_ctor_get(v_cfg_305_, 16);
v_versionTags_325_ = lean_ctor_get(v_cfg_305_, 17);
v_description_326_ = lean_ctor_get(v_cfg_305_, 18);
v_keywords_327_ = lean_ctor_get(v_cfg_305_, 19);
v_homepage_328_ = lean_ctor_get(v_cfg_305_, 20);
v_license_329_ = lean_ctor_get(v_cfg_305_, 21);
v_licenseFiles_330_ = lean_ctor_get(v_cfg_305_, 22);
v_readmeFile_331_ = lean_ctor_get(v_cfg_305_, 23);
v_reservoir_332_ = lean_ctor_get_uint8(v_cfg_305_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_333_ = lean_ctor_get(v_cfg_305_, 24);
v_restoreAllArtifacts_x3f_334_ = lean_ctor_get(v_cfg_305_, 25);
v_libPrefixOnWindows_335_ = lean_ctor_get_uint8(v_cfg_305_, sizeof(void*)*26 + 4);
v_allowImportAll_336_ = lean_ctor_get_uint8(v_cfg_305_, sizeof(void*)*26 + 5);
v_fixedToolchain_337_ = lean_ctor_get_uint8(v_cfg_305_, sizeof(void*)*26 + 6);
v_isSharedCheck_344_ = !lean_is_exclusive(v_cfg_305_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v_cfg_305_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_334_);
lean_inc(v_enableArtifactCache_x3f_333_);
lean_inc(v_readmeFile_331_);
lean_inc(v_licenseFiles_330_);
lean_inc(v_license_329_);
lean_inc(v_homepage_328_);
lean_inc(v_keywords_327_);
lean_inc(v_description_326_);
lean_inc(v_versionTags_325_);
lean_inc(v_version_324_);
lean_inc(v_lintDriverArgs_323_);
lean_inc(v_lintDriver_322_);
lean_inc(v_testDriverArgs_321_);
lean_inc(v_testDriver_320_);
lean_inc(v_buildArchive_318_);
lean_inc(v_releaseRepo_317_);
lean_inc(v_irDir_316_);
lean_inc(v_binDir_315_);
lean_inc(v_nativeLibDir_314_);
lean_inc(v_leanLibDir_313_);
lean_inc(v_buildDir_312_);
lean_inc(v_srcDir_311_);
lean_inc(v_moreGlobalServerArgs_310_);
lean_inc(v_extraDepTargets_309_);
lean_inc(v_toLeanConfig_307_);
lean_inc(v_toWorkspaceConfig_306_);
lean_dec(v_cfg_305_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_toWorkspaceConfig_306_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_toLeanConfig_307_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_extraDepTargets_309_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_moreGlobalServerArgs_310_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v_srcDir_311_);
lean_ctor_set(v_reuseFailAlloc_343_, 5, v_buildDir_312_);
lean_ctor_set(v_reuseFailAlloc_343_, 6, v_leanLibDir_313_);
lean_ctor_set(v_reuseFailAlloc_343_, 7, v_nativeLibDir_314_);
lean_ctor_set(v_reuseFailAlloc_343_, 8, v_binDir_315_);
lean_ctor_set(v_reuseFailAlloc_343_, 9, v_irDir_316_);
lean_ctor_set(v_reuseFailAlloc_343_, 10, v_releaseRepo_317_);
lean_ctor_set(v_reuseFailAlloc_343_, 11, v_buildArchive_318_);
lean_ctor_set(v_reuseFailAlloc_343_, 12, v_testDriver_320_);
lean_ctor_set(v_reuseFailAlloc_343_, 13, v_testDriverArgs_321_);
lean_ctor_set(v_reuseFailAlloc_343_, 14, v_lintDriver_322_);
lean_ctor_set(v_reuseFailAlloc_343_, 15, v_lintDriverArgs_323_);
lean_ctor_set(v_reuseFailAlloc_343_, 16, v_version_324_);
lean_ctor_set(v_reuseFailAlloc_343_, 17, v_versionTags_325_);
lean_ctor_set(v_reuseFailAlloc_343_, 18, v_description_326_);
lean_ctor_set(v_reuseFailAlloc_343_, 19, v_keywords_327_);
lean_ctor_set(v_reuseFailAlloc_343_, 20, v_homepage_328_);
lean_ctor_set(v_reuseFailAlloc_343_, 21, v_license_329_);
lean_ctor_set(v_reuseFailAlloc_343_, 22, v_licenseFiles_330_);
lean_ctor_set(v_reuseFailAlloc_343_, 23, v_readmeFile_331_);
lean_ctor_set(v_reuseFailAlloc_343_, 24, v_enableArtifactCache_x3f_333_);
lean_ctor_set(v_reuseFailAlloc_343_, 25, v_restoreAllArtifacts_x3f_334_);
lean_ctor_set_uint8(v_reuseFailAlloc_343_, sizeof(void*)*26, v_bootstrap_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_343_, sizeof(void*)*26 + 2, v_preferReleaseBuild_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_343_, sizeof(void*)*26 + 3, v_reservoir_332_);
lean_ctor_set_uint8(v_reuseFailAlloc_343_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_335_);
lean_ctor_set_uint8(v_reuseFailAlloc_343_, sizeof(void*)*26 + 5, v_allowImportAll_336_);
lean_ctor_set_uint8(v_reuseFailAlloc_343_, sizeof(void*)*26 + 6, v_fixedToolchain_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*26 + 1, v_val_304_);
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1___boxed(lean_object* v_val_345_, lean_object* v_cfg_346_){
_start:
{
uint8_t v_val_134__boxed_347_; lean_object* v_res_348_; 
v_val_134__boxed_347_ = lean_unbox(v_val_345_);
v_res_348_ = l_Lake_PackageConfig_precompileModules___proj___lam__1(v_val_134__boxed_347_, v_cfg_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__2(lean_object* v_f_349_, lean_object* v_cfg_350_){
_start:
{
lean_object* v_toWorkspaceConfig_351_; lean_object* v_toLeanConfig_352_; uint8_t v_bootstrap_353_; lean_object* v_extraDepTargets_354_; uint8_t v_precompileModules_355_; lean_object* v_moreGlobalServerArgs_356_; lean_object* v_srcDir_357_; lean_object* v_buildDir_358_; lean_object* v_leanLibDir_359_; lean_object* v_nativeLibDir_360_; lean_object* v_binDir_361_; lean_object* v_irDir_362_; lean_object* v_releaseRepo_363_; lean_object* v_buildArchive_364_; uint8_t v_preferReleaseBuild_365_; lean_object* v_testDriver_366_; lean_object* v_testDriverArgs_367_; lean_object* v_lintDriver_368_; lean_object* v_lintDriverArgs_369_; lean_object* v_version_370_; lean_object* v_versionTags_371_; lean_object* v_description_372_; lean_object* v_keywords_373_; lean_object* v_homepage_374_; lean_object* v_license_375_; lean_object* v_licenseFiles_376_; lean_object* v_readmeFile_377_; uint8_t v_reservoir_378_; lean_object* v_enableArtifactCache_x3f_379_; lean_object* v_restoreAllArtifacts_x3f_380_; uint8_t v_libPrefixOnWindows_381_; uint8_t v_allowImportAll_382_; uint8_t v_fixedToolchain_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_393_; 
v_toWorkspaceConfig_351_ = lean_ctor_get(v_cfg_350_, 0);
v_toLeanConfig_352_ = lean_ctor_get(v_cfg_350_, 1);
v_bootstrap_353_ = lean_ctor_get_uint8(v_cfg_350_, sizeof(void*)*26);
v_extraDepTargets_354_ = lean_ctor_get(v_cfg_350_, 2);
v_precompileModules_355_ = lean_ctor_get_uint8(v_cfg_350_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_356_ = lean_ctor_get(v_cfg_350_, 3);
v_srcDir_357_ = lean_ctor_get(v_cfg_350_, 4);
v_buildDir_358_ = lean_ctor_get(v_cfg_350_, 5);
v_leanLibDir_359_ = lean_ctor_get(v_cfg_350_, 6);
v_nativeLibDir_360_ = lean_ctor_get(v_cfg_350_, 7);
v_binDir_361_ = lean_ctor_get(v_cfg_350_, 8);
v_irDir_362_ = lean_ctor_get(v_cfg_350_, 9);
v_releaseRepo_363_ = lean_ctor_get(v_cfg_350_, 10);
v_buildArchive_364_ = lean_ctor_get(v_cfg_350_, 11);
v_preferReleaseBuild_365_ = lean_ctor_get_uint8(v_cfg_350_, sizeof(void*)*26 + 2);
v_testDriver_366_ = lean_ctor_get(v_cfg_350_, 12);
v_testDriverArgs_367_ = lean_ctor_get(v_cfg_350_, 13);
v_lintDriver_368_ = lean_ctor_get(v_cfg_350_, 14);
v_lintDriverArgs_369_ = lean_ctor_get(v_cfg_350_, 15);
v_version_370_ = lean_ctor_get(v_cfg_350_, 16);
v_versionTags_371_ = lean_ctor_get(v_cfg_350_, 17);
v_description_372_ = lean_ctor_get(v_cfg_350_, 18);
v_keywords_373_ = lean_ctor_get(v_cfg_350_, 19);
v_homepage_374_ = lean_ctor_get(v_cfg_350_, 20);
v_license_375_ = lean_ctor_get(v_cfg_350_, 21);
v_licenseFiles_376_ = lean_ctor_get(v_cfg_350_, 22);
v_readmeFile_377_ = lean_ctor_get(v_cfg_350_, 23);
v_reservoir_378_ = lean_ctor_get_uint8(v_cfg_350_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_379_ = lean_ctor_get(v_cfg_350_, 24);
v_restoreAllArtifacts_x3f_380_ = lean_ctor_get(v_cfg_350_, 25);
v_libPrefixOnWindows_381_ = lean_ctor_get_uint8(v_cfg_350_, sizeof(void*)*26 + 4);
v_allowImportAll_382_ = lean_ctor_get_uint8(v_cfg_350_, sizeof(void*)*26 + 5);
v_fixedToolchain_383_ = lean_ctor_get_uint8(v_cfg_350_, sizeof(void*)*26 + 6);
v_isSharedCheck_393_ = !lean_is_exclusive(v_cfg_350_);
if (v_isSharedCheck_393_ == 0)
{
v___x_385_ = v_cfg_350_;
v_isShared_386_ = v_isSharedCheck_393_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_380_);
lean_inc(v_enableArtifactCache_x3f_379_);
lean_inc(v_readmeFile_377_);
lean_inc(v_licenseFiles_376_);
lean_inc(v_license_375_);
lean_inc(v_homepage_374_);
lean_inc(v_keywords_373_);
lean_inc(v_description_372_);
lean_inc(v_versionTags_371_);
lean_inc(v_version_370_);
lean_inc(v_lintDriverArgs_369_);
lean_inc(v_lintDriver_368_);
lean_inc(v_testDriverArgs_367_);
lean_inc(v_testDriver_366_);
lean_inc(v_buildArchive_364_);
lean_inc(v_releaseRepo_363_);
lean_inc(v_irDir_362_);
lean_inc(v_binDir_361_);
lean_inc(v_nativeLibDir_360_);
lean_inc(v_leanLibDir_359_);
lean_inc(v_buildDir_358_);
lean_inc(v_srcDir_357_);
lean_inc(v_moreGlobalServerArgs_356_);
lean_inc(v_extraDepTargets_354_);
lean_inc(v_toLeanConfig_352_);
lean_inc(v_toWorkspaceConfig_351_);
lean_dec(v_cfg_350_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_393_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = lean_box(v_precompileModules_355_);
v___x_388_ = lean_apply_1(v_f_349_, v___x_387_);
if (v_isShared_386_ == 0)
{
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_toWorkspaceConfig_351_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_toLeanConfig_352_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_extraDepTargets_354_);
lean_ctor_set(v_reuseFailAlloc_392_, 3, v_moreGlobalServerArgs_356_);
lean_ctor_set(v_reuseFailAlloc_392_, 4, v_srcDir_357_);
lean_ctor_set(v_reuseFailAlloc_392_, 5, v_buildDir_358_);
lean_ctor_set(v_reuseFailAlloc_392_, 6, v_leanLibDir_359_);
lean_ctor_set(v_reuseFailAlloc_392_, 7, v_nativeLibDir_360_);
lean_ctor_set(v_reuseFailAlloc_392_, 8, v_binDir_361_);
lean_ctor_set(v_reuseFailAlloc_392_, 9, v_irDir_362_);
lean_ctor_set(v_reuseFailAlloc_392_, 10, v_releaseRepo_363_);
lean_ctor_set(v_reuseFailAlloc_392_, 11, v_buildArchive_364_);
lean_ctor_set(v_reuseFailAlloc_392_, 12, v_testDriver_366_);
lean_ctor_set(v_reuseFailAlloc_392_, 13, v_testDriverArgs_367_);
lean_ctor_set(v_reuseFailAlloc_392_, 14, v_lintDriver_368_);
lean_ctor_set(v_reuseFailAlloc_392_, 15, v_lintDriverArgs_369_);
lean_ctor_set(v_reuseFailAlloc_392_, 16, v_version_370_);
lean_ctor_set(v_reuseFailAlloc_392_, 17, v_versionTags_371_);
lean_ctor_set(v_reuseFailAlloc_392_, 18, v_description_372_);
lean_ctor_set(v_reuseFailAlloc_392_, 19, v_keywords_373_);
lean_ctor_set(v_reuseFailAlloc_392_, 20, v_homepage_374_);
lean_ctor_set(v_reuseFailAlloc_392_, 21, v_license_375_);
lean_ctor_set(v_reuseFailAlloc_392_, 22, v_licenseFiles_376_);
lean_ctor_set(v_reuseFailAlloc_392_, 23, v_readmeFile_377_);
lean_ctor_set(v_reuseFailAlloc_392_, 24, v_enableArtifactCache_x3f_379_);
lean_ctor_set(v_reuseFailAlloc_392_, 25, v_restoreAllArtifacts_x3f_380_);
lean_ctor_set_uint8(v_reuseFailAlloc_392_, sizeof(void*)*26, v_bootstrap_353_);
v___x_390_ = v_reuseFailAlloc_392_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
uint8_t v___x_391_; 
v___x_391_ = lean_unbox(v___x_388_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*26 + 1, v___x_391_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*26 + 2, v_preferReleaseBuild_365_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*26 + 3, v_reservoir_378_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_381_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*26 + 5, v_allowImportAll_382_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*26 + 6, v_fixedToolchain_383_);
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object* v_p_402_, lean_object* v_n_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = ((lean_object*)(l_Lake_PackageConfig_precompileModules___proj___closed__3));
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object* v_p_405_, lean_object* v_n_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lake_PackageConfig_precompileModules___proj(v_p_405_, v_n_406_);
lean_dec(v_n_406_);
lean_dec(v_p_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object* v_p_408_, lean_object* v_n_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lake_PackageConfig_precompileModules___proj(v_p_408_, v_n_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object* v_p_411_, lean_object* v_n_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lake_PackageConfig_precompileModules_instConfigField(v_p_411_, v_n_412_);
lean_dec(v_n_412_);
lean_dec(v_p_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(lean_object* v_cfg_414_){
_start:
{
lean_object* v_moreGlobalServerArgs_415_; 
v_moreGlobalServerArgs_415_ = lean_ctor_get(v_cfg_414_, 3);
lean_inc_ref(v_moreGlobalServerArgs_415_);
return v_moreGlobalServerArgs_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0___boxed(lean_object* v_cfg_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(v_cfg_416_);
lean_dec_ref(v_cfg_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__1(lean_object* v_val_418_, lean_object* v_cfg_419_){
_start:
{
lean_object* v_toWorkspaceConfig_420_; lean_object* v_toLeanConfig_421_; uint8_t v_bootstrap_422_; lean_object* v_extraDepTargets_423_; uint8_t v_precompileModules_424_; lean_object* v_srcDir_425_; lean_object* v_buildDir_426_; lean_object* v_leanLibDir_427_; lean_object* v_nativeLibDir_428_; lean_object* v_binDir_429_; lean_object* v_irDir_430_; lean_object* v_releaseRepo_431_; lean_object* v_buildArchive_432_; uint8_t v_preferReleaseBuild_433_; lean_object* v_testDriver_434_; lean_object* v_testDriverArgs_435_; lean_object* v_lintDriver_436_; lean_object* v_lintDriverArgs_437_; lean_object* v_version_438_; lean_object* v_versionTags_439_; lean_object* v_description_440_; lean_object* v_keywords_441_; lean_object* v_homepage_442_; lean_object* v_license_443_; lean_object* v_licenseFiles_444_; lean_object* v_readmeFile_445_; uint8_t v_reservoir_446_; lean_object* v_enableArtifactCache_x3f_447_; lean_object* v_restoreAllArtifacts_x3f_448_; uint8_t v_libPrefixOnWindows_449_; uint8_t v_allowImportAll_450_; uint8_t v_fixedToolchain_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_toWorkspaceConfig_420_ = lean_ctor_get(v_cfg_419_, 0);
v_toLeanConfig_421_ = lean_ctor_get(v_cfg_419_, 1);
v_bootstrap_422_ = lean_ctor_get_uint8(v_cfg_419_, sizeof(void*)*26);
v_extraDepTargets_423_ = lean_ctor_get(v_cfg_419_, 2);
v_precompileModules_424_ = lean_ctor_get_uint8(v_cfg_419_, sizeof(void*)*26 + 1);
v_srcDir_425_ = lean_ctor_get(v_cfg_419_, 4);
v_buildDir_426_ = lean_ctor_get(v_cfg_419_, 5);
v_leanLibDir_427_ = lean_ctor_get(v_cfg_419_, 6);
v_nativeLibDir_428_ = lean_ctor_get(v_cfg_419_, 7);
v_binDir_429_ = lean_ctor_get(v_cfg_419_, 8);
v_irDir_430_ = lean_ctor_get(v_cfg_419_, 9);
v_releaseRepo_431_ = lean_ctor_get(v_cfg_419_, 10);
v_buildArchive_432_ = lean_ctor_get(v_cfg_419_, 11);
v_preferReleaseBuild_433_ = lean_ctor_get_uint8(v_cfg_419_, sizeof(void*)*26 + 2);
v_testDriver_434_ = lean_ctor_get(v_cfg_419_, 12);
v_testDriverArgs_435_ = lean_ctor_get(v_cfg_419_, 13);
v_lintDriver_436_ = lean_ctor_get(v_cfg_419_, 14);
v_lintDriverArgs_437_ = lean_ctor_get(v_cfg_419_, 15);
v_version_438_ = lean_ctor_get(v_cfg_419_, 16);
v_versionTags_439_ = lean_ctor_get(v_cfg_419_, 17);
v_description_440_ = lean_ctor_get(v_cfg_419_, 18);
v_keywords_441_ = lean_ctor_get(v_cfg_419_, 19);
v_homepage_442_ = lean_ctor_get(v_cfg_419_, 20);
v_license_443_ = lean_ctor_get(v_cfg_419_, 21);
v_licenseFiles_444_ = lean_ctor_get(v_cfg_419_, 22);
v_readmeFile_445_ = lean_ctor_get(v_cfg_419_, 23);
v_reservoir_446_ = lean_ctor_get_uint8(v_cfg_419_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_447_ = lean_ctor_get(v_cfg_419_, 24);
v_restoreAllArtifacts_x3f_448_ = lean_ctor_get(v_cfg_419_, 25);
v_libPrefixOnWindows_449_ = lean_ctor_get_uint8(v_cfg_419_, sizeof(void*)*26 + 4);
v_allowImportAll_450_ = lean_ctor_get_uint8(v_cfg_419_, sizeof(void*)*26 + 5);
v_fixedToolchain_451_ = lean_ctor_get_uint8(v_cfg_419_, sizeof(void*)*26 + 6);
v_isSharedCheck_458_ = !lean_is_exclusive(v_cfg_419_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v_cfg_419_, 3);
lean_dec(v_unused_459_);
v___x_453_ = v_cfg_419_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_448_);
lean_inc(v_enableArtifactCache_x3f_447_);
lean_inc(v_readmeFile_445_);
lean_inc(v_licenseFiles_444_);
lean_inc(v_license_443_);
lean_inc(v_homepage_442_);
lean_inc(v_keywords_441_);
lean_inc(v_description_440_);
lean_inc(v_versionTags_439_);
lean_inc(v_version_438_);
lean_inc(v_lintDriverArgs_437_);
lean_inc(v_lintDriver_436_);
lean_inc(v_testDriverArgs_435_);
lean_inc(v_testDriver_434_);
lean_inc(v_buildArchive_432_);
lean_inc(v_releaseRepo_431_);
lean_inc(v_irDir_430_);
lean_inc(v_binDir_429_);
lean_inc(v_nativeLibDir_428_);
lean_inc(v_leanLibDir_427_);
lean_inc(v_buildDir_426_);
lean_inc(v_srcDir_425_);
lean_inc(v_extraDepTargets_423_);
lean_inc(v_toLeanConfig_421_);
lean_inc(v_toWorkspaceConfig_420_);
lean_dec(v_cfg_419_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 3, v_val_418_);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_toWorkspaceConfig_420_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_toLeanConfig_421_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_extraDepTargets_423_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_val_418_);
lean_ctor_set(v_reuseFailAlloc_457_, 4, v_srcDir_425_);
lean_ctor_set(v_reuseFailAlloc_457_, 5, v_buildDir_426_);
lean_ctor_set(v_reuseFailAlloc_457_, 6, v_leanLibDir_427_);
lean_ctor_set(v_reuseFailAlloc_457_, 7, v_nativeLibDir_428_);
lean_ctor_set(v_reuseFailAlloc_457_, 8, v_binDir_429_);
lean_ctor_set(v_reuseFailAlloc_457_, 9, v_irDir_430_);
lean_ctor_set(v_reuseFailAlloc_457_, 10, v_releaseRepo_431_);
lean_ctor_set(v_reuseFailAlloc_457_, 11, v_buildArchive_432_);
lean_ctor_set(v_reuseFailAlloc_457_, 12, v_testDriver_434_);
lean_ctor_set(v_reuseFailAlloc_457_, 13, v_testDriverArgs_435_);
lean_ctor_set(v_reuseFailAlloc_457_, 14, v_lintDriver_436_);
lean_ctor_set(v_reuseFailAlloc_457_, 15, v_lintDriverArgs_437_);
lean_ctor_set(v_reuseFailAlloc_457_, 16, v_version_438_);
lean_ctor_set(v_reuseFailAlloc_457_, 17, v_versionTags_439_);
lean_ctor_set(v_reuseFailAlloc_457_, 18, v_description_440_);
lean_ctor_set(v_reuseFailAlloc_457_, 19, v_keywords_441_);
lean_ctor_set(v_reuseFailAlloc_457_, 20, v_homepage_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 21, v_license_443_);
lean_ctor_set(v_reuseFailAlloc_457_, 22, v_licenseFiles_444_);
lean_ctor_set(v_reuseFailAlloc_457_, 23, v_readmeFile_445_);
lean_ctor_set(v_reuseFailAlloc_457_, 24, v_enableArtifactCache_x3f_447_);
lean_ctor_set(v_reuseFailAlloc_457_, 25, v_restoreAllArtifacts_x3f_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*26, v_bootstrap_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*26 + 1, v_precompileModules_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*26 + 2, v_preferReleaseBuild_433_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*26 + 3, v_reservoir_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*26 + 5, v_allowImportAll_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*26 + 6, v_fixedToolchain_451_);
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
lean_object* v_toWorkspaceConfig_462_; lean_object* v_toLeanConfig_463_; uint8_t v_bootstrap_464_; lean_object* v_extraDepTargets_465_; uint8_t v_precompileModules_466_; lean_object* v_moreGlobalServerArgs_467_; lean_object* v_srcDir_468_; lean_object* v_buildDir_469_; lean_object* v_leanLibDir_470_; lean_object* v_nativeLibDir_471_; lean_object* v_binDir_472_; lean_object* v_irDir_473_; lean_object* v_releaseRepo_474_; lean_object* v_buildArchive_475_; uint8_t v_preferReleaseBuild_476_; lean_object* v_testDriver_477_; lean_object* v_testDriverArgs_478_; lean_object* v_lintDriver_479_; lean_object* v_lintDriverArgs_480_; lean_object* v_version_481_; lean_object* v_versionTags_482_; lean_object* v_description_483_; lean_object* v_keywords_484_; lean_object* v_homepage_485_; lean_object* v_license_486_; lean_object* v_licenseFiles_487_; lean_object* v_readmeFile_488_; uint8_t v_reservoir_489_; lean_object* v_enableArtifactCache_x3f_490_; lean_object* v_restoreAllArtifacts_x3f_491_; uint8_t v_libPrefixOnWindows_492_; uint8_t v_allowImportAll_493_; uint8_t v_fixedToolchain_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_502_; 
v_toWorkspaceConfig_462_ = lean_ctor_get(v_cfg_461_, 0);
v_toLeanConfig_463_ = lean_ctor_get(v_cfg_461_, 1);
v_bootstrap_464_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*26);
v_extraDepTargets_465_ = lean_ctor_get(v_cfg_461_, 2);
v_precompileModules_466_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_467_ = lean_ctor_get(v_cfg_461_, 3);
v_srcDir_468_ = lean_ctor_get(v_cfg_461_, 4);
v_buildDir_469_ = lean_ctor_get(v_cfg_461_, 5);
v_leanLibDir_470_ = lean_ctor_get(v_cfg_461_, 6);
v_nativeLibDir_471_ = lean_ctor_get(v_cfg_461_, 7);
v_binDir_472_ = lean_ctor_get(v_cfg_461_, 8);
v_irDir_473_ = lean_ctor_get(v_cfg_461_, 9);
v_releaseRepo_474_ = lean_ctor_get(v_cfg_461_, 10);
v_buildArchive_475_ = lean_ctor_get(v_cfg_461_, 11);
v_preferReleaseBuild_476_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*26 + 2);
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
v_reservoir_489_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_490_ = lean_ctor_get(v_cfg_461_, 24);
v_restoreAllArtifacts_x3f_491_ = lean_ctor_get(v_cfg_461_, 25);
v_libPrefixOnWindows_492_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*26 + 4);
v_allowImportAll_493_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*26 + 5);
v_fixedToolchain_494_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*26 + 6);
v_isSharedCheck_502_ = !lean_is_exclusive(v_cfg_461_);
if (v_isSharedCheck_502_ == 0)
{
v___x_496_ = v_cfg_461_;
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
else
{
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
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = lean_apply_1(v_f_460_, v_moreGlobalServerArgs_467_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 3, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_toWorkspaceConfig_462_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_toLeanConfig_463_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_extraDepTargets_465_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v_srcDir_468_);
lean_ctor_set(v_reuseFailAlloc_501_, 5, v_buildDir_469_);
lean_ctor_set(v_reuseFailAlloc_501_, 6, v_leanLibDir_470_);
lean_ctor_set(v_reuseFailAlloc_501_, 7, v_nativeLibDir_471_);
lean_ctor_set(v_reuseFailAlloc_501_, 8, v_binDir_472_);
lean_ctor_set(v_reuseFailAlloc_501_, 9, v_irDir_473_);
lean_ctor_set(v_reuseFailAlloc_501_, 10, v_releaseRepo_474_);
lean_ctor_set(v_reuseFailAlloc_501_, 11, v_buildArchive_475_);
lean_ctor_set(v_reuseFailAlloc_501_, 12, v_testDriver_477_);
lean_ctor_set(v_reuseFailAlloc_501_, 13, v_testDriverArgs_478_);
lean_ctor_set(v_reuseFailAlloc_501_, 14, v_lintDriver_479_);
lean_ctor_set(v_reuseFailAlloc_501_, 15, v_lintDriverArgs_480_);
lean_ctor_set(v_reuseFailAlloc_501_, 16, v_version_481_);
lean_ctor_set(v_reuseFailAlloc_501_, 17, v_versionTags_482_);
lean_ctor_set(v_reuseFailAlloc_501_, 18, v_description_483_);
lean_ctor_set(v_reuseFailAlloc_501_, 19, v_keywords_484_);
lean_ctor_set(v_reuseFailAlloc_501_, 20, v_homepage_485_);
lean_ctor_set(v_reuseFailAlloc_501_, 21, v_license_486_);
lean_ctor_set(v_reuseFailAlloc_501_, 22, v_licenseFiles_487_);
lean_ctor_set(v_reuseFailAlloc_501_, 23, v_readmeFile_488_);
lean_ctor_set(v_reuseFailAlloc_501_, 24, v_enableArtifactCache_x3f_490_);
lean_ctor_set(v_reuseFailAlloc_501_, 25, v_restoreAllArtifacts_x3f_491_);
lean_ctor_set_uint8(v_reuseFailAlloc_501_, sizeof(void*)*26, v_bootstrap_464_);
lean_ctor_set_uint8(v_reuseFailAlloc_501_, sizeof(void*)*26 + 1, v_precompileModules_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_501_, sizeof(void*)*26 + 2, v_preferReleaseBuild_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_501_, sizeof(void*)*26 + 3, v_reservoir_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_501_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_501_, sizeof(void*)*26 + 5, v_allowImportAll_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_501_, sizeof(void*)*26 + 6, v_fixedToolchain_494_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(lean_object* v_x_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0));
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___boxed(lean_object* v_x_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(v_x_507_);
lean_dec_ref(v_x_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object* v_p_518_, lean_object* v_n_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__4));
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object* v_p_521_, lean_object* v_n_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_521_, v_n_522_);
lean_dec(v_n_522_);
lean_dec(v_p_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object* v_p_524_, lean_object* v_n_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_524_, v_n_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object* v_p_527_, lean_object* v_n_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(v_p_527_, v_n_528_);
lean_dec(v_n_528_);
lean_dec(v_p_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object* v_p_530_, lean_object* v_n_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_530_, v_n_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object* v_p_533_, lean_object* v_n_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lake_PackageConfig_moreServerArgs_instConfigField(v_p_533_, v_n_534_);
lean_dec(v_n_534_);
lean_dec(v_p_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0(lean_object* v_cfg_536_){
_start:
{
lean_object* v_srcDir_537_; 
v_srcDir_537_ = lean_ctor_get(v_cfg_536_, 4);
lean_inc_ref(v_srcDir_537_);
return v_srcDir_537_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0___boxed(lean_object* v_cfg_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lake_PackageConfig_srcDir___proj___lam__0(v_cfg_538_);
lean_dec_ref(v_cfg_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__1(lean_object* v_val_540_, lean_object* v_cfg_541_){
_start:
{
lean_object* v_toWorkspaceConfig_542_; lean_object* v_toLeanConfig_543_; uint8_t v_bootstrap_544_; lean_object* v_extraDepTargets_545_; uint8_t v_precompileModules_546_; lean_object* v_moreGlobalServerArgs_547_; lean_object* v_buildDir_548_; lean_object* v_leanLibDir_549_; lean_object* v_nativeLibDir_550_; lean_object* v_binDir_551_; lean_object* v_irDir_552_; lean_object* v_releaseRepo_553_; lean_object* v_buildArchive_554_; uint8_t v_preferReleaseBuild_555_; lean_object* v_testDriver_556_; lean_object* v_testDriverArgs_557_; lean_object* v_lintDriver_558_; lean_object* v_lintDriverArgs_559_; lean_object* v_version_560_; lean_object* v_versionTags_561_; lean_object* v_description_562_; lean_object* v_keywords_563_; lean_object* v_homepage_564_; lean_object* v_license_565_; lean_object* v_licenseFiles_566_; lean_object* v_readmeFile_567_; uint8_t v_reservoir_568_; lean_object* v_enableArtifactCache_x3f_569_; lean_object* v_restoreAllArtifacts_x3f_570_; uint8_t v_libPrefixOnWindows_571_; uint8_t v_allowImportAll_572_; uint8_t v_fixedToolchain_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_toWorkspaceConfig_542_ = lean_ctor_get(v_cfg_541_, 0);
v_toLeanConfig_543_ = lean_ctor_get(v_cfg_541_, 1);
v_bootstrap_544_ = lean_ctor_get_uint8(v_cfg_541_, sizeof(void*)*26);
v_extraDepTargets_545_ = lean_ctor_get(v_cfg_541_, 2);
v_precompileModules_546_ = lean_ctor_get_uint8(v_cfg_541_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_547_ = lean_ctor_get(v_cfg_541_, 3);
v_buildDir_548_ = lean_ctor_get(v_cfg_541_, 5);
v_leanLibDir_549_ = lean_ctor_get(v_cfg_541_, 6);
v_nativeLibDir_550_ = lean_ctor_get(v_cfg_541_, 7);
v_binDir_551_ = lean_ctor_get(v_cfg_541_, 8);
v_irDir_552_ = lean_ctor_get(v_cfg_541_, 9);
v_releaseRepo_553_ = lean_ctor_get(v_cfg_541_, 10);
v_buildArchive_554_ = lean_ctor_get(v_cfg_541_, 11);
v_preferReleaseBuild_555_ = lean_ctor_get_uint8(v_cfg_541_, sizeof(void*)*26 + 2);
v_testDriver_556_ = lean_ctor_get(v_cfg_541_, 12);
v_testDriverArgs_557_ = lean_ctor_get(v_cfg_541_, 13);
v_lintDriver_558_ = lean_ctor_get(v_cfg_541_, 14);
v_lintDriverArgs_559_ = lean_ctor_get(v_cfg_541_, 15);
v_version_560_ = lean_ctor_get(v_cfg_541_, 16);
v_versionTags_561_ = lean_ctor_get(v_cfg_541_, 17);
v_description_562_ = lean_ctor_get(v_cfg_541_, 18);
v_keywords_563_ = lean_ctor_get(v_cfg_541_, 19);
v_homepage_564_ = lean_ctor_get(v_cfg_541_, 20);
v_license_565_ = lean_ctor_get(v_cfg_541_, 21);
v_licenseFiles_566_ = lean_ctor_get(v_cfg_541_, 22);
v_readmeFile_567_ = lean_ctor_get(v_cfg_541_, 23);
v_reservoir_568_ = lean_ctor_get_uint8(v_cfg_541_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_569_ = lean_ctor_get(v_cfg_541_, 24);
v_restoreAllArtifacts_x3f_570_ = lean_ctor_get(v_cfg_541_, 25);
v_libPrefixOnWindows_571_ = lean_ctor_get_uint8(v_cfg_541_, sizeof(void*)*26 + 4);
v_allowImportAll_572_ = lean_ctor_get_uint8(v_cfg_541_, sizeof(void*)*26 + 5);
v_fixedToolchain_573_ = lean_ctor_get_uint8(v_cfg_541_, sizeof(void*)*26 + 6);
v_isSharedCheck_580_ = !lean_is_exclusive(v_cfg_541_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v_cfg_541_, 4);
lean_dec(v_unused_581_);
v___x_575_ = v_cfg_541_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_570_);
lean_inc(v_enableArtifactCache_x3f_569_);
lean_inc(v_readmeFile_567_);
lean_inc(v_licenseFiles_566_);
lean_inc(v_license_565_);
lean_inc(v_homepage_564_);
lean_inc(v_keywords_563_);
lean_inc(v_description_562_);
lean_inc(v_versionTags_561_);
lean_inc(v_version_560_);
lean_inc(v_lintDriverArgs_559_);
lean_inc(v_lintDriver_558_);
lean_inc(v_testDriverArgs_557_);
lean_inc(v_testDriver_556_);
lean_inc(v_buildArchive_554_);
lean_inc(v_releaseRepo_553_);
lean_inc(v_irDir_552_);
lean_inc(v_binDir_551_);
lean_inc(v_nativeLibDir_550_);
lean_inc(v_leanLibDir_549_);
lean_inc(v_buildDir_548_);
lean_inc(v_moreGlobalServerArgs_547_);
lean_inc(v_extraDepTargets_545_);
lean_inc(v_toLeanConfig_543_);
lean_inc(v_toWorkspaceConfig_542_);
lean_dec(v_cfg_541_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 4, v_val_540_);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_toWorkspaceConfig_542_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_toLeanConfig_543_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_extraDepTargets_545_);
lean_ctor_set(v_reuseFailAlloc_579_, 3, v_moreGlobalServerArgs_547_);
lean_ctor_set(v_reuseFailAlloc_579_, 4, v_val_540_);
lean_ctor_set(v_reuseFailAlloc_579_, 5, v_buildDir_548_);
lean_ctor_set(v_reuseFailAlloc_579_, 6, v_leanLibDir_549_);
lean_ctor_set(v_reuseFailAlloc_579_, 7, v_nativeLibDir_550_);
lean_ctor_set(v_reuseFailAlloc_579_, 8, v_binDir_551_);
lean_ctor_set(v_reuseFailAlloc_579_, 9, v_irDir_552_);
lean_ctor_set(v_reuseFailAlloc_579_, 10, v_releaseRepo_553_);
lean_ctor_set(v_reuseFailAlloc_579_, 11, v_buildArchive_554_);
lean_ctor_set(v_reuseFailAlloc_579_, 12, v_testDriver_556_);
lean_ctor_set(v_reuseFailAlloc_579_, 13, v_testDriverArgs_557_);
lean_ctor_set(v_reuseFailAlloc_579_, 14, v_lintDriver_558_);
lean_ctor_set(v_reuseFailAlloc_579_, 15, v_lintDriverArgs_559_);
lean_ctor_set(v_reuseFailAlloc_579_, 16, v_version_560_);
lean_ctor_set(v_reuseFailAlloc_579_, 17, v_versionTags_561_);
lean_ctor_set(v_reuseFailAlloc_579_, 18, v_description_562_);
lean_ctor_set(v_reuseFailAlloc_579_, 19, v_keywords_563_);
lean_ctor_set(v_reuseFailAlloc_579_, 20, v_homepage_564_);
lean_ctor_set(v_reuseFailAlloc_579_, 21, v_license_565_);
lean_ctor_set(v_reuseFailAlloc_579_, 22, v_licenseFiles_566_);
lean_ctor_set(v_reuseFailAlloc_579_, 23, v_readmeFile_567_);
lean_ctor_set(v_reuseFailAlloc_579_, 24, v_enableArtifactCache_x3f_569_);
lean_ctor_set(v_reuseFailAlloc_579_, 25, v_restoreAllArtifacts_x3f_570_);
lean_ctor_set_uint8(v_reuseFailAlloc_579_, sizeof(void*)*26, v_bootstrap_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_579_, sizeof(void*)*26 + 1, v_precompileModules_546_);
lean_ctor_set_uint8(v_reuseFailAlloc_579_, sizeof(void*)*26 + 2, v_preferReleaseBuild_555_);
lean_ctor_set_uint8(v_reuseFailAlloc_579_, sizeof(void*)*26 + 3, v_reservoir_568_);
lean_ctor_set_uint8(v_reuseFailAlloc_579_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_571_);
lean_ctor_set_uint8(v_reuseFailAlloc_579_, sizeof(void*)*26 + 5, v_allowImportAll_572_);
lean_ctor_set_uint8(v_reuseFailAlloc_579_, sizeof(void*)*26 + 6, v_fixedToolchain_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__2(lean_object* v_f_582_, lean_object* v_cfg_583_){
_start:
{
lean_object* v_toWorkspaceConfig_584_; lean_object* v_toLeanConfig_585_; uint8_t v_bootstrap_586_; lean_object* v_extraDepTargets_587_; uint8_t v_precompileModules_588_; lean_object* v_moreGlobalServerArgs_589_; lean_object* v_srcDir_590_; lean_object* v_buildDir_591_; lean_object* v_leanLibDir_592_; lean_object* v_nativeLibDir_593_; lean_object* v_binDir_594_; lean_object* v_irDir_595_; lean_object* v_releaseRepo_596_; lean_object* v_buildArchive_597_; uint8_t v_preferReleaseBuild_598_; lean_object* v_testDriver_599_; lean_object* v_testDriverArgs_600_; lean_object* v_lintDriver_601_; lean_object* v_lintDriverArgs_602_; lean_object* v_version_603_; lean_object* v_versionTags_604_; lean_object* v_description_605_; lean_object* v_keywords_606_; lean_object* v_homepage_607_; lean_object* v_license_608_; lean_object* v_licenseFiles_609_; lean_object* v_readmeFile_610_; uint8_t v_reservoir_611_; lean_object* v_enableArtifactCache_x3f_612_; lean_object* v_restoreAllArtifacts_x3f_613_; uint8_t v_libPrefixOnWindows_614_; uint8_t v_allowImportAll_615_; uint8_t v_fixedToolchain_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_624_; 
v_toWorkspaceConfig_584_ = lean_ctor_get(v_cfg_583_, 0);
v_toLeanConfig_585_ = lean_ctor_get(v_cfg_583_, 1);
v_bootstrap_586_ = lean_ctor_get_uint8(v_cfg_583_, sizeof(void*)*26);
v_extraDepTargets_587_ = lean_ctor_get(v_cfg_583_, 2);
v_precompileModules_588_ = lean_ctor_get_uint8(v_cfg_583_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_589_ = lean_ctor_get(v_cfg_583_, 3);
v_srcDir_590_ = lean_ctor_get(v_cfg_583_, 4);
v_buildDir_591_ = lean_ctor_get(v_cfg_583_, 5);
v_leanLibDir_592_ = lean_ctor_get(v_cfg_583_, 6);
v_nativeLibDir_593_ = lean_ctor_get(v_cfg_583_, 7);
v_binDir_594_ = lean_ctor_get(v_cfg_583_, 8);
v_irDir_595_ = lean_ctor_get(v_cfg_583_, 9);
v_releaseRepo_596_ = lean_ctor_get(v_cfg_583_, 10);
v_buildArchive_597_ = lean_ctor_get(v_cfg_583_, 11);
v_preferReleaseBuild_598_ = lean_ctor_get_uint8(v_cfg_583_, sizeof(void*)*26 + 2);
v_testDriver_599_ = lean_ctor_get(v_cfg_583_, 12);
v_testDriverArgs_600_ = lean_ctor_get(v_cfg_583_, 13);
v_lintDriver_601_ = lean_ctor_get(v_cfg_583_, 14);
v_lintDriverArgs_602_ = lean_ctor_get(v_cfg_583_, 15);
v_version_603_ = lean_ctor_get(v_cfg_583_, 16);
v_versionTags_604_ = lean_ctor_get(v_cfg_583_, 17);
v_description_605_ = lean_ctor_get(v_cfg_583_, 18);
v_keywords_606_ = lean_ctor_get(v_cfg_583_, 19);
v_homepage_607_ = lean_ctor_get(v_cfg_583_, 20);
v_license_608_ = lean_ctor_get(v_cfg_583_, 21);
v_licenseFiles_609_ = lean_ctor_get(v_cfg_583_, 22);
v_readmeFile_610_ = lean_ctor_get(v_cfg_583_, 23);
v_reservoir_611_ = lean_ctor_get_uint8(v_cfg_583_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_612_ = lean_ctor_get(v_cfg_583_, 24);
v_restoreAllArtifacts_x3f_613_ = lean_ctor_get(v_cfg_583_, 25);
v_libPrefixOnWindows_614_ = lean_ctor_get_uint8(v_cfg_583_, sizeof(void*)*26 + 4);
v_allowImportAll_615_ = lean_ctor_get_uint8(v_cfg_583_, sizeof(void*)*26 + 5);
v_fixedToolchain_616_ = lean_ctor_get_uint8(v_cfg_583_, sizeof(void*)*26 + 6);
v_isSharedCheck_624_ = !lean_is_exclusive(v_cfg_583_);
if (v_isSharedCheck_624_ == 0)
{
v___x_618_ = v_cfg_583_;
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_613_);
lean_inc(v_enableArtifactCache_x3f_612_);
lean_inc(v_readmeFile_610_);
lean_inc(v_licenseFiles_609_);
lean_inc(v_license_608_);
lean_inc(v_homepage_607_);
lean_inc(v_keywords_606_);
lean_inc(v_description_605_);
lean_inc(v_versionTags_604_);
lean_inc(v_version_603_);
lean_inc(v_lintDriverArgs_602_);
lean_inc(v_lintDriver_601_);
lean_inc(v_testDriverArgs_600_);
lean_inc(v_testDriver_599_);
lean_inc(v_buildArchive_597_);
lean_inc(v_releaseRepo_596_);
lean_inc(v_irDir_595_);
lean_inc(v_binDir_594_);
lean_inc(v_nativeLibDir_593_);
lean_inc(v_leanLibDir_592_);
lean_inc(v_buildDir_591_);
lean_inc(v_srcDir_590_);
lean_inc(v_moreGlobalServerArgs_589_);
lean_inc(v_extraDepTargets_587_);
lean_inc(v_toLeanConfig_585_);
lean_inc(v_toWorkspaceConfig_584_);
lean_dec(v_cfg_583_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = lean_apply_1(v_f_582_, v_srcDir_590_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v___x_620_);
v___x_622_ = v___x_618_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_toWorkspaceConfig_584_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_toLeanConfig_585_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_extraDepTargets_587_);
lean_ctor_set(v_reuseFailAlloc_623_, 3, v_moreGlobalServerArgs_589_);
lean_ctor_set(v_reuseFailAlloc_623_, 4, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_623_, 5, v_buildDir_591_);
lean_ctor_set(v_reuseFailAlloc_623_, 6, v_leanLibDir_592_);
lean_ctor_set(v_reuseFailAlloc_623_, 7, v_nativeLibDir_593_);
lean_ctor_set(v_reuseFailAlloc_623_, 8, v_binDir_594_);
lean_ctor_set(v_reuseFailAlloc_623_, 9, v_irDir_595_);
lean_ctor_set(v_reuseFailAlloc_623_, 10, v_releaseRepo_596_);
lean_ctor_set(v_reuseFailAlloc_623_, 11, v_buildArchive_597_);
lean_ctor_set(v_reuseFailAlloc_623_, 12, v_testDriver_599_);
lean_ctor_set(v_reuseFailAlloc_623_, 13, v_testDriverArgs_600_);
lean_ctor_set(v_reuseFailAlloc_623_, 14, v_lintDriver_601_);
lean_ctor_set(v_reuseFailAlloc_623_, 15, v_lintDriverArgs_602_);
lean_ctor_set(v_reuseFailAlloc_623_, 16, v_version_603_);
lean_ctor_set(v_reuseFailAlloc_623_, 17, v_versionTags_604_);
lean_ctor_set(v_reuseFailAlloc_623_, 18, v_description_605_);
lean_ctor_set(v_reuseFailAlloc_623_, 19, v_keywords_606_);
lean_ctor_set(v_reuseFailAlloc_623_, 20, v_homepage_607_);
lean_ctor_set(v_reuseFailAlloc_623_, 21, v_license_608_);
lean_ctor_set(v_reuseFailAlloc_623_, 22, v_licenseFiles_609_);
lean_ctor_set(v_reuseFailAlloc_623_, 23, v_readmeFile_610_);
lean_ctor_set(v_reuseFailAlloc_623_, 24, v_enableArtifactCache_x3f_612_);
lean_ctor_set(v_reuseFailAlloc_623_, 25, v_restoreAllArtifacts_x3f_613_);
lean_ctor_set_uint8(v_reuseFailAlloc_623_, sizeof(void*)*26, v_bootstrap_586_);
lean_ctor_set_uint8(v_reuseFailAlloc_623_, sizeof(void*)*26 + 1, v_precompileModules_588_);
lean_ctor_set_uint8(v_reuseFailAlloc_623_, sizeof(void*)*26 + 2, v_preferReleaseBuild_598_);
lean_ctor_set_uint8(v_reuseFailAlloc_623_, sizeof(void*)*26 + 3, v_reservoir_611_);
lean_ctor_set_uint8(v_reuseFailAlloc_623_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_614_);
lean_ctor_set_uint8(v_reuseFailAlloc_623_, sizeof(void*)*26 + 5, v_allowImportAll_615_);
lean_ctor_set_uint8(v_reuseFailAlloc_623_, sizeof(void*)*26 + 6, v_fixedToolchain_616_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3(lean_object* v_x_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__2));
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3___boxed(lean_object* v_x_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lake_PackageConfig_srcDir___proj___lam__3(v_x_627_);
lean_dec_ref(v_x_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object* v_p_638_, lean_object* v_n_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___closed__4));
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object* v_p_641_, lean_object* v_n_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lake_PackageConfig_srcDir___proj(v_p_641_, v_n_642_);
lean_dec(v_n_642_);
lean_dec(v_p_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object* v_p_644_, lean_object* v_n_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lake_PackageConfig_srcDir___proj(v_p_644_, v_n_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object* v_p_647_, lean_object* v_n_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lake_PackageConfig_srcDir_instConfigField(v_p_647_, v_n_648_);
lean_dec(v_n_648_);
lean_dec(v_p_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0(lean_object* v_cfg_650_){
_start:
{
lean_object* v_buildDir_651_; 
v_buildDir_651_ = lean_ctor_get(v_cfg_650_, 5);
lean_inc_ref(v_buildDir_651_);
return v_buildDir_651_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0___boxed(lean_object* v_cfg_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lake_PackageConfig_buildDir___proj___lam__0(v_cfg_652_);
lean_dec_ref(v_cfg_652_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__1(lean_object* v_val_654_, lean_object* v_cfg_655_){
_start:
{
lean_object* v_toWorkspaceConfig_656_; lean_object* v_toLeanConfig_657_; uint8_t v_bootstrap_658_; lean_object* v_extraDepTargets_659_; uint8_t v_precompileModules_660_; lean_object* v_moreGlobalServerArgs_661_; lean_object* v_srcDir_662_; lean_object* v_leanLibDir_663_; lean_object* v_nativeLibDir_664_; lean_object* v_binDir_665_; lean_object* v_irDir_666_; lean_object* v_releaseRepo_667_; lean_object* v_buildArchive_668_; uint8_t v_preferReleaseBuild_669_; lean_object* v_testDriver_670_; lean_object* v_testDriverArgs_671_; lean_object* v_lintDriver_672_; lean_object* v_lintDriverArgs_673_; lean_object* v_version_674_; lean_object* v_versionTags_675_; lean_object* v_description_676_; lean_object* v_keywords_677_; lean_object* v_homepage_678_; lean_object* v_license_679_; lean_object* v_licenseFiles_680_; lean_object* v_readmeFile_681_; uint8_t v_reservoir_682_; lean_object* v_enableArtifactCache_x3f_683_; lean_object* v_restoreAllArtifacts_x3f_684_; uint8_t v_libPrefixOnWindows_685_; uint8_t v_allowImportAll_686_; uint8_t v_fixedToolchain_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
v_toWorkspaceConfig_656_ = lean_ctor_get(v_cfg_655_, 0);
v_toLeanConfig_657_ = lean_ctor_get(v_cfg_655_, 1);
v_bootstrap_658_ = lean_ctor_get_uint8(v_cfg_655_, sizeof(void*)*26);
v_extraDepTargets_659_ = lean_ctor_get(v_cfg_655_, 2);
v_precompileModules_660_ = lean_ctor_get_uint8(v_cfg_655_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_661_ = lean_ctor_get(v_cfg_655_, 3);
v_srcDir_662_ = lean_ctor_get(v_cfg_655_, 4);
v_leanLibDir_663_ = lean_ctor_get(v_cfg_655_, 6);
v_nativeLibDir_664_ = lean_ctor_get(v_cfg_655_, 7);
v_binDir_665_ = lean_ctor_get(v_cfg_655_, 8);
v_irDir_666_ = lean_ctor_get(v_cfg_655_, 9);
v_releaseRepo_667_ = lean_ctor_get(v_cfg_655_, 10);
v_buildArchive_668_ = lean_ctor_get(v_cfg_655_, 11);
v_preferReleaseBuild_669_ = lean_ctor_get_uint8(v_cfg_655_, sizeof(void*)*26 + 2);
v_testDriver_670_ = lean_ctor_get(v_cfg_655_, 12);
v_testDriverArgs_671_ = lean_ctor_get(v_cfg_655_, 13);
v_lintDriver_672_ = lean_ctor_get(v_cfg_655_, 14);
v_lintDriverArgs_673_ = lean_ctor_get(v_cfg_655_, 15);
v_version_674_ = lean_ctor_get(v_cfg_655_, 16);
v_versionTags_675_ = lean_ctor_get(v_cfg_655_, 17);
v_description_676_ = lean_ctor_get(v_cfg_655_, 18);
v_keywords_677_ = lean_ctor_get(v_cfg_655_, 19);
v_homepage_678_ = lean_ctor_get(v_cfg_655_, 20);
v_license_679_ = lean_ctor_get(v_cfg_655_, 21);
v_licenseFiles_680_ = lean_ctor_get(v_cfg_655_, 22);
v_readmeFile_681_ = lean_ctor_get(v_cfg_655_, 23);
v_reservoir_682_ = lean_ctor_get_uint8(v_cfg_655_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_683_ = lean_ctor_get(v_cfg_655_, 24);
v_restoreAllArtifacts_x3f_684_ = lean_ctor_get(v_cfg_655_, 25);
v_libPrefixOnWindows_685_ = lean_ctor_get_uint8(v_cfg_655_, sizeof(void*)*26 + 4);
v_allowImportAll_686_ = lean_ctor_get_uint8(v_cfg_655_, sizeof(void*)*26 + 5);
v_fixedToolchain_687_ = lean_ctor_get_uint8(v_cfg_655_, sizeof(void*)*26 + 6);
v_isSharedCheck_694_ = !lean_is_exclusive(v_cfg_655_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v_cfg_655_, 5);
lean_dec(v_unused_695_);
v___x_689_ = v_cfg_655_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_684_);
lean_inc(v_enableArtifactCache_x3f_683_);
lean_inc(v_readmeFile_681_);
lean_inc(v_licenseFiles_680_);
lean_inc(v_license_679_);
lean_inc(v_homepage_678_);
lean_inc(v_keywords_677_);
lean_inc(v_description_676_);
lean_inc(v_versionTags_675_);
lean_inc(v_version_674_);
lean_inc(v_lintDriverArgs_673_);
lean_inc(v_lintDriver_672_);
lean_inc(v_testDriverArgs_671_);
lean_inc(v_testDriver_670_);
lean_inc(v_buildArchive_668_);
lean_inc(v_releaseRepo_667_);
lean_inc(v_irDir_666_);
lean_inc(v_binDir_665_);
lean_inc(v_nativeLibDir_664_);
lean_inc(v_leanLibDir_663_);
lean_inc(v_srcDir_662_);
lean_inc(v_moreGlobalServerArgs_661_);
lean_inc(v_extraDepTargets_659_);
lean_inc(v_toLeanConfig_657_);
lean_inc(v_toWorkspaceConfig_656_);
lean_dec(v_cfg_655_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 5, v_val_654_);
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_toWorkspaceConfig_656_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_toLeanConfig_657_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_extraDepTargets_659_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v_moreGlobalServerArgs_661_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v_srcDir_662_);
lean_ctor_set(v_reuseFailAlloc_693_, 5, v_val_654_);
lean_ctor_set(v_reuseFailAlloc_693_, 6, v_leanLibDir_663_);
lean_ctor_set(v_reuseFailAlloc_693_, 7, v_nativeLibDir_664_);
lean_ctor_set(v_reuseFailAlloc_693_, 8, v_binDir_665_);
lean_ctor_set(v_reuseFailAlloc_693_, 9, v_irDir_666_);
lean_ctor_set(v_reuseFailAlloc_693_, 10, v_releaseRepo_667_);
lean_ctor_set(v_reuseFailAlloc_693_, 11, v_buildArchive_668_);
lean_ctor_set(v_reuseFailAlloc_693_, 12, v_testDriver_670_);
lean_ctor_set(v_reuseFailAlloc_693_, 13, v_testDriverArgs_671_);
lean_ctor_set(v_reuseFailAlloc_693_, 14, v_lintDriver_672_);
lean_ctor_set(v_reuseFailAlloc_693_, 15, v_lintDriverArgs_673_);
lean_ctor_set(v_reuseFailAlloc_693_, 16, v_version_674_);
lean_ctor_set(v_reuseFailAlloc_693_, 17, v_versionTags_675_);
lean_ctor_set(v_reuseFailAlloc_693_, 18, v_description_676_);
lean_ctor_set(v_reuseFailAlloc_693_, 19, v_keywords_677_);
lean_ctor_set(v_reuseFailAlloc_693_, 20, v_homepage_678_);
lean_ctor_set(v_reuseFailAlloc_693_, 21, v_license_679_);
lean_ctor_set(v_reuseFailAlloc_693_, 22, v_licenseFiles_680_);
lean_ctor_set(v_reuseFailAlloc_693_, 23, v_readmeFile_681_);
lean_ctor_set(v_reuseFailAlloc_693_, 24, v_enableArtifactCache_x3f_683_);
lean_ctor_set(v_reuseFailAlloc_693_, 25, v_restoreAllArtifacts_x3f_684_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*26, v_bootstrap_658_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*26 + 1, v_precompileModules_660_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*26 + 2, v_preferReleaseBuild_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*26 + 3, v_reservoir_682_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_685_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*26 + 5, v_allowImportAll_686_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*26 + 6, v_fixedToolchain_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__2(lean_object* v_f_696_, lean_object* v_cfg_697_){
_start:
{
lean_object* v_toWorkspaceConfig_698_; lean_object* v_toLeanConfig_699_; uint8_t v_bootstrap_700_; lean_object* v_extraDepTargets_701_; uint8_t v_precompileModules_702_; lean_object* v_moreGlobalServerArgs_703_; lean_object* v_srcDir_704_; lean_object* v_buildDir_705_; lean_object* v_leanLibDir_706_; lean_object* v_nativeLibDir_707_; lean_object* v_binDir_708_; lean_object* v_irDir_709_; lean_object* v_releaseRepo_710_; lean_object* v_buildArchive_711_; uint8_t v_preferReleaseBuild_712_; lean_object* v_testDriver_713_; lean_object* v_testDriverArgs_714_; lean_object* v_lintDriver_715_; lean_object* v_lintDriverArgs_716_; lean_object* v_version_717_; lean_object* v_versionTags_718_; lean_object* v_description_719_; lean_object* v_keywords_720_; lean_object* v_homepage_721_; lean_object* v_license_722_; lean_object* v_licenseFiles_723_; lean_object* v_readmeFile_724_; uint8_t v_reservoir_725_; lean_object* v_enableArtifactCache_x3f_726_; lean_object* v_restoreAllArtifacts_x3f_727_; uint8_t v_libPrefixOnWindows_728_; uint8_t v_allowImportAll_729_; uint8_t v_fixedToolchain_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_738_; 
v_toWorkspaceConfig_698_ = lean_ctor_get(v_cfg_697_, 0);
v_toLeanConfig_699_ = lean_ctor_get(v_cfg_697_, 1);
v_bootstrap_700_ = lean_ctor_get_uint8(v_cfg_697_, sizeof(void*)*26);
v_extraDepTargets_701_ = lean_ctor_get(v_cfg_697_, 2);
v_precompileModules_702_ = lean_ctor_get_uint8(v_cfg_697_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_703_ = lean_ctor_get(v_cfg_697_, 3);
v_srcDir_704_ = lean_ctor_get(v_cfg_697_, 4);
v_buildDir_705_ = lean_ctor_get(v_cfg_697_, 5);
v_leanLibDir_706_ = lean_ctor_get(v_cfg_697_, 6);
v_nativeLibDir_707_ = lean_ctor_get(v_cfg_697_, 7);
v_binDir_708_ = lean_ctor_get(v_cfg_697_, 8);
v_irDir_709_ = lean_ctor_get(v_cfg_697_, 9);
v_releaseRepo_710_ = lean_ctor_get(v_cfg_697_, 10);
v_buildArchive_711_ = lean_ctor_get(v_cfg_697_, 11);
v_preferReleaseBuild_712_ = lean_ctor_get_uint8(v_cfg_697_, sizeof(void*)*26 + 2);
v_testDriver_713_ = lean_ctor_get(v_cfg_697_, 12);
v_testDriverArgs_714_ = lean_ctor_get(v_cfg_697_, 13);
v_lintDriver_715_ = lean_ctor_get(v_cfg_697_, 14);
v_lintDriverArgs_716_ = lean_ctor_get(v_cfg_697_, 15);
v_version_717_ = lean_ctor_get(v_cfg_697_, 16);
v_versionTags_718_ = lean_ctor_get(v_cfg_697_, 17);
v_description_719_ = lean_ctor_get(v_cfg_697_, 18);
v_keywords_720_ = lean_ctor_get(v_cfg_697_, 19);
v_homepage_721_ = lean_ctor_get(v_cfg_697_, 20);
v_license_722_ = lean_ctor_get(v_cfg_697_, 21);
v_licenseFiles_723_ = lean_ctor_get(v_cfg_697_, 22);
v_readmeFile_724_ = lean_ctor_get(v_cfg_697_, 23);
v_reservoir_725_ = lean_ctor_get_uint8(v_cfg_697_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_726_ = lean_ctor_get(v_cfg_697_, 24);
v_restoreAllArtifacts_x3f_727_ = lean_ctor_get(v_cfg_697_, 25);
v_libPrefixOnWindows_728_ = lean_ctor_get_uint8(v_cfg_697_, sizeof(void*)*26 + 4);
v_allowImportAll_729_ = lean_ctor_get_uint8(v_cfg_697_, sizeof(void*)*26 + 5);
v_fixedToolchain_730_ = lean_ctor_get_uint8(v_cfg_697_, sizeof(void*)*26 + 6);
v_isSharedCheck_738_ = !lean_is_exclusive(v_cfg_697_);
if (v_isSharedCheck_738_ == 0)
{
v___x_732_ = v_cfg_697_;
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_727_);
lean_inc(v_enableArtifactCache_x3f_726_);
lean_inc(v_readmeFile_724_);
lean_inc(v_licenseFiles_723_);
lean_inc(v_license_722_);
lean_inc(v_homepage_721_);
lean_inc(v_keywords_720_);
lean_inc(v_description_719_);
lean_inc(v_versionTags_718_);
lean_inc(v_version_717_);
lean_inc(v_lintDriverArgs_716_);
lean_inc(v_lintDriver_715_);
lean_inc(v_testDriverArgs_714_);
lean_inc(v_testDriver_713_);
lean_inc(v_buildArchive_711_);
lean_inc(v_releaseRepo_710_);
lean_inc(v_irDir_709_);
lean_inc(v_binDir_708_);
lean_inc(v_nativeLibDir_707_);
lean_inc(v_leanLibDir_706_);
lean_inc(v_buildDir_705_);
lean_inc(v_srcDir_704_);
lean_inc(v_moreGlobalServerArgs_703_);
lean_inc(v_extraDepTargets_701_);
lean_inc(v_toLeanConfig_699_);
lean_inc(v_toWorkspaceConfig_698_);
lean_dec(v_cfg_697_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_734_ = lean_apply_1(v_f_696_, v_buildDir_705_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 5, v___x_734_);
v___x_736_ = v___x_732_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_toWorkspaceConfig_698_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_toLeanConfig_699_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_extraDepTargets_701_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v_moreGlobalServerArgs_703_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_srcDir_704_);
lean_ctor_set(v_reuseFailAlloc_737_, 5, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_737_, 6, v_leanLibDir_706_);
lean_ctor_set(v_reuseFailAlloc_737_, 7, v_nativeLibDir_707_);
lean_ctor_set(v_reuseFailAlloc_737_, 8, v_binDir_708_);
lean_ctor_set(v_reuseFailAlloc_737_, 9, v_irDir_709_);
lean_ctor_set(v_reuseFailAlloc_737_, 10, v_releaseRepo_710_);
lean_ctor_set(v_reuseFailAlloc_737_, 11, v_buildArchive_711_);
lean_ctor_set(v_reuseFailAlloc_737_, 12, v_testDriver_713_);
lean_ctor_set(v_reuseFailAlloc_737_, 13, v_testDriverArgs_714_);
lean_ctor_set(v_reuseFailAlloc_737_, 14, v_lintDriver_715_);
lean_ctor_set(v_reuseFailAlloc_737_, 15, v_lintDriverArgs_716_);
lean_ctor_set(v_reuseFailAlloc_737_, 16, v_version_717_);
lean_ctor_set(v_reuseFailAlloc_737_, 17, v_versionTags_718_);
lean_ctor_set(v_reuseFailAlloc_737_, 18, v_description_719_);
lean_ctor_set(v_reuseFailAlloc_737_, 19, v_keywords_720_);
lean_ctor_set(v_reuseFailAlloc_737_, 20, v_homepage_721_);
lean_ctor_set(v_reuseFailAlloc_737_, 21, v_license_722_);
lean_ctor_set(v_reuseFailAlloc_737_, 22, v_licenseFiles_723_);
lean_ctor_set(v_reuseFailAlloc_737_, 23, v_readmeFile_724_);
lean_ctor_set(v_reuseFailAlloc_737_, 24, v_enableArtifactCache_x3f_726_);
lean_ctor_set(v_reuseFailAlloc_737_, 25, v_restoreAllArtifacts_x3f_727_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*26, v_bootstrap_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*26 + 1, v_precompileModules_702_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*26 + 2, v_preferReleaseBuild_712_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*26 + 3, v_reservoir_725_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_728_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*26 + 5, v_allowImportAll_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*26 + 6, v_fixedToolchain_730_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3(lean_object* v_x_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lake_defaultBuildDir;
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3___boxed(lean_object* v_x_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lake_PackageConfig_buildDir___proj___lam__3(v_x_741_);
lean_dec_ref(v_x_741_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object* v_p_752_, lean_object* v_n_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = ((lean_object*)(l_Lake_PackageConfig_buildDir___proj___closed__4));
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object* v_p_755_, lean_object* v_n_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lake_PackageConfig_buildDir___proj(v_p_755_, v_n_756_);
lean_dec(v_n_756_);
lean_dec(v_p_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object* v_p_758_, lean_object* v_n_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lake_PackageConfig_buildDir___proj(v_p_758_, v_n_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object* v_p_761_, lean_object* v_n_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lake_PackageConfig_buildDir_instConfigField(v_p_761_, v_n_762_);
lean_dec(v_n_762_);
lean_dec(v_p_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0(lean_object* v_cfg_764_){
_start:
{
lean_object* v_leanLibDir_765_; 
v_leanLibDir_765_ = lean_ctor_get(v_cfg_764_, 6);
lean_inc_ref(v_leanLibDir_765_);
return v_leanLibDir_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0___boxed(lean_object* v_cfg_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lake_PackageConfig_leanLibDir___proj___lam__0(v_cfg_766_);
lean_dec_ref(v_cfg_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__1(lean_object* v_val_768_, lean_object* v_cfg_769_){
_start:
{
lean_object* v_toWorkspaceConfig_770_; lean_object* v_toLeanConfig_771_; uint8_t v_bootstrap_772_; lean_object* v_extraDepTargets_773_; uint8_t v_precompileModules_774_; lean_object* v_moreGlobalServerArgs_775_; lean_object* v_srcDir_776_; lean_object* v_buildDir_777_; lean_object* v_nativeLibDir_778_; lean_object* v_binDir_779_; lean_object* v_irDir_780_; lean_object* v_releaseRepo_781_; lean_object* v_buildArchive_782_; uint8_t v_preferReleaseBuild_783_; lean_object* v_testDriver_784_; lean_object* v_testDriverArgs_785_; lean_object* v_lintDriver_786_; lean_object* v_lintDriverArgs_787_; lean_object* v_version_788_; lean_object* v_versionTags_789_; lean_object* v_description_790_; lean_object* v_keywords_791_; lean_object* v_homepage_792_; lean_object* v_license_793_; lean_object* v_licenseFiles_794_; lean_object* v_readmeFile_795_; uint8_t v_reservoir_796_; lean_object* v_enableArtifactCache_x3f_797_; lean_object* v_restoreAllArtifacts_x3f_798_; uint8_t v_libPrefixOnWindows_799_; uint8_t v_allowImportAll_800_; uint8_t v_fixedToolchain_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
v_toWorkspaceConfig_770_ = lean_ctor_get(v_cfg_769_, 0);
v_toLeanConfig_771_ = lean_ctor_get(v_cfg_769_, 1);
v_bootstrap_772_ = lean_ctor_get_uint8(v_cfg_769_, sizeof(void*)*26);
v_extraDepTargets_773_ = lean_ctor_get(v_cfg_769_, 2);
v_precompileModules_774_ = lean_ctor_get_uint8(v_cfg_769_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_775_ = lean_ctor_get(v_cfg_769_, 3);
v_srcDir_776_ = lean_ctor_get(v_cfg_769_, 4);
v_buildDir_777_ = lean_ctor_get(v_cfg_769_, 5);
v_nativeLibDir_778_ = lean_ctor_get(v_cfg_769_, 7);
v_binDir_779_ = lean_ctor_get(v_cfg_769_, 8);
v_irDir_780_ = lean_ctor_get(v_cfg_769_, 9);
v_releaseRepo_781_ = lean_ctor_get(v_cfg_769_, 10);
v_buildArchive_782_ = lean_ctor_get(v_cfg_769_, 11);
v_preferReleaseBuild_783_ = lean_ctor_get_uint8(v_cfg_769_, sizeof(void*)*26 + 2);
v_testDriver_784_ = lean_ctor_get(v_cfg_769_, 12);
v_testDriverArgs_785_ = lean_ctor_get(v_cfg_769_, 13);
v_lintDriver_786_ = lean_ctor_get(v_cfg_769_, 14);
v_lintDriverArgs_787_ = lean_ctor_get(v_cfg_769_, 15);
v_version_788_ = lean_ctor_get(v_cfg_769_, 16);
v_versionTags_789_ = lean_ctor_get(v_cfg_769_, 17);
v_description_790_ = lean_ctor_get(v_cfg_769_, 18);
v_keywords_791_ = lean_ctor_get(v_cfg_769_, 19);
v_homepage_792_ = lean_ctor_get(v_cfg_769_, 20);
v_license_793_ = lean_ctor_get(v_cfg_769_, 21);
v_licenseFiles_794_ = lean_ctor_get(v_cfg_769_, 22);
v_readmeFile_795_ = lean_ctor_get(v_cfg_769_, 23);
v_reservoir_796_ = lean_ctor_get_uint8(v_cfg_769_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_797_ = lean_ctor_get(v_cfg_769_, 24);
v_restoreAllArtifacts_x3f_798_ = lean_ctor_get(v_cfg_769_, 25);
v_libPrefixOnWindows_799_ = lean_ctor_get_uint8(v_cfg_769_, sizeof(void*)*26 + 4);
v_allowImportAll_800_ = lean_ctor_get_uint8(v_cfg_769_, sizeof(void*)*26 + 5);
v_fixedToolchain_801_ = lean_ctor_get_uint8(v_cfg_769_, sizeof(void*)*26 + 6);
v_isSharedCheck_808_ = !lean_is_exclusive(v_cfg_769_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v_cfg_769_, 6);
lean_dec(v_unused_809_);
v___x_803_ = v_cfg_769_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_798_);
lean_inc(v_enableArtifactCache_x3f_797_);
lean_inc(v_readmeFile_795_);
lean_inc(v_licenseFiles_794_);
lean_inc(v_license_793_);
lean_inc(v_homepage_792_);
lean_inc(v_keywords_791_);
lean_inc(v_description_790_);
lean_inc(v_versionTags_789_);
lean_inc(v_version_788_);
lean_inc(v_lintDriverArgs_787_);
lean_inc(v_lintDriver_786_);
lean_inc(v_testDriverArgs_785_);
lean_inc(v_testDriver_784_);
lean_inc(v_buildArchive_782_);
lean_inc(v_releaseRepo_781_);
lean_inc(v_irDir_780_);
lean_inc(v_binDir_779_);
lean_inc(v_nativeLibDir_778_);
lean_inc(v_buildDir_777_);
lean_inc(v_srcDir_776_);
lean_inc(v_moreGlobalServerArgs_775_);
lean_inc(v_extraDepTargets_773_);
lean_inc(v_toLeanConfig_771_);
lean_inc(v_toWorkspaceConfig_770_);
lean_dec(v_cfg_769_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 6, v_val_768_);
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_toWorkspaceConfig_770_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_toLeanConfig_771_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_extraDepTargets_773_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v_moreGlobalServerArgs_775_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v_srcDir_776_);
lean_ctor_set(v_reuseFailAlloc_807_, 5, v_buildDir_777_);
lean_ctor_set(v_reuseFailAlloc_807_, 6, v_val_768_);
lean_ctor_set(v_reuseFailAlloc_807_, 7, v_nativeLibDir_778_);
lean_ctor_set(v_reuseFailAlloc_807_, 8, v_binDir_779_);
lean_ctor_set(v_reuseFailAlloc_807_, 9, v_irDir_780_);
lean_ctor_set(v_reuseFailAlloc_807_, 10, v_releaseRepo_781_);
lean_ctor_set(v_reuseFailAlloc_807_, 11, v_buildArchive_782_);
lean_ctor_set(v_reuseFailAlloc_807_, 12, v_testDriver_784_);
lean_ctor_set(v_reuseFailAlloc_807_, 13, v_testDriverArgs_785_);
lean_ctor_set(v_reuseFailAlloc_807_, 14, v_lintDriver_786_);
lean_ctor_set(v_reuseFailAlloc_807_, 15, v_lintDriverArgs_787_);
lean_ctor_set(v_reuseFailAlloc_807_, 16, v_version_788_);
lean_ctor_set(v_reuseFailAlloc_807_, 17, v_versionTags_789_);
lean_ctor_set(v_reuseFailAlloc_807_, 18, v_description_790_);
lean_ctor_set(v_reuseFailAlloc_807_, 19, v_keywords_791_);
lean_ctor_set(v_reuseFailAlloc_807_, 20, v_homepage_792_);
lean_ctor_set(v_reuseFailAlloc_807_, 21, v_license_793_);
lean_ctor_set(v_reuseFailAlloc_807_, 22, v_licenseFiles_794_);
lean_ctor_set(v_reuseFailAlloc_807_, 23, v_readmeFile_795_);
lean_ctor_set(v_reuseFailAlloc_807_, 24, v_enableArtifactCache_x3f_797_);
lean_ctor_set(v_reuseFailAlloc_807_, 25, v_restoreAllArtifacts_x3f_798_);
lean_ctor_set_uint8(v_reuseFailAlloc_807_, sizeof(void*)*26, v_bootstrap_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_807_, sizeof(void*)*26 + 1, v_precompileModules_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_807_, sizeof(void*)*26 + 2, v_preferReleaseBuild_783_);
lean_ctor_set_uint8(v_reuseFailAlloc_807_, sizeof(void*)*26 + 3, v_reservoir_796_);
lean_ctor_set_uint8(v_reuseFailAlloc_807_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_799_);
lean_ctor_set_uint8(v_reuseFailAlloc_807_, sizeof(void*)*26 + 5, v_allowImportAll_800_);
lean_ctor_set_uint8(v_reuseFailAlloc_807_, sizeof(void*)*26 + 6, v_fixedToolchain_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__2(lean_object* v_f_810_, lean_object* v_cfg_811_){
_start:
{
lean_object* v_toWorkspaceConfig_812_; lean_object* v_toLeanConfig_813_; uint8_t v_bootstrap_814_; lean_object* v_extraDepTargets_815_; uint8_t v_precompileModules_816_; lean_object* v_moreGlobalServerArgs_817_; lean_object* v_srcDir_818_; lean_object* v_buildDir_819_; lean_object* v_leanLibDir_820_; lean_object* v_nativeLibDir_821_; lean_object* v_binDir_822_; lean_object* v_irDir_823_; lean_object* v_releaseRepo_824_; lean_object* v_buildArchive_825_; uint8_t v_preferReleaseBuild_826_; lean_object* v_testDriver_827_; lean_object* v_testDriverArgs_828_; lean_object* v_lintDriver_829_; lean_object* v_lintDriverArgs_830_; lean_object* v_version_831_; lean_object* v_versionTags_832_; lean_object* v_description_833_; lean_object* v_keywords_834_; lean_object* v_homepage_835_; lean_object* v_license_836_; lean_object* v_licenseFiles_837_; lean_object* v_readmeFile_838_; uint8_t v_reservoir_839_; lean_object* v_enableArtifactCache_x3f_840_; lean_object* v_restoreAllArtifacts_x3f_841_; uint8_t v_libPrefixOnWindows_842_; uint8_t v_allowImportAll_843_; uint8_t v_fixedToolchain_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_852_; 
v_toWorkspaceConfig_812_ = lean_ctor_get(v_cfg_811_, 0);
v_toLeanConfig_813_ = lean_ctor_get(v_cfg_811_, 1);
v_bootstrap_814_ = lean_ctor_get_uint8(v_cfg_811_, sizeof(void*)*26);
v_extraDepTargets_815_ = lean_ctor_get(v_cfg_811_, 2);
v_precompileModules_816_ = lean_ctor_get_uint8(v_cfg_811_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_817_ = lean_ctor_get(v_cfg_811_, 3);
v_srcDir_818_ = lean_ctor_get(v_cfg_811_, 4);
v_buildDir_819_ = lean_ctor_get(v_cfg_811_, 5);
v_leanLibDir_820_ = lean_ctor_get(v_cfg_811_, 6);
v_nativeLibDir_821_ = lean_ctor_get(v_cfg_811_, 7);
v_binDir_822_ = lean_ctor_get(v_cfg_811_, 8);
v_irDir_823_ = lean_ctor_get(v_cfg_811_, 9);
v_releaseRepo_824_ = lean_ctor_get(v_cfg_811_, 10);
v_buildArchive_825_ = lean_ctor_get(v_cfg_811_, 11);
v_preferReleaseBuild_826_ = lean_ctor_get_uint8(v_cfg_811_, sizeof(void*)*26 + 2);
v_testDriver_827_ = lean_ctor_get(v_cfg_811_, 12);
v_testDriverArgs_828_ = lean_ctor_get(v_cfg_811_, 13);
v_lintDriver_829_ = lean_ctor_get(v_cfg_811_, 14);
v_lintDriverArgs_830_ = lean_ctor_get(v_cfg_811_, 15);
v_version_831_ = lean_ctor_get(v_cfg_811_, 16);
v_versionTags_832_ = lean_ctor_get(v_cfg_811_, 17);
v_description_833_ = lean_ctor_get(v_cfg_811_, 18);
v_keywords_834_ = lean_ctor_get(v_cfg_811_, 19);
v_homepage_835_ = lean_ctor_get(v_cfg_811_, 20);
v_license_836_ = lean_ctor_get(v_cfg_811_, 21);
v_licenseFiles_837_ = lean_ctor_get(v_cfg_811_, 22);
v_readmeFile_838_ = lean_ctor_get(v_cfg_811_, 23);
v_reservoir_839_ = lean_ctor_get_uint8(v_cfg_811_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_840_ = lean_ctor_get(v_cfg_811_, 24);
v_restoreAllArtifacts_x3f_841_ = lean_ctor_get(v_cfg_811_, 25);
v_libPrefixOnWindows_842_ = lean_ctor_get_uint8(v_cfg_811_, sizeof(void*)*26 + 4);
v_allowImportAll_843_ = lean_ctor_get_uint8(v_cfg_811_, sizeof(void*)*26 + 5);
v_fixedToolchain_844_ = lean_ctor_get_uint8(v_cfg_811_, sizeof(void*)*26 + 6);
v_isSharedCheck_852_ = !lean_is_exclusive(v_cfg_811_);
if (v_isSharedCheck_852_ == 0)
{
v___x_846_ = v_cfg_811_;
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_841_);
lean_inc(v_enableArtifactCache_x3f_840_);
lean_inc(v_readmeFile_838_);
lean_inc(v_licenseFiles_837_);
lean_inc(v_license_836_);
lean_inc(v_homepage_835_);
lean_inc(v_keywords_834_);
lean_inc(v_description_833_);
lean_inc(v_versionTags_832_);
lean_inc(v_version_831_);
lean_inc(v_lintDriverArgs_830_);
lean_inc(v_lintDriver_829_);
lean_inc(v_testDriverArgs_828_);
lean_inc(v_testDriver_827_);
lean_inc(v_buildArchive_825_);
lean_inc(v_releaseRepo_824_);
lean_inc(v_irDir_823_);
lean_inc(v_binDir_822_);
lean_inc(v_nativeLibDir_821_);
lean_inc(v_leanLibDir_820_);
lean_inc(v_buildDir_819_);
lean_inc(v_srcDir_818_);
lean_inc(v_moreGlobalServerArgs_817_);
lean_inc(v_extraDepTargets_815_);
lean_inc(v_toLeanConfig_813_);
lean_inc(v_toWorkspaceConfig_812_);
lean_dec(v_cfg_811_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = lean_apply_1(v_f_810_, v_leanLibDir_820_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 6, v___x_848_);
v___x_850_ = v___x_846_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_toWorkspaceConfig_812_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_toLeanConfig_813_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_extraDepTargets_815_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_moreGlobalServerArgs_817_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v_srcDir_818_);
lean_ctor_set(v_reuseFailAlloc_851_, 5, v_buildDir_819_);
lean_ctor_set(v_reuseFailAlloc_851_, 6, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_851_, 7, v_nativeLibDir_821_);
lean_ctor_set(v_reuseFailAlloc_851_, 8, v_binDir_822_);
lean_ctor_set(v_reuseFailAlloc_851_, 9, v_irDir_823_);
lean_ctor_set(v_reuseFailAlloc_851_, 10, v_releaseRepo_824_);
lean_ctor_set(v_reuseFailAlloc_851_, 11, v_buildArchive_825_);
lean_ctor_set(v_reuseFailAlloc_851_, 12, v_testDriver_827_);
lean_ctor_set(v_reuseFailAlloc_851_, 13, v_testDriverArgs_828_);
lean_ctor_set(v_reuseFailAlloc_851_, 14, v_lintDriver_829_);
lean_ctor_set(v_reuseFailAlloc_851_, 15, v_lintDriverArgs_830_);
lean_ctor_set(v_reuseFailAlloc_851_, 16, v_version_831_);
lean_ctor_set(v_reuseFailAlloc_851_, 17, v_versionTags_832_);
lean_ctor_set(v_reuseFailAlloc_851_, 18, v_description_833_);
lean_ctor_set(v_reuseFailAlloc_851_, 19, v_keywords_834_);
lean_ctor_set(v_reuseFailAlloc_851_, 20, v_homepage_835_);
lean_ctor_set(v_reuseFailAlloc_851_, 21, v_license_836_);
lean_ctor_set(v_reuseFailAlloc_851_, 22, v_licenseFiles_837_);
lean_ctor_set(v_reuseFailAlloc_851_, 23, v_readmeFile_838_);
lean_ctor_set(v_reuseFailAlloc_851_, 24, v_enableArtifactCache_x3f_840_);
lean_ctor_set(v_reuseFailAlloc_851_, 25, v_restoreAllArtifacts_x3f_841_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*26, v_bootstrap_814_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*26 + 1, v_precompileModules_816_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*26 + 2, v_preferReleaseBuild_826_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*26 + 3, v_reservoir_839_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_842_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*26 + 5, v_allowImportAll_843_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*26 + 6, v_fixedToolchain_844_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3(lean_object* v_x_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lake_defaultLeanLibDir;
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3___boxed(lean_object* v_x_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lake_PackageConfig_leanLibDir___proj___lam__3(v_x_855_);
lean_dec_ref(v_x_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object* v_p_866_, lean_object* v_n_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = ((lean_object*)(l_Lake_PackageConfig_leanLibDir___proj___closed__4));
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object* v_p_869_, lean_object* v_n_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_869_, v_n_870_);
lean_dec(v_n_870_);
lean_dec(v_p_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object* v_p_872_, lean_object* v_n_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_872_, v_n_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object* v_p_875_, lean_object* v_n_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lake_PackageConfig_leanLibDir_instConfigField(v_p_875_, v_n_876_);
lean_dec(v_n_876_);
lean_dec(v_p_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0(lean_object* v_cfg_878_){
_start:
{
lean_object* v_nativeLibDir_879_; 
v_nativeLibDir_879_ = lean_ctor_get(v_cfg_878_, 7);
lean_inc_ref(v_nativeLibDir_879_);
return v_nativeLibDir_879_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0___boxed(lean_object* v_cfg_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__0(v_cfg_880_);
lean_dec_ref(v_cfg_880_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__1(lean_object* v_val_882_, lean_object* v_cfg_883_){
_start:
{
lean_object* v_toWorkspaceConfig_884_; lean_object* v_toLeanConfig_885_; uint8_t v_bootstrap_886_; lean_object* v_extraDepTargets_887_; uint8_t v_precompileModules_888_; lean_object* v_moreGlobalServerArgs_889_; lean_object* v_srcDir_890_; lean_object* v_buildDir_891_; lean_object* v_leanLibDir_892_; lean_object* v_binDir_893_; lean_object* v_irDir_894_; lean_object* v_releaseRepo_895_; lean_object* v_buildArchive_896_; uint8_t v_preferReleaseBuild_897_; lean_object* v_testDriver_898_; lean_object* v_testDriverArgs_899_; lean_object* v_lintDriver_900_; lean_object* v_lintDriverArgs_901_; lean_object* v_version_902_; lean_object* v_versionTags_903_; lean_object* v_description_904_; lean_object* v_keywords_905_; lean_object* v_homepage_906_; lean_object* v_license_907_; lean_object* v_licenseFiles_908_; lean_object* v_readmeFile_909_; uint8_t v_reservoir_910_; lean_object* v_enableArtifactCache_x3f_911_; lean_object* v_restoreAllArtifacts_x3f_912_; uint8_t v_libPrefixOnWindows_913_; uint8_t v_allowImportAll_914_; uint8_t v_fixedToolchain_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
v_toWorkspaceConfig_884_ = lean_ctor_get(v_cfg_883_, 0);
v_toLeanConfig_885_ = lean_ctor_get(v_cfg_883_, 1);
v_bootstrap_886_ = lean_ctor_get_uint8(v_cfg_883_, sizeof(void*)*26);
v_extraDepTargets_887_ = lean_ctor_get(v_cfg_883_, 2);
v_precompileModules_888_ = lean_ctor_get_uint8(v_cfg_883_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_889_ = lean_ctor_get(v_cfg_883_, 3);
v_srcDir_890_ = lean_ctor_get(v_cfg_883_, 4);
v_buildDir_891_ = lean_ctor_get(v_cfg_883_, 5);
v_leanLibDir_892_ = lean_ctor_get(v_cfg_883_, 6);
v_binDir_893_ = lean_ctor_get(v_cfg_883_, 8);
v_irDir_894_ = lean_ctor_get(v_cfg_883_, 9);
v_releaseRepo_895_ = lean_ctor_get(v_cfg_883_, 10);
v_buildArchive_896_ = lean_ctor_get(v_cfg_883_, 11);
v_preferReleaseBuild_897_ = lean_ctor_get_uint8(v_cfg_883_, sizeof(void*)*26 + 2);
v_testDriver_898_ = lean_ctor_get(v_cfg_883_, 12);
v_testDriverArgs_899_ = lean_ctor_get(v_cfg_883_, 13);
v_lintDriver_900_ = lean_ctor_get(v_cfg_883_, 14);
v_lintDriverArgs_901_ = lean_ctor_get(v_cfg_883_, 15);
v_version_902_ = lean_ctor_get(v_cfg_883_, 16);
v_versionTags_903_ = lean_ctor_get(v_cfg_883_, 17);
v_description_904_ = lean_ctor_get(v_cfg_883_, 18);
v_keywords_905_ = lean_ctor_get(v_cfg_883_, 19);
v_homepage_906_ = lean_ctor_get(v_cfg_883_, 20);
v_license_907_ = lean_ctor_get(v_cfg_883_, 21);
v_licenseFiles_908_ = lean_ctor_get(v_cfg_883_, 22);
v_readmeFile_909_ = lean_ctor_get(v_cfg_883_, 23);
v_reservoir_910_ = lean_ctor_get_uint8(v_cfg_883_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_911_ = lean_ctor_get(v_cfg_883_, 24);
v_restoreAllArtifacts_x3f_912_ = lean_ctor_get(v_cfg_883_, 25);
v_libPrefixOnWindows_913_ = lean_ctor_get_uint8(v_cfg_883_, sizeof(void*)*26 + 4);
v_allowImportAll_914_ = lean_ctor_get_uint8(v_cfg_883_, sizeof(void*)*26 + 5);
v_fixedToolchain_915_ = lean_ctor_get_uint8(v_cfg_883_, sizeof(void*)*26 + 6);
v_isSharedCheck_922_ = !lean_is_exclusive(v_cfg_883_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v_cfg_883_, 7);
lean_dec(v_unused_923_);
v___x_917_ = v_cfg_883_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_912_);
lean_inc(v_enableArtifactCache_x3f_911_);
lean_inc(v_readmeFile_909_);
lean_inc(v_licenseFiles_908_);
lean_inc(v_license_907_);
lean_inc(v_homepage_906_);
lean_inc(v_keywords_905_);
lean_inc(v_description_904_);
lean_inc(v_versionTags_903_);
lean_inc(v_version_902_);
lean_inc(v_lintDriverArgs_901_);
lean_inc(v_lintDriver_900_);
lean_inc(v_testDriverArgs_899_);
lean_inc(v_testDriver_898_);
lean_inc(v_buildArchive_896_);
lean_inc(v_releaseRepo_895_);
lean_inc(v_irDir_894_);
lean_inc(v_binDir_893_);
lean_inc(v_leanLibDir_892_);
lean_inc(v_buildDir_891_);
lean_inc(v_srcDir_890_);
lean_inc(v_moreGlobalServerArgs_889_);
lean_inc(v_extraDepTargets_887_);
lean_inc(v_toLeanConfig_885_);
lean_inc(v_toWorkspaceConfig_884_);
lean_dec(v_cfg_883_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 7, v_val_882_);
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_toWorkspaceConfig_884_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_toLeanConfig_885_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_extraDepTargets_887_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_moreGlobalServerArgs_889_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_srcDir_890_);
lean_ctor_set(v_reuseFailAlloc_921_, 5, v_buildDir_891_);
lean_ctor_set(v_reuseFailAlloc_921_, 6, v_leanLibDir_892_);
lean_ctor_set(v_reuseFailAlloc_921_, 7, v_val_882_);
lean_ctor_set(v_reuseFailAlloc_921_, 8, v_binDir_893_);
lean_ctor_set(v_reuseFailAlloc_921_, 9, v_irDir_894_);
lean_ctor_set(v_reuseFailAlloc_921_, 10, v_releaseRepo_895_);
lean_ctor_set(v_reuseFailAlloc_921_, 11, v_buildArchive_896_);
lean_ctor_set(v_reuseFailAlloc_921_, 12, v_testDriver_898_);
lean_ctor_set(v_reuseFailAlloc_921_, 13, v_testDriverArgs_899_);
lean_ctor_set(v_reuseFailAlloc_921_, 14, v_lintDriver_900_);
lean_ctor_set(v_reuseFailAlloc_921_, 15, v_lintDriverArgs_901_);
lean_ctor_set(v_reuseFailAlloc_921_, 16, v_version_902_);
lean_ctor_set(v_reuseFailAlloc_921_, 17, v_versionTags_903_);
lean_ctor_set(v_reuseFailAlloc_921_, 18, v_description_904_);
lean_ctor_set(v_reuseFailAlloc_921_, 19, v_keywords_905_);
lean_ctor_set(v_reuseFailAlloc_921_, 20, v_homepage_906_);
lean_ctor_set(v_reuseFailAlloc_921_, 21, v_license_907_);
lean_ctor_set(v_reuseFailAlloc_921_, 22, v_licenseFiles_908_);
lean_ctor_set(v_reuseFailAlloc_921_, 23, v_readmeFile_909_);
lean_ctor_set(v_reuseFailAlloc_921_, 24, v_enableArtifactCache_x3f_911_);
lean_ctor_set(v_reuseFailAlloc_921_, 25, v_restoreAllArtifacts_x3f_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*26, v_bootstrap_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*26 + 1, v_precompileModules_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*26 + 2, v_preferReleaseBuild_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*26 + 3, v_reservoir_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*26 + 5, v_allowImportAll_914_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*26 + 6, v_fixedToolchain_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__2(lean_object* v_f_924_, lean_object* v_cfg_925_){
_start:
{
lean_object* v_toWorkspaceConfig_926_; lean_object* v_toLeanConfig_927_; uint8_t v_bootstrap_928_; lean_object* v_extraDepTargets_929_; uint8_t v_precompileModules_930_; lean_object* v_moreGlobalServerArgs_931_; lean_object* v_srcDir_932_; lean_object* v_buildDir_933_; lean_object* v_leanLibDir_934_; lean_object* v_nativeLibDir_935_; lean_object* v_binDir_936_; lean_object* v_irDir_937_; lean_object* v_releaseRepo_938_; lean_object* v_buildArchive_939_; uint8_t v_preferReleaseBuild_940_; lean_object* v_testDriver_941_; lean_object* v_testDriverArgs_942_; lean_object* v_lintDriver_943_; lean_object* v_lintDriverArgs_944_; lean_object* v_version_945_; lean_object* v_versionTags_946_; lean_object* v_description_947_; lean_object* v_keywords_948_; lean_object* v_homepage_949_; lean_object* v_license_950_; lean_object* v_licenseFiles_951_; lean_object* v_readmeFile_952_; uint8_t v_reservoir_953_; lean_object* v_enableArtifactCache_x3f_954_; lean_object* v_restoreAllArtifacts_x3f_955_; uint8_t v_libPrefixOnWindows_956_; uint8_t v_allowImportAll_957_; uint8_t v_fixedToolchain_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
v_toWorkspaceConfig_926_ = lean_ctor_get(v_cfg_925_, 0);
v_toLeanConfig_927_ = lean_ctor_get(v_cfg_925_, 1);
v_bootstrap_928_ = lean_ctor_get_uint8(v_cfg_925_, sizeof(void*)*26);
v_extraDepTargets_929_ = lean_ctor_get(v_cfg_925_, 2);
v_precompileModules_930_ = lean_ctor_get_uint8(v_cfg_925_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_931_ = lean_ctor_get(v_cfg_925_, 3);
v_srcDir_932_ = lean_ctor_get(v_cfg_925_, 4);
v_buildDir_933_ = lean_ctor_get(v_cfg_925_, 5);
v_leanLibDir_934_ = lean_ctor_get(v_cfg_925_, 6);
v_nativeLibDir_935_ = lean_ctor_get(v_cfg_925_, 7);
v_binDir_936_ = lean_ctor_get(v_cfg_925_, 8);
v_irDir_937_ = lean_ctor_get(v_cfg_925_, 9);
v_releaseRepo_938_ = lean_ctor_get(v_cfg_925_, 10);
v_buildArchive_939_ = lean_ctor_get(v_cfg_925_, 11);
v_preferReleaseBuild_940_ = lean_ctor_get_uint8(v_cfg_925_, sizeof(void*)*26 + 2);
v_testDriver_941_ = lean_ctor_get(v_cfg_925_, 12);
v_testDriverArgs_942_ = lean_ctor_get(v_cfg_925_, 13);
v_lintDriver_943_ = lean_ctor_get(v_cfg_925_, 14);
v_lintDriverArgs_944_ = lean_ctor_get(v_cfg_925_, 15);
v_version_945_ = lean_ctor_get(v_cfg_925_, 16);
v_versionTags_946_ = lean_ctor_get(v_cfg_925_, 17);
v_description_947_ = lean_ctor_get(v_cfg_925_, 18);
v_keywords_948_ = lean_ctor_get(v_cfg_925_, 19);
v_homepage_949_ = lean_ctor_get(v_cfg_925_, 20);
v_license_950_ = lean_ctor_get(v_cfg_925_, 21);
v_licenseFiles_951_ = lean_ctor_get(v_cfg_925_, 22);
v_readmeFile_952_ = lean_ctor_get(v_cfg_925_, 23);
v_reservoir_953_ = lean_ctor_get_uint8(v_cfg_925_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_954_ = lean_ctor_get(v_cfg_925_, 24);
v_restoreAllArtifacts_x3f_955_ = lean_ctor_get(v_cfg_925_, 25);
v_libPrefixOnWindows_956_ = lean_ctor_get_uint8(v_cfg_925_, sizeof(void*)*26 + 4);
v_allowImportAll_957_ = lean_ctor_get_uint8(v_cfg_925_, sizeof(void*)*26 + 5);
v_fixedToolchain_958_ = lean_ctor_get_uint8(v_cfg_925_, sizeof(void*)*26 + 6);
v_isSharedCheck_966_ = !lean_is_exclusive(v_cfg_925_);
if (v_isSharedCheck_966_ == 0)
{
v___x_960_ = v_cfg_925_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_955_);
lean_inc(v_enableArtifactCache_x3f_954_);
lean_inc(v_readmeFile_952_);
lean_inc(v_licenseFiles_951_);
lean_inc(v_license_950_);
lean_inc(v_homepage_949_);
lean_inc(v_keywords_948_);
lean_inc(v_description_947_);
lean_inc(v_versionTags_946_);
lean_inc(v_version_945_);
lean_inc(v_lintDriverArgs_944_);
lean_inc(v_lintDriver_943_);
lean_inc(v_testDriverArgs_942_);
lean_inc(v_testDriver_941_);
lean_inc(v_buildArchive_939_);
lean_inc(v_releaseRepo_938_);
lean_inc(v_irDir_937_);
lean_inc(v_binDir_936_);
lean_inc(v_nativeLibDir_935_);
lean_inc(v_leanLibDir_934_);
lean_inc(v_buildDir_933_);
lean_inc(v_srcDir_932_);
lean_inc(v_moreGlobalServerArgs_931_);
lean_inc(v_extraDepTargets_929_);
lean_inc(v_toLeanConfig_927_);
lean_inc(v_toWorkspaceConfig_926_);
lean_dec(v_cfg_925_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = lean_apply_1(v_f_924_, v_nativeLibDir_935_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 7, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_toWorkspaceConfig_926_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_toLeanConfig_927_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_extraDepTargets_929_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_moreGlobalServerArgs_931_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_srcDir_932_);
lean_ctor_set(v_reuseFailAlloc_965_, 5, v_buildDir_933_);
lean_ctor_set(v_reuseFailAlloc_965_, 6, v_leanLibDir_934_);
lean_ctor_set(v_reuseFailAlloc_965_, 7, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_965_, 8, v_binDir_936_);
lean_ctor_set(v_reuseFailAlloc_965_, 9, v_irDir_937_);
lean_ctor_set(v_reuseFailAlloc_965_, 10, v_releaseRepo_938_);
lean_ctor_set(v_reuseFailAlloc_965_, 11, v_buildArchive_939_);
lean_ctor_set(v_reuseFailAlloc_965_, 12, v_testDriver_941_);
lean_ctor_set(v_reuseFailAlloc_965_, 13, v_testDriverArgs_942_);
lean_ctor_set(v_reuseFailAlloc_965_, 14, v_lintDriver_943_);
lean_ctor_set(v_reuseFailAlloc_965_, 15, v_lintDriverArgs_944_);
lean_ctor_set(v_reuseFailAlloc_965_, 16, v_version_945_);
lean_ctor_set(v_reuseFailAlloc_965_, 17, v_versionTags_946_);
lean_ctor_set(v_reuseFailAlloc_965_, 18, v_description_947_);
lean_ctor_set(v_reuseFailAlloc_965_, 19, v_keywords_948_);
lean_ctor_set(v_reuseFailAlloc_965_, 20, v_homepage_949_);
lean_ctor_set(v_reuseFailAlloc_965_, 21, v_license_950_);
lean_ctor_set(v_reuseFailAlloc_965_, 22, v_licenseFiles_951_);
lean_ctor_set(v_reuseFailAlloc_965_, 23, v_readmeFile_952_);
lean_ctor_set(v_reuseFailAlloc_965_, 24, v_enableArtifactCache_x3f_954_);
lean_ctor_set(v_reuseFailAlloc_965_, 25, v_restoreAllArtifacts_x3f_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*26, v_bootstrap_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*26 + 1, v_precompileModules_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*26 + 2, v_preferReleaseBuild_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*26 + 3, v_reservoir_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*26 + 5, v_allowImportAll_957_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*26 + 6, v_fixedToolchain_958_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3(lean_object* v_x_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lake_defaultNativeLibDir;
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3___boxed(lean_object* v_x_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__3(v_x_969_);
lean_dec_ref(v_x_969_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object* v_p_980_, lean_object* v_n_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = ((lean_object*)(l_Lake_PackageConfig_nativeLibDir___proj___closed__4));
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object* v_p_983_, lean_object* v_n_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_983_, v_n_984_);
lean_dec(v_n_984_);
lean_dec(v_p_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object* v_p_986_, lean_object* v_n_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_986_, v_n_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object* v_p_989_, lean_object* v_n_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lake_PackageConfig_nativeLibDir_instConfigField(v_p_989_, v_n_990_);
lean_dec(v_n_990_);
lean_dec(v_p_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0(lean_object* v_cfg_992_){
_start:
{
lean_object* v_binDir_993_; 
v_binDir_993_ = lean_ctor_get(v_cfg_992_, 8);
lean_inc_ref(v_binDir_993_);
return v_binDir_993_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0___boxed(lean_object* v_cfg_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lake_PackageConfig_binDir___proj___lam__0(v_cfg_994_);
lean_dec_ref(v_cfg_994_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__1(lean_object* v_val_996_, lean_object* v_cfg_997_){
_start:
{
lean_object* v_toWorkspaceConfig_998_; lean_object* v_toLeanConfig_999_; uint8_t v_bootstrap_1000_; lean_object* v_extraDepTargets_1001_; uint8_t v_precompileModules_1002_; lean_object* v_moreGlobalServerArgs_1003_; lean_object* v_srcDir_1004_; lean_object* v_buildDir_1005_; lean_object* v_leanLibDir_1006_; lean_object* v_nativeLibDir_1007_; lean_object* v_irDir_1008_; lean_object* v_releaseRepo_1009_; lean_object* v_buildArchive_1010_; uint8_t v_preferReleaseBuild_1011_; lean_object* v_testDriver_1012_; lean_object* v_testDriverArgs_1013_; lean_object* v_lintDriver_1014_; lean_object* v_lintDriverArgs_1015_; lean_object* v_version_1016_; lean_object* v_versionTags_1017_; lean_object* v_description_1018_; lean_object* v_keywords_1019_; lean_object* v_homepage_1020_; lean_object* v_license_1021_; lean_object* v_licenseFiles_1022_; lean_object* v_readmeFile_1023_; uint8_t v_reservoir_1024_; lean_object* v_enableArtifactCache_x3f_1025_; lean_object* v_restoreAllArtifacts_x3f_1026_; uint8_t v_libPrefixOnWindows_1027_; uint8_t v_allowImportAll_1028_; uint8_t v_fixedToolchain_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_toWorkspaceConfig_998_ = lean_ctor_get(v_cfg_997_, 0);
v_toLeanConfig_999_ = lean_ctor_get(v_cfg_997_, 1);
v_bootstrap_1000_ = lean_ctor_get_uint8(v_cfg_997_, sizeof(void*)*26);
v_extraDepTargets_1001_ = lean_ctor_get(v_cfg_997_, 2);
v_precompileModules_1002_ = lean_ctor_get_uint8(v_cfg_997_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1003_ = lean_ctor_get(v_cfg_997_, 3);
v_srcDir_1004_ = lean_ctor_get(v_cfg_997_, 4);
v_buildDir_1005_ = lean_ctor_get(v_cfg_997_, 5);
v_leanLibDir_1006_ = lean_ctor_get(v_cfg_997_, 6);
v_nativeLibDir_1007_ = lean_ctor_get(v_cfg_997_, 7);
v_irDir_1008_ = lean_ctor_get(v_cfg_997_, 9);
v_releaseRepo_1009_ = lean_ctor_get(v_cfg_997_, 10);
v_buildArchive_1010_ = lean_ctor_get(v_cfg_997_, 11);
v_preferReleaseBuild_1011_ = lean_ctor_get_uint8(v_cfg_997_, sizeof(void*)*26 + 2);
v_testDriver_1012_ = lean_ctor_get(v_cfg_997_, 12);
v_testDriverArgs_1013_ = lean_ctor_get(v_cfg_997_, 13);
v_lintDriver_1014_ = lean_ctor_get(v_cfg_997_, 14);
v_lintDriverArgs_1015_ = lean_ctor_get(v_cfg_997_, 15);
v_version_1016_ = lean_ctor_get(v_cfg_997_, 16);
v_versionTags_1017_ = lean_ctor_get(v_cfg_997_, 17);
v_description_1018_ = lean_ctor_get(v_cfg_997_, 18);
v_keywords_1019_ = lean_ctor_get(v_cfg_997_, 19);
v_homepage_1020_ = lean_ctor_get(v_cfg_997_, 20);
v_license_1021_ = lean_ctor_get(v_cfg_997_, 21);
v_licenseFiles_1022_ = lean_ctor_get(v_cfg_997_, 22);
v_readmeFile_1023_ = lean_ctor_get(v_cfg_997_, 23);
v_reservoir_1024_ = lean_ctor_get_uint8(v_cfg_997_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1025_ = lean_ctor_get(v_cfg_997_, 24);
v_restoreAllArtifacts_x3f_1026_ = lean_ctor_get(v_cfg_997_, 25);
v_libPrefixOnWindows_1027_ = lean_ctor_get_uint8(v_cfg_997_, sizeof(void*)*26 + 4);
v_allowImportAll_1028_ = lean_ctor_get_uint8(v_cfg_997_, sizeof(void*)*26 + 5);
v_fixedToolchain_1029_ = lean_ctor_get_uint8(v_cfg_997_, sizeof(void*)*26 + 6);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_cfg_997_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v_cfg_997_, 8);
lean_dec(v_unused_1037_);
v___x_1031_ = v_cfg_997_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1026_);
lean_inc(v_enableArtifactCache_x3f_1025_);
lean_inc(v_readmeFile_1023_);
lean_inc(v_licenseFiles_1022_);
lean_inc(v_license_1021_);
lean_inc(v_homepage_1020_);
lean_inc(v_keywords_1019_);
lean_inc(v_description_1018_);
lean_inc(v_versionTags_1017_);
lean_inc(v_version_1016_);
lean_inc(v_lintDriverArgs_1015_);
lean_inc(v_lintDriver_1014_);
lean_inc(v_testDriverArgs_1013_);
lean_inc(v_testDriver_1012_);
lean_inc(v_buildArchive_1010_);
lean_inc(v_releaseRepo_1009_);
lean_inc(v_irDir_1008_);
lean_inc(v_nativeLibDir_1007_);
lean_inc(v_leanLibDir_1006_);
lean_inc(v_buildDir_1005_);
lean_inc(v_srcDir_1004_);
lean_inc(v_moreGlobalServerArgs_1003_);
lean_inc(v_extraDepTargets_1001_);
lean_inc(v_toLeanConfig_999_);
lean_inc(v_toWorkspaceConfig_998_);
lean_dec(v_cfg_997_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 8, v_val_996_);
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_toWorkspaceConfig_998_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_toLeanConfig_999_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_extraDepTargets_1001_);
lean_ctor_set(v_reuseFailAlloc_1035_, 3, v_moreGlobalServerArgs_1003_);
lean_ctor_set(v_reuseFailAlloc_1035_, 4, v_srcDir_1004_);
lean_ctor_set(v_reuseFailAlloc_1035_, 5, v_buildDir_1005_);
lean_ctor_set(v_reuseFailAlloc_1035_, 6, v_leanLibDir_1006_);
lean_ctor_set(v_reuseFailAlloc_1035_, 7, v_nativeLibDir_1007_);
lean_ctor_set(v_reuseFailAlloc_1035_, 8, v_val_996_);
lean_ctor_set(v_reuseFailAlloc_1035_, 9, v_irDir_1008_);
lean_ctor_set(v_reuseFailAlloc_1035_, 10, v_releaseRepo_1009_);
lean_ctor_set(v_reuseFailAlloc_1035_, 11, v_buildArchive_1010_);
lean_ctor_set(v_reuseFailAlloc_1035_, 12, v_testDriver_1012_);
lean_ctor_set(v_reuseFailAlloc_1035_, 13, v_testDriverArgs_1013_);
lean_ctor_set(v_reuseFailAlloc_1035_, 14, v_lintDriver_1014_);
lean_ctor_set(v_reuseFailAlloc_1035_, 15, v_lintDriverArgs_1015_);
lean_ctor_set(v_reuseFailAlloc_1035_, 16, v_version_1016_);
lean_ctor_set(v_reuseFailAlloc_1035_, 17, v_versionTags_1017_);
lean_ctor_set(v_reuseFailAlloc_1035_, 18, v_description_1018_);
lean_ctor_set(v_reuseFailAlloc_1035_, 19, v_keywords_1019_);
lean_ctor_set(v_reuseFailAlloc_1035_, 20, v_homepage_1020_);
lean_ctor_set(v_reuseFailAlloc_1035_, 21, v_license_1021_);
lean_ctor_set(v_reuseFailAlloc_1035_, 22, v_licenseFiles_1022_);
lean_ctor_set(v_reuseFailAlloc_1035_, 23, v_readmeFile_1023_);
lean_ctor_set(v_reuseFailAlloc_1035_, 24, v_enableArtifactCache_x3f_1025_);
lean_ctor_set(v_reuseFailAlloc_1035_, 25, v_restoreAllArtifacts_x3f_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*26, v_bootstrap_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*26 + 1, v_precompileModules_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*26 + 3, v_reservoir_1024_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1027_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*26 + 5, v_allowImportAll_1028_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*26 + 6, v_fixedToolchain_1029_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__2(lean_object* v_f_1038_, lean_object* v_cfg_1039_){
_start:
{
lean_object* v_toWorkspaceConfig_1040_; lean_object* v_toLeanConfig_1041_; uint8_t v_bootstrap_1042_; lean_object* v_extraDepTargets_1043_; uint8_t v_precompileModules_1044_; lean_object* v_moreGlobalServerArgs_1045_; lean_object* v_srcDir_1046_; lean_object* v_buildDir_1047_; lean_object* v_leanLibDir_1048_; lean_object* v_nativeLibDir_1049_; lean_object* v_binDir_1050_; lean_object* v_irDir_1051_; lean_object* v_releaseRepo_1052_; lean_object* v_buildArchive_1053_; uint8_t v_preferReleaseBuild_1054_; lean_object* v_testDriver_1055_; lean_object* v_testDriverArgs_1056_; lean_object* v_lintDriver_1057_; lean_object* v_lintDriverArgs_1058_; lean_object* v_version_1059_; lean_object* v_versionTags_1060_; lean_object* v_description_1061_; lean_object* v_keywords_1062_; lean_object* v_homepage_1063_; lean_object* v_license_1064_; lean_object* v_licenseFiles_1065_; lean_object* v_readmeFile_1066_; uint8_t v_reservoir_1067_; lean_object* v_enableArtifactCache_x3f_1068_; lean_object* v_restoreAllArtifacts_x3f_1069_; uint8_t v_libPrefixOnWindows_1070_; uint8_t v_allowImportAll_1071_; uint8_t v_fixedToolchain_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1080_; 
v_toWorkspaceConfig_1040_ = lean_ctor_get(v_cfg_1039_, 0);
v_toLeanConfig_1041_ = lean_ctor_get(v_cfg_1039_, 1);
v_bootstrap_1042_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*26);
v_extraDepTargets_1043_ = lean_ctor_get(v_cfg_1039_, 2);
v_precompileModules_1044_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1045_ = lean_ctor_get(v_cfg_1039_, 3);
v_srcDir_1046_ = lean_ctor_get(v_cfg_1039_, 4);
v_buildDir_1047_ = lean_ctor_get(v_cfg_1039_, 5);
v_leanLibDir_1048_ = lean_ctor_get(v_cfg_1039_, 6);
v_nativeLibDir_1049_ = lean_ctor_get(v_cfg_1039_, 7);
v_binDir_1050_ = lean_ctor_get(v_cfg_1039_, 8);
v_irDir_1051_ = lean_ctor_get(v_cfg_1039_, 9);
v_releaseRepo_1052_ = lean_ctor_get(v_cfg_1039_, 10);
v_buildArchive_1053_ = lean_ctor_get(v_cfg_1039_, 11);
v_preferReleaseBuild_1054_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*26 + 2);
v_testDriver_1055_ = lean_ctor_get(v_cfg_1039_, 12);
v_testDriverArgs_1056_ = lean_ctor_get(v_cfg_1039_, 13);
v_lintDriver_1057_ = lean_ctor_get(v_cfg_1039_, 14);
v_lintDriverArgs_1058_ = lean_ctor_get(v_cfg_1039_, 15);
v_version_1059_ = lean_ctor_get(v_cfg_1039_, 16);
v_versionTags_1060_ = lean_ctor_get(v_cfg_1039_, 17);
v_description_1061_ = lean_ctor_get(v_cfg_1039_, 18);
v_keywords_1062_ = lean_ctor_get(v_cfg_1039_, 19);
v_homepage_1063_ = lean_ctor_get(v_cfg_1039_, 20);
v_license_1064_ = lean_ctor_get(v_cfg_1039_, 21);
v_licenseFiles_1065_ = lean_ctor_get(v_cfg_1039_, 22);
v_readmeFile_1066_ = lean_ctor_get(v_cfg_1039_, 23);
v_reservoir_1067_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1068_ = lean_ctor_get(v_cfg_1039_, 24);
v_restoreAllArtifacts_x3f_1069_ = lean_ctor_get(v_cfg_1039_, 25);
v_libPrefixOnWindows_1070_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*26 + 4);
v_allowImportAll_1071_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*26 + 5);
v_fixedToolchain_1072_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*26 + 6);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_cfg_1039_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1074_ = v_cfg_1039_;
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1069_);
lean_inc(v_enableArtifactCache_x3f_1068_);
lean_inc(v_readmeFile_1066_);
lean_inc(v_licenseFiles_1065_);
lean_inc(v_license_1064_);
lean_inc(v_homepage_1063_);
lean_inc(v_keywords_1062_);
lean_inc(v_description_1061_);
lean_inc(v_versionTags_1060_);
lean_inc(v_version_1059_);
lean_inc(v_lintDriverArgs_1058_);
lean_inc(v_lintDriver_1057_);
lean_inc(v_testDriverArgs_1056_);
lean_inc(v_testDriver_1055_);
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
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = lean_apply_1(v_f_1038_, v_binDir_1050_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 8, v___x_1076_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_toWorkspaceConfig_1040_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_toLeanConfig_1041_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_extraDepTargets_1043_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_moreGlobalServerArgs_1045_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_srcDir_1046_);
lean_ctor_set(v_reuseFailAlloc_1079_, 5, v_buildDir_1047_);
lean_ctor_set(v_reuseFailAlloc_1079_, 6, v_leanLibDir_1048_);
lean_ctor_set(v_reuseFailAlloc_1079_, 7, v_nativeLibDir_1049_);
lean_ctor_set(v_reuseFailAlloc_1079_, 8, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1079_, 9, v_irDir_1051_);
lean_ctor_set(v_reuseFailAlloc_1079_, 10, v_releaseRepo_1052_);
lean_ctor_set(v_reuseFailAlloc_1079_, 11, v_buildArchive_1053_);
lean_ctor_set(v_reuseFailAlloc_1079_, 12, v_testDriver_1055_);
lean_ctor_set(v_reuseFailAlloc_1079_, 13, v_testDriverArgs_1056_);
lean_ctor_set(v_reuseFailAlloc_1079_, 14, v_lintDriver_1057_);
lean_ctor_set(v_reuseFailAlloc_1079_, 15, v_lintDriverArgs_1058_);
lean_ctor_set(v_reuseFailAlloc_1079_, 16, v_version_1059_);
lean_ctor_set(v_reuseFailAlloc_1079_, 17, v_versionTags_1060_);
lean_ctor_set(v_reuseFailAlloc_1079_, 18, v_description_1061_);
lean_ctor_set(v_reuseFailAlloc_1079_, 19, v_keywords_1062_);
lean_ctor_set(v_reuseFailAlloc_1079_, 20, v_homepage_1063_);
lean_ctor_set(v_reuseFailAlloc_1079_, 21, v_license_1064_);
lean_ctor_set(v_reuseFailAlloc_1079_, 22, v_licenseFiles_1065_);
lean_ctor_set(v_reuseFailAlloc_1079_, 23, v_readmeFile_1066_);
lean_ctor_set(v_reuseFailAlloc_1079_, 24, v_enableArtifactCache_x3f_1068_);
lean_ctor_set(v_reuseFailAlloc_1079_, 25, v_restoreAllArtifacts_x3f_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*26, v_bootstrap_1042_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*26 + 1, v_precompileModules_1044_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1054_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*26 + 3, v_reservoir_1067_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*26 + 5, v_allowImportAll_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*26 + 6, v_fixedToolchain_1072_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3(lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lake_defaultBinDir;
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3___boxed(lean_object* v_x_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lake_PackageConfig_binDir___proj___lam__3(v_x_1083_);
lean_dec_ref(v_x_1083_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object* v_p_1094_, lean_object* v_n_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = ((lean_object*)(l_Lake_PackageConfig_binDir___proj___closed__4));
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object* v_p_1097_, lean_object* v_n_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lake_PackageConfig_binDir___proj(v_p_1097_, v_n_1098_);
lean_dec(v_n_1098_);
lean_dec(v_p_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object* v_p_1100_, lean_object* v_n_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lake_PackageConfig_binDir___proj(v_p_1100_, v_n_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object* v_p_1103_, lean_object* v_n_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lake_PackageConfig_binDir_instConfigField(v_p_1103_, v_n_1104_);
lean_dec(v_n_1104_);
lean_dec(v_p_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0(lean_object* v_cfg_1106_){
_start:
{
lean_object* v_irDir_1107_; 
v_irDir_1107_ = lean_ctor_get(v_cfg_1106_, 9);
lean_inc_ref(v_irDir_1107_);
return v_irDir_1107_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0___boxed(lean_object* v_cfg_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lake_PackageConfig_irDir___proj___lam__0(v_cfg_1108_);
lean_dec_ref(v_cfg_1108_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__1(lean_object* v_val_1110_, lean_object* v_cfg_1111_){
_start:
{
lean_object* v_toWorkspaceConfig_1112_; lean_object* v_toLeanConfig_1113_; uint8_t v_bootstrap_1114_; lean_object* v_extraDepTargets_1115_; uint8_t v_precompileModules_1116_; lean_object* v_moreGlobalServerArgs_1117_; lean_object* v_srcDir_1118_; lean_object* v_buildDir_1119_; lean_object* v_leanLibDir_1120_; lean_object* v_nativeLibDir_1121_; lean_object* v_binDir_1122_; lean_object* v_releaseRepo_1123_; lean_object* v_buildArchive_1124_; uint8_t v_preferReleaseBuild_1125_; lean_object* v_testDriver_1126_; lean_object* v_testDriverArgs_1127_; lean_object* v_lintDriver_1128_; lean_object* v_lintDriverArgs_1129_; lean_object* v_version_1130_; lean_object* v_versionTags_1131_; lean_object* v_description_1132_; lean_object* v_keywords_1133_; lean_object* v_homepage_1134_; lean_object* v_license_1135_; lean_object* v_licenseFiles_1136_; lean_object* v_readmeFile_1137_; uint8_t v_reservoir_1138_; lean_object* v_enableArtifactCache_x3f_1139_; lean_object* v_restoreAllArtifacts_x3f_1140_; uint8_t v_libPrefixOnWindows_1141_; uint8_t v_allowImportAll_1142_; uint8_t v_fixedToolchain_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_toWorkspaceConfig_1112_ = lean_ctor_get(v_cfg_1111_, 0);
v_toLeanConfig_1113_ = lean_ctor_get(v_cfg_1111_, 1);
v_bootstrap_1114_ = lean_ctor_get_uint8(v_cfg_1111_, sizeof(void*)*26);
v_extraDepTargets_1115_ = lean_ctor_get(v_cfg_1111_, 2);
v_precompileModules_1116_ = lean_ctor_get_uint8(v_cfg_1111_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1117_ = lean_ctor_get(v_cfg_1111_, 3);
v_srcDir_1118_ = lean_ctor_get(v_cfg_1111_, 4);
v_buildDir_1119_ = lean_ctor_get(v_cfg_1111_, 5);
v_leanLibDir_1120_ = lean_ctor_get(v_cfg_1111_, 6);
v_nativeLibDir_1121_ = lean_ctor_get(v_cfg_1111_, 7);
v_binDir_1122_ = lean_ctor_get(v_cfg_1111_, 8);
v_releaseRepo_1123_ = lean_ctor_get(v_cfg_1111_, 10);
v_buildArchive_1124_ = lean_ctor_get(v_cfg_1111_, 11);
v_preferReleaseBuild_1125_ = lean_ctor_get_uint8(v_cfg_1111_, sizeof(void*)*26 + 2);
v_testDriver_1126_ = lean_ctor_get(v_cfg_1111_, 12);
v_testDriverArgs_1127_ = lean_ctor_get(v_cfg_1111_, 13);
v_lintDriver_1128_ = lean_ctor_get(v_cfg_1111_, 14);
v_lintDriverArgs_1129_ = lean_ctor_get(v_cfg_1111_, 15);
v_version_1130_ = lean_ctor_get(v_cfg_1111_, 16);
v_versionTags_1131_ = lean_ctor_get(v_cfg_1111_, 17);
v_description_1132_ = lean_ctor_get(v_cfg_1111_, 18);
v_keywords_1133_ = lean_ctor_get(v_cfg_1111_, 19);
v_homepage_1134_ = lean_ctor_get(v_cfg_1111_, 20);
v_license_1135_ = lean_ctor_get(v_cfg_1111_, 21);
v_licenseFiles_1136_ = lean_ctor_get(v_cfg_1111_, 22);
v_readmeFile_1137_ = lean_ctor_get(v_cfg_1111_, 23);
v_reservoir_1138_ = lean_ctor_get_uint8(v_cfg_1111_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1139_ = lean_ctor_get(v_cfg_1111_, 24);
v_restoreAllArtifacts_x3f_1140_ = lean_ctor_get(v_cfg_1111_, 25);
v_libPrefixOnWindows_1141_ = lean_ctor_get_uint8(v_cfg_1111_, sizeof(void*)*26 + 4);
v_allowImportAll_1142_ = lean_ctor_get_uint8(v_cfg_1111_, sizeof(void*)*26 + 5);
v_fixedToolchain_1143_ = lean_ctor_get_uint8(v_cfg_1111_, sizeof(void*)*26 + 6);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_cfg_1111_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v_cfg_1111_, 9);
lean_dec(v_unused_1151_);
v___x_1145_ = v_cfg_1111_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1140_);
lean_inc(v_enableArtifactCache_x3f_1139_);
lean_inc(v_readmeFile_1137_);
lean_inc(v_licenseFiles_1136_);
lean_inc(v_license_1135_);
lean_inc(v_homepage_1134_);
lean_inc(v_keywords_1133_);
lean_inc(v_description_1132_);
lean_inc(v_versionTags_1131_);
lean_inc(v_version_1130_);
lean_inc(v_lintDriverArgs_1129_);
lean_inc(v_lintDriver_1128_);
lean_inc(v_testDriverArgs_1127_);
lean_inc(v_testDriver_1126_);
lean_inc(v_buildArchive_1124_);
lean_inc(v_releaseRepo_1123_);
lean_inc(v_binDir_1122_);
lean_inc(v_nativeLibDir_1121_);
lean_inc(v_leanLibDir_1120_);
lean_inc(v_buildDir_1119_);
lean_inc(v_srcDir_1118_);
lean_inc(v_moreGlobalServerArgs_1117_);
lean_inc(v_extraDepTargets_1115_);
lean_inc(v_toLeanConfig_1113_);
lean_inc(v_toWorkspaceConfig_1112_);
lean_dec(v_cfg_1111_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 9, v_val_1110_);
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_toWorkspaceConfig_1112_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_toLeanConfig_1113_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_extraDepTargets_1115_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_moreGlobalServerArgs_1117_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_srcDir_1118_);
lean_ctor_set(v_reuseFailAlloc_1149_, 5, v_buildDir_1119_);
lean_ctor_set(v_reuseFailAlloc_1149_, 6, v_leanLibDir_1120_);
lean_ctor_set(v_reuseFailAlloc_1149_, 7, v_nativeLibDir_1121_);
lean_ctor_set(v_reuseFailAlloc_1149_, 8, v_binDir_1122_);
lean_ctor_set(v_reuseFailAlloc_1149_, 9, v_val_1110_);
lean_ctor_set(v_reuseFailAlloc_1149_, 10, v_releaseRepo_1123_);
lean_ctor_set(v_reuseFailAlloc_1149_, 11, v_buildArchive_1124_);
lean_ctor_set(v_reuseFailAlloc_1149_, 12, v_testDriver_1126_);
lean_ctor_set(v_reuseFailAlloc_1149_, 13, v_testDriverArgs_1127_);
lean_ctor_set(v_reuseFailAlloc_1149_, 14, v_lintDriver_1128_);
lean_ctor_set(v_reuseFailAlloc_1149_, 15, v_lintDriverArgs_1129_);
lean_ctor_set(v_reuseFailAlloc_1149_, 16, v_version_1130_);
lean_ctor_set(v_reuseFailAlloc_1149_, 17, v_versionTags_1131_);
lean_ctor_set(v_reuseFailAlloc_1149_, 18, v_description_1132_);
lean_ctor_set(v_reuseFailAlloc_1149_, 19, v_keywords_1133_);
lean_ctor_set(v_reuseFailAlloc_1149_, 20, v_homepage_1134_);
lean_ctor_set(v_reuseFailAlloc_1149_, 21, v_license_1135_);
lean_ctor_set(v_reuseFailAlloc_1149_, 22, v_licenseFiles_1136_);
lean_ctor_set(v_reuseFailAlloc_1149_, 23, v_readmeFile_1137_);
lean_ctor_set(v_reuseFailAlloc_1149_, 24, v_enableArtifactCache_x3f_1139_);
lean_ctor_set(v_reuseFailAlloc_1149_, 25, v_restoreAllArtifacts_x3f_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*26, v_bootstrap_1114_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*26 + 1, v_precompileModules_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*26 + 3, v_reservoir_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*26 + 5, v_allowImportAll_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*26 + 6, v_fixedToolchain_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__2(lean_object* v_f_1152_, lean_object* v_cfg_1153_){
_start:
{
lean_object* v_toWorkspaceConfig_1154_; lean_object* v_toLeanConfig_1155_; uint8_t v_bootstrap_1156_; lean_object* v_extraDepTargets_1157_; uint8_t v_precompileModules_1158_; lean_object* v_moreGlobalServerArgs_1159_; lean_object* v_srcDir_1160_; lean_object* v_buildDir_1161_; lean_object* v_leanLibDir_1162_; lean_object* v_nativeLibDir_1163_; lean_object* v_binDir_1164_; lean_object* v_irDir_1165_; lean_object* v_releaseRepo_1166_; lean_object* v_buildArchive_1167_; uint8_t v_preferReleaseBuild_1168_; lean_object* v_testDriver_1169_; lean_object* v_testDriverArgs_1170_; lean_object* v_lintDriver_1171_; lean_object* v_lintDriverArgs_1172_; lean_object* v_version_1173_; lean_object* v_versionTags_1174_; lean_object* v_description_1175_; lean_object* v_keywords_1176_; lean_object* v_homepage_1177_; lean_object* v_license_1178_; lean_object* v_licenseFiles_1179_; lean_object* v_readmeFile_1180_; uint8_t v_reservoir_1181_; lean_object* v_enableArtifactCache_x3f_1182_; lean_object* v_restoreAllArtifacts_x3f_1183_; uint8_t v_libPrefixOnWindows_1184_; uint8_t v_allowImportAll_1185_; uint8_t v_fixedToolchain_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
v_toWorkspaceConfig_1154_ = lean_ctor_get(v_cfg_1153_, 0);
v_toLeanConfig_1155_ = lean_ctor_get(v_cfg_1153_, 1);
v_bootstrap_1156_ = lean_ctor_get_uint8(v_cfg_1153_, sizeof(void*)*26);
v_extraDepTargets_1157_ = lean_ctor_get(v_cfg_1153_, 2);
v_precompileModules_1158_ = lean_ctor_get_uint8(v_cfg_1153_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1159_ = lean_ctor_get(v_cfg_1153_, 3);
v_srcDir_1160_ = lean_ctor_get(v_cfg_1153_, 4);
v_buildDir_1161_ = lean_ctor_get(v_cfg_1153_, 5);
v_leanLibDir_1162_ = lean_ctor_get(v_cfg_1153_, 6);
v_nativeLibDir_1163_ = lean_ctor_get(v_cfg_1153_, 7);
v_binDir_1164_ = lean_ctor_get(v_cfg_1153_, 8);
v_irDir_1165_ = lean_ctor_get(v_cfg_1153_, 9);
v_releaseRepo_1166_ = lean_ctor_get(v_cfg_1153_, 10);
v_buildArchive_1167_ = lean_ctor_get(v_cfg_1153_, 11);
v_preferReleaseBuild_1168_ = lean_ctor_get_uint8(v_cfg_1153_, sizeof(void*)*26 + 2);
v_testDriver_1169_ = lean_ctor_get(v_cfg_1153_, 12);
v_testDriverArgs_1170_ = lean_ctor_get(v_cfg_1153_, 13);
v_lintDriver_1171_ = lean_ctor_get(v_cfg_1153_, 14);
v_lintDriverArgs_1172_ = lean_ctor_get(v_cfg_1153_, 15);
v_version_1173_ = lean_ctor_get(v_cfg_1153_, 16);
v_versionTags_1174_ = lean_ctor_get(v_cfg_1153_, 17);
v_description_1175_ = lean_ctor_get(v_cfg_1153_, 18);
v_keywords_1176_ = lean_ctor_get(v_cfg_1153_, 19);
v_homepage_1177_ = lean_ctor_get(v_cfg_1153_, 20);
v_license_1178_ = lean_ctor_get(v_cfg_1153_, 21);
v_licenseFiles_1179_ = lean_ctor_get(v_cfg_1153_, 22);
v_readmeFile_1180_ = lean_ctor_get(v_cfg_1153_, 23);
v_reservoir_1181_ = lean_ctor_get_uint8(v_cfg_1153_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1182_ = lean_ctor_get(v_cfg_1153_, 24);
v_restoreAllArtifacts_x3f_1183_ = lean_ctor_get(v_cfg_1153_, 25);
v_libPrefixOnWindows_1184_ = lean_ctor_get_uint8(v_cfg_1153_, sizeof(void*)*26 + 4);
v_allowImportAll_1185_ = lean_ctor_get_uint8(v_cfg_1153_, sizeof(void*)*26 + 5);
v_fixedToolchain_1186_ = lean_ctor_get_uint8(v_cfg_1153_, sizeof(void*)*26 + 6);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_cfg_1153_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1188_ = v_cfg_1153_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1183_);
lean_inc(v_enableArtifactCache_x3f_1182_);
lean_inc(v_readmeFile_1180_);
lean_inc(v_licenseFiles_1179_);
lean_inc(v_license_1178_);
lean_inc(v_homepage_1177_);
lean_inc(v_keywords_1176_);
lean_inc(v_description_1175_);
lean_inc(v_versionTags_1174_);
lean_inc(v_version_1173_);
lean_inc(v_lintDriverArgs_1172_);
lean_inc(v_lintDriver_1171_);
lean_inc(v_testDriverArgs_1170_);
lean_inc(v_testDriver_1169_);
lean_inc(v_buildArchive_1167_);
lean_inc(v_releaseRepo_1166_);
lean_inc(v_irDir_1165_);
lean_inc(v_binDir_1164_);
lean_inc(v_nativeLibDir_1163_);
lean_inc(v_leanLibDir_1162_);
lean_inc(v_buildDir_1161_);
lean_inc(v_srcDir_1160_);
lean_inc(v_moreGlobalServerArgs_1159_);
lean_inc(v_extraDepTargets_1157_);
lean_inc(v_toLeanConfig_1155_);
lean_inc(v_toWorkspaceConfig_1154_);
lean_dec(v_cfg_1153_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_apply_1(v_f_1152_, v_irDir_1165_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 9, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_toWorkspaceConfig_1154_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_toLeanConfig_1155_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_extraDepTargets_1157_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_moreGlobalServerArgs_1159_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_srcDir_1160_);
lean_ctor_set(v_reuseFailAlloc_1193_, 5, v_buildDir_1161_);
lean_ctor_set(v_reuseFailAlloc_1193_, 6, v_leanLibDir_1162_);
lean_ctor_set(v_reuseFailAlloc_1193_, 7, v_nativeLibDir_1163_);
lean_ctor_set(v_reuseFailAlloc_1193_, 8, v_binDir_1164_);
lean_ctor_set(v_reuseFailAlloc_1193_, 9, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1193_, 10, v_releaseRepo_1166_);
lean_ctor_set(v_reuseFailAlloc_1193_, 11, v_buildArchive_1167_);
lean_ctor_set(v_reuseFailAlloc_1193_, 12, v_testDriver_1169_);
lean_ctor_set(v_reuseFailAlloc_1193_, 13, v_testDriverArgs_1170_);
lean_ctor_set(v_reuseFailAlloc_1193_, 14, v_lintDriver_1171_);
lean_ctor_set(v_reuseFailAlloc_1193_, 15, v_lintDriverArgs_1172_);
lean_ctor_set(v_reuseFailAlloc_1193_, 16, v_version_1173_);
lean_ctor_set(v_reuseFailAlloc_1193_, 17, v_versionTags_1174_);
lean_ctor_set(v_reuseFailAlloc_1193_, 18, v_description_1175_);
lean_ctor_set(v_reuseFailAlloc_1193_, 19, v_keywords_1176_);
lean_ctor_set(v_reuseFailAlloc_1193_, 20, v_homepage_1177_);
lean_ctor_set(v_reuseFailAlloc_1193_, 21, v_license_1178_);
lean_ctor_set(v_reuseFailAlloc_1193_, 22, v_licenseFiles_1179_);
lean_ctor_set(v_reuseFailAlloc_1193_, 23, v_readmeFile_1180_);
lean_ctor_set(v_reuseFailAlloc_1193_, 24, v_enableArtifactCache_x3f_1182_);
lean_ctor_set(v_reuseFailAlloc_1193_, 25, v_restoreAllArtifacts_x3f_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*26, v_bootstrap_1156_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*26 + 1, v_precompileModules_1158_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1168_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*26 + 3, v_reservoir_1181_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*26 + 5, v_allowImportAll_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*26 + 6, v_fixedToolchain_1186_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3(lean_object* v_x_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lake_defaultIrDir;
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3___boxed(lean_object* v_x_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lake_PackageConfig_irDir___proj___lam__3(v_x_1197_);
lean_dec_ref(v_x_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object* v_p_1208_, lean_object* v_n_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = ((lean_object*)(l_Lake_PackageConfig_irDir___proj___closed__4));
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object* v_p_1211_, lean_object* v_n_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lake_PackageConfig_irDir___proj(v_p_1211_, v_n_1212_);
lean_dec(v_n_1212_);
lean_dec(v_p_1211_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object* v_p_1214_, lean_object* v_n_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lake_PackageConfig_irDir___proj(v_p_1214_, v_n_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object* v_p_1217_, lean_object* v_n_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lake_PackageConfig_irDir_instConfigField(v_p_1217_, v_n_1218_);
lean_dec(v_n_1218_);
lean_dec(v_p_1217_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0(lean_object* v_cfg_1220_){
_start:
{
lean_object* v_releaseRepo_1221_; 
v_releaseRepo_1221_ = lean_ctor_get(v_cfg_1220_, 10);
lean_inc(v_releaseRepo_1221_);
return v_releaseRepo_1221_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0___boxed(lean_object* v_cfg_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lake_PackageConfig_releaseRepo___proj___lam__0(v_cfg_1222_);
lean_dec_ref(v_cfg_1222_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__1(lean_object* v_val_1224_, lean_object* v_cfg_1225_){
_start:
{
lean_object* v_toWorkspaceConfig_1226_; lean_object* v_toLeanConfig_1227_; uint8_t v_bootstrap_1228_; lean_object* v_extraDepTargets_1229_; uint8_t v_precompileModules_1230_; lean_object* v_moreGlobalServerArgs_1231_; lean_object* v_srcDir_1232_; lean_object* v_buildDir_1233_; lean_object* v_leanLibDir_1234_; lean_object* v_nativeLibDir_1235_; lean_object* v_binDir_1236_; lean_object* v_irDir_1237_; lean_object* v_buildArchive_1238_; uint8_t v_preferReleaseBuild_1239_; lean_object* v_testDriver_1240_; lean_object* v_testDriverArgs_1241_; lean_object* v_lintDriver_1242_; lean_object* v_lintDriverArgs_1243_; lean_object* v_version_1244_; lean_object* v_versionTags_1245_; lean_object* v_description_1246_; lean_object* v_keywords_1247_; lean_object* v_homepage_1248_; lean_object* v_license_1249_; lean_object* v_licenseFiles_1250_; lean_object* v_readmeFile_1251_; uint8_t v_reservoir_1252_; lean_object* v_enableArtifactCache_x3f_1253_; lean_object* v_restoreAllArtifacts_x3f_1254_; uint8_t v_libPrefixOnWindows_1255_; uint8_t v_allowImportAll_1256_; uint8_t v_fixedToolchain_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_toWorkspaceConfig_1226_ = lean_ctor_get(v_cfg_1225_, 0);
v_toLeanConfig_1227_ = lean_ctor_get(v_cfg_1225_, 1);
v_bootstrap_1228_ = lean_ctor_get_uint8(v_cfg_1225_, sizeof(void*)*26);
v_extraDepTargets_1229_ = lean_ctor_get(v_cfg_1225_, 2);
v_precompileModules_1230_ = lean_ctor_get_uint8(v_cfg_1225_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1231_ = lean_ctor_get(v_cfg_1225_, 3);
v_srcDir_1232_ = lean_ctor_get(v_cfg_1225_, 4);
v_buildDir_1233_ = lean_ctor_get(v_cfg_1225_, 5);
v_leanLibDir_1234_ = lean_ctor_get(v_cfg_1225_, 6);
v_nativeLibDir_1235_ = lean_ctor_get(v_cfg_1225_, 7);
v_binDir_1236_ = lean_ctor_get(v_cfg_1225_, 8);
v_irDir_1237_ = lean_ctor_get(v_cfg_1225_, 9);
v_buildArchive_1238_ = lean_ctor_get(v_cfg_1225_, 11);
v_preferReleaseBuild_1239_ = lean_ctor_get_uint8(v_cfg_1225_, sizeof(void*)*26 + 2);
v_testDriver_1240_ = lean_ctor_get(v_cfg_1225_, 12);
v_testDriverArgs_1241_ = lean_ctor_get(v_cfg_1225_, 13);
v_lintDriver_1242_ = lean_ctor_get(v_cfg_1225_, 14);
v_lintDriverArgs_1243_ = lean_ctor_get(v_cfg_1225_, 15);
v_version_1244_ = lean_ctor_get(v_cfg_1225_, 16);
v_versionTags_1245_ = lean_ctor_get(v_cfg_1225_, 17);
v_description_1246_ = lean_ctor_get(v_cfg_1225_, 18);
v_keywords_1247_ = lean_ctor_get(v_cfg_1225_, 19);
v_homepage_1248_ = lean_ctor_get(v_cfg_1225_, 20);
v_license_1249_ = lean_ctor_get(v_cfg_1225_, 21);
v_licenseFiles_1250_ = lean_ctor_get(v_cfg_1225_, 22);
v_readmeFile_1251_ = lean_ctor_get(v_cfg_1225_, 23);
v_reservoir_1252_ = lean_ctor_get_uint8(v_cfg_1225_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1253_ = lean_ctor_get(v_cfg_1225_, 24);
v_restoreAllArtifacts_x3f_1254_ = lean_ctor_get(v_cfg_1225_, 25);
v_libPrefixOnWindows_1255_ = lean_ctor_get_uint8(v_cfg_1225_, sizeof(void*)*26 + 4);
v_allowImportAll_1256_ = lean_ctor_get_uint8(v_cfg_1225_, sizeof(void*)*26 + 5);
v_fixedToolchain_1257_ = lean_ctor_get_uint8(v_cfg_1225_, sizeof(void*)*26 + 6);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_cfg_1225_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v_cfg_1225_, 10);
lean_dec(v_unused_1265_);
v___x_1259_ = v_cfg_1225_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1254_);
lean_inc(v_enableArtifactCache_x3f_1253_);
lean_inc(v_readmeFile_1251_);
lean_inc(v_licenseFiles_1250_);
lean_inc(v_license_1249_);
lean_inc(v_homepage_1248_);
lean_inc(v_keywords_1247_);
lean_inc(v_description_1246_);
lean_inc(v_versionTags_1245_);
lean_inc(v_version_1244_);
lean_inc(v_lintDriverArgs_1243_);
lean_inc(v_lintDriver_1242_);
lean_inc(v_testDriverArgs_1241_);
lean_inc(v_testDriver_1240_);
lean_inc(v_buildArchive_1238_);
lean_inc(v_irDir_1237_);
lean_inc(v_binDir_1236_);
lean_inc(v_nativeLibDir_1235_);
lean_inc(v_leanLibDir_1234_);
lean_inc(v_buildDir_1233_);
lean_inc(v_srcDir_1232_);
lean_inc(v_moreGlobalServerArgs_1231_);
lean_inc(v_extraDepTargets_1229_);
lean_inc(v_toLeanConfig_1227_);
lean_inc(v_toWorkspaceConfig_1226_);
lean_dec(v_cfg_1225_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 10, v_val_1224_);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_toWorkspaceConfig_1226_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_toLeanConfig_1227_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_extraDepTargets_1229_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_moreGlobalServerArgs_1231_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_srcDir_1232_);
lean_ctor_set(v_reuseFailAlloc_1263_, 5, v_buildDir_1233_);
lean_ctor_set(v_reuseFailAlloc_1263_, 6, v_leanLibDir_1234_);
lean_ctor_set(v_reuseFailAlloc_1263_, 7, v_nativeLibDir_1235_);
lean_ctor_set(v_reuseFailAlloc_1263_, 8, v_binDir_1236_);
lean_ctor_set(v_reuseFailAlloc_1263_, 9, v_irDir_1237_);
lean_ctor_set(v_reuseFailAlloc_1263_, 10, v_val_1224_);
lean_ctor_set(v_reuseFailAlloc_1263_, 11, v_buildArchive_1238_);
lean_ctor_set(v_reuseFailAlloc_1263_, 12, v_testDriver_1240_);
lean_ctor_set(v_reuseFailAlloc_1263_, 13, v_testDriverArgs_1241_);
lean_ctor_set(v_reuseFailAlloc_1263_, 14, v_lintDriver_1242_);
lean_ctor_set(v_reuseFailAlloc_1263_, 15, v_lintDriverArgs_1243_);
lean_ctor_set(v_reuseFailAlloc_1263_, 16, v_version_1244_);
lean_ctor_set(v_reuseFailAlloc_1263_, 17, v_versionTags_1245_);
lean_ctor_set(v_reuseFailAlloc_1263_, 18, v_description_1246_);
lean_ctor_set(v_reuseFailAlloc_1263_, 19, v_keywords_1247_);
lean_ctor_set(v_reuseFailAlloc_1263_, 20, v_homepage_1248_);
lean_ctor_set(v_reuseFailAlloc_1263_, 21, v_license_1249_);
lean_ctor_set(v_reuseFailAlloc_1263_, 22, v_licenseFiles_1250_);
lean_ctor_set(v_reuseFailAlloc_1263_, 23, v_readmeFile_1251_);
lean_ctor_set(v_reuseFailAlloc_1263_, 24, v_enableArtifactCache_x3f_1253_);
lean_ctor_set(v_reuseFailAlloc_1263_, 25, v_restoreAllArtifacts_x3f_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*26, v_bootstrap_1228_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*26 + 1, v_precompileModules_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*26 + 3, v_reservoir_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*26 + 5, v_allowImportAll_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*26 + 6, v_fixedToolchain_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__2(lean_object* v_f_1266_, lean_object* v_cfg_1267_){
_start:
{
lean_object* v_toWorkspaceConfig_1268_; lean_object* v_toLeanConfig_1269_; uint8_t v_bootstrap_1270_; lean_object* v_extraDepTargets_1271_; uint8_t v_precompileModules_1272_; lean_object* v_moreGlobalServerArgs_1273_; lean_object* v_srcDir_1274_; lean_object* v_buildDir_1275_; lean_object* v_leanLibDir_1276_; lean_object* v_nativeLibDir_1277_; lean_object* v_binDir_1278_; lean_object* v_irDir_1279_; lean_object* v_releaseRepo_1280_; lean_object* v_buildArchive_1281_; uint8_t v_preferReleaseBuild_1282_; lean_object* v_testDriver_1283_; lean_object* v_testDriverArgs_1284_; lean_object* v_lintDriver_1285_; lean_object* v_lintDriverArgs_1286_; lean_object* v_version_1287_; lean_object* v_versionTags_1288_; lean_object* v_description_1289_; lean_object* v_keywords_1290_; lean_object* v_homepage_1291_; lean_object* v_license_1292_; lean_object* v_licenseFiles_1293_; lean_object* v_readmeFile_1294_; uint8_t v_reservoir_1295_; lean_object* v_enableArtifactCache_x3f_1296_; lean_object* v_restoreAllArtifacts_x3f_1297_; uint8_t v_libPrefixOnWindows_1298_; uint8_t v_allowImportAll_1299_; uint8_t v_fixedToolchain_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1308_; 
v_toWorkspaceConfig_1268_ = lean_ctor_get(v_cfg_1267_, 0);
v_toLeanConfig_1269_ = lean_ctor_get(v_cfg_1267_, 1);
v_bootstrap_1270_ = lean_ctor_get_uint8(v_cfg_1267_, sizeof(void*)*26);
v_extraDepTargets_1271_ = lean_ctor_get(v_cfg_1267_, 2);
v_precompileModules_1272_ = lean_ctor_get_uint8(v_cfg_1267_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1273_ = lean_ctor_get(v_cfg_1267_, 3);
v_srcDir_1274_ = lean_ctor_get(v_cfg_1267_, 4);
v_buildDir_1275_ = lean_ctor_get(v_cfg_1267_, 5);
v_leanLibDir_1276_ = lean_ctor_get(v_cfg_1267_, 6);
v_nativeLibDir_1277_ = lean_ctor_get(v_cfg_1267_, 7);
v_binDir_1278_ = lean_ctor_get(v_cfg_1267_, 8);
v_irDir_1279_ = lean_ctor_get(v_cfg_1267_, 9);
v_releaseRepo_1280_ = lean_ctor_get(v_cfg_1267_, 10);
v_buildArchive_1281_ = lean_ctor_get(v_cfg_1267_, 11);
v_preferReleaseBuild_1282_ = lean_ctor_get_uint8(v_cfg_1267_, sizeof(void*)*26 + 2);
v_testDriver_1283_ = lean_ctor_get(v_cfg_1267_, 12);
v_testDriverArgs_1284_ = lean_ctor_get(v_cfg_1267_, 13);
v_lintDriver_1285_ = lean_ctor_get(v_cfg_1267_, 14);
v_lintDriverArgs_1286_ = lean_ctor_get(v_cfg_1267_, 15);
v_version_1287_ = lean_ctor_get(v_cfg_1267_, 16);
v_versionTags_1288_ = lean_ctor_get(v_cfg_1267_, 17);
v_description_1289_ = lean_ctor_get(v_cfg_1267_, 18);
v_keywords_1290_ = lean_ctor_get(v_cfg_1267_, 19);
v_homepage_1291_ = lean_ctor_get(v_cfg_1267_, 20);
v_license_1292_ = lean_ctor_get(v_cfg_1267_, 21);
v_licenseFiles_1293_ = lean_ctor_get(v_cfg_1267_, 22);
v_readmeFile_1294_ = lean_ctor_get(v_cfg_1267_, 23);
v_reservoir_1295_ = lean_ctor_get_uint8(v_cfg_1267_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1296_ = lean_ctor_get(v_cfg_1267_, 24);
v_restoreAllArtifacts_x3f_1297_ = lean_ctor_get(v_cfg_1267_, 25);
v_libPrefixOnWindows_1298_ = lean_ctor_get_uint8(v_cfg_1267_, sizeof(void*)*26 + 4);
v_allowImportAll_1299_ = lean_ctor_get_uint8(v_cfg_1267_, sizeof(void*)*26 + 5);
v_fixedToolchain_1300_ = lean_ctor_get_uint8(v_cfg_1267_, sizeof(void*)*26 + 6);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_cfg_1267_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1302_ = v_cfg_1267_;
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1297_);
lean_inc(v_enableArtifactCache_x3f_1296_);
lean_inc(v_readmeFile_1294_);
lean_inc(v_licenseFiles_1293_);
lean_inc(v_license_1292_);
lean_inc(v_homepage_1291_);
lean_inc(v_keywords_1290_);
lean_inc(v_description_1289_);
lean_inc(v_versionTags_1288_);
lean_inc(v_version_1287_);
lean_inc(v_lintDriverArgs_1286_);
lean_inc(v_lintDriver_1285_);
lean_inc(v_testDriverArgs_1284_);
lean_inc(v_testDriver_1283_);
lean_inc(v_buildArchive_1281_);
lean_inc(v_releaseRepo_1280_);
lean_inc(v_irDir_1279_);
lean_inc(v_binDir_1278_);
lean_inc(v_nativeLibDir_1277_);
lean_inc(v_leanLibDir_1276_);
lean_inc(v_buildDir_1275_);
lean_inc(v_srcDir_1274_);
lean_inc(v_moreGlobalServerArgs_1273_);
lean_inc(v_extraDepTargets_1271_);
lean_inc(v_toLeanConfig_1269_);
lean_inc(v_toWorkspaceConfig_1268_);
lean_dec(v_cfg_1267_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_apply_1(v_f_1266_, v_releaseRepo_1280_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 10, v___x_1304_);
v___x_1306_ = v___x_1302_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_toWorkspaceConfig_1268_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_toLeanConfig_1269_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_extraDepTargets_1271_);
lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_moreGlobalServerArgs_1273_);
lean_ctor_set(v_reuseFailAlloc_1307_, 4, v_srcDir_1274_);
lean_ctor_set(v_reuseFailAlloc_1307_, 5, v_buildDir_1275_);
lean_ctor_set(v_reuseFailAlloc_1307_, 6, v_leanLibDir_1276_);
lean_ctor_set(v_reuseFailAlloc_1307_, 7, v_nativeLibDir_1277_);
lean_ctor_set(v_reuseFailAlloc_1307_, 8, v_binDir_1278_);
lean_ctor_set(v_reuseFailAlloc_1307_, 9, v_irDir_1279_);
lean_ctor_set(v_reuseFailAlloc_1307_, 10, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1307_, 11, v_buildArchive_1281_);
lean_ctor_set(v_reuseFailAlloc_1307_, 12, v_testDriver_1283_);
lean_ctor_set(v_reuseFailAlloc_1307_, 13, v_testDriverArgs_1284_);
lean_ctor_set(v_reuseFailAlloc_1307_, 14, v_lintDriver_1285_);
lean_ctor_set(v_reuseFailAlloc_1307_, 15, v_lintDriverArgs_1286_);
lean_ctor_set(v_reuseFailAlloc_1307_, 16, v_version_1287_);
lean_ctor_set(v_reuseFailAlloc_1307_, 17, v_versionTags_1288_);
lean_ctor_set(v_reuseFailAlloc_1307_, 18, v_description_1289_);
lean_ctor_set(v_reuseFailAlloc_1307_, 19, v_keywords_1290_);
lean_ctor_set(v_reuseFailAlloc_1307_, 20, v_homepage_1291_);
lean_ctor_set(v_reuseFailAlloc_1307_, 21, v_license_1292_);
lean_ctor_set(v_reuseFailAlloc_1307_, 22, v_licenseFiles_1293_);
lean_ctor_set(v_reuseFailAlloc_1307_, 23, v_readmeFile_1294_);
lean_ctor_set(v_reuseFailAlloc_1307_, 24, v_enableArtifactCache_x3f_1296_);
lean_ctor_set(v_reuseFailAlloc_1307_, 25, v_restoreAllArtifacts_x3f_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*26, v_bootstrap_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*26 + 1, v_precompileModules_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1282_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*26 + 3, v_reservoir_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*26 + 5, v_allowImportAll_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*26 + 6, v_fixedToolchain_1300_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3(lean_object* v_x_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_box(0);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3___boxed(lean_object* v_x_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lake_PackageConfig_releaseRepo___proj___lam__3(v_x_1311_);
lean_dec_ref(v_x_1311_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object* v_p_1322_, lean_object* v_n_1323_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = ((lean_object*)(l_Lake_PackageConfig_releaseRepo___proj___closed__4));
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object* v_p_1325_, lean_object* v_n_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1325_, v_n_1326_);
lean_dec(v_n_1326_);
lean_dec(v_p_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object* v_p_1328_, lean_object* v_n_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1328_, v_n_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object* v_p_1331_, lean_object* v_n_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lake_PackageConfig_releaseRepo_instConfigField(v_p_1331_, v_n_1332_);
lean_dec(v_n_1332_);
lean_dec(v_p_1331_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object* v_p_1334_, lean_object* v_n_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1334_, v_n_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object* v_p_1337_, lean_object* v_n_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(v_p_1337_, v_n_1338_);
lean_dec(v_n_1338_);
lean_dec(v_p_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0(lean_object* v_cfg_1340_){
_start:
{
lean_object* v_buildArchive_1341_; 
v_buildArchive_1341_ = lean_ctor_get(v_cfg_1340_, 11);
lean_inc(v_buildArchive_1341_);
return v_buildArchive_1341_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0___boxed(lean_object* v_cfg_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lake_PackageConfig_buildArchive___proj___lam__0(v_cfg_1342_);
lean_dec_ref(v_cfg_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__1(lean_object* v_val_1344_, lean_object* v_cfg_1345_){
_start:
{
lean_object* v_toWorkspaceConfig_1346_; lean_object* v_toLeanConfig_1347_; uint8_t v_bootstrap_1348_; lean_object* v_extraDepTargets_1349_; uint8_t v_precompileModules_1350_; lean_object* v_moreGlobalServerArgs_1351_; lean_object* v_srcDir_1352_; lean_object* v_buildDir_1353_; lean_object* v_leanLibDir_1354_; lean_object* v_nativeLibDir_1355_; lean_object* v_binDir_1356_; lean_object* v_irDir_1357_; lean_object* v_releaseRepo_1358_; uint8_t v_preferReleaseBuild_1359_; lean_object* v_testDriver_1360_; lean_object* v_testDriverArgs_1361_; lean_object* v_lintDriver_1362_; lean_object* v_lintDriverArgs_1363_; lean_object* v_version_1364_; lean_object* v_versionTags_1365_; lean_object* v_description_1366_; lean_object* v_keywords_1367_; lean_object* v_homepage_1368_; lean_object* v_license_1369_; lean_object* v_licenseFiles_1370_; lean_object* v_readmeFile_1371_; uint8_t v_reservoir_1372_; lean_object* v_enableArtifactCache_x3f_1373_; lean_object* v_restoreAllArtifacts_x3f_1374_; uint8_t v_libPrefixOnWindows_1375_; uint8_t v_allowImportAll_1376_; uint8_t v_fixedToolchain_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
v_toWorkspaceConfig_1346_ = lean_ctor_get(v_cfg_1345_, 0);
v_toLeanConfig_1347_ = lean_ctor_get(v_cfg_1345_, 1);
v_bootstrap_1348_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*26);
v_extraDepTargets_1349_ = lean_ctor_get(v_cfg_1345_, 2);
v_precompileModules_1350_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1351_ = lean_ctor_get(v_cfg_1345_, 3);
v_srcDir_1352_ = lean_ctor_get(v_cfg_1345_, 4);
v_buildDir_1353_ = lean_ctor_get(v_cfg_1345_, 5);
v_leanLibDir_1354_ = lean_ctor_get(v_cfg_1345_, 6);
v_nativeLibDir_1355_ = lean_ctor_get(v_cfg_1345_, 7);
v_binDir_1356_ = lean_ctor_get(v_cfg_1345_, 8);
v_irDir_1357_ = lean_ctor_get(v_cfg_1345_, 9);
v_releaseRepo_1358_ = lean_ctor_get(v_cfg_1345_, 10);
v_preferReleaseBuild_1359_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*26 + 2);
v_testDriver_1360_ = lean_ctor_get(v_cfg_1345_, 12);
v_testDriverArgs_1361_ = lean_ctor_get(v_cfg_1345_, 13);
v_lintDriver_1362_ = lean_ctor_get(v_cfg_1345_, 14);
v_lintDriverArgs_1363_ = lean_ctor_get(v_cfg_1345_, 15);
v_version_1364_ = lean_ctor_get(v_cfg_1345_, 16);
v_versionTags_1365_ = lean_ctor_get(v_cfg_1345_, 17);
v_description_1366_ = lean_ctor_get(v_cfg_1345_, 18);
v_keywords_1367_ = lean_ctor_get(v_cfg_1345_, 19);
v_homepage_1368_ = lean_ctor_get(v_cfg_1345_, 20);
v_license_1369_ = lean_ctor_get(v_cfg_1345_, 21);
v_licenseFiles_1370_ = lean_ctor_get(v_cfg_1345_, 22);
v_readmeFile_1371_ = lean_ctor_get(v_cfg_1345_, 23);
v_reservoir_1372_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1373_ = lean_ctor_get(v_cfg_1345_, 24);
v_restoreAllArtifacts_x3f_1374_ = lean_ctor_get(v_cfg_1345_, 25);
v_libPrefixOnWindows_1375_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*26 + 4);
v_allowImportAll_1376_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*26 + 5);
v_fixedToolchain_1377_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*26 + 6);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_cfg_1345_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; 
v_unused_1385_ = lean_ctor_get(v_cfg_1345_, 11);
lean_dec(v_unused_1385_);
v___x_1379_ = v_cfg_1345_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1374_);
lean_inc(v_enableArtifactCache_x3f_1373_);
lean_inc(v_readmeFile_1371_);
lean_inc(v_licenseFiles_1370_);
lean_inc(v_license_1369_);
lean_inc(v_homepage_1368_);
lean_inc(v_keywords_1367_);
lean_inc(v_description_1366_);
lean_inc(v_versionTags_1365_);
lean_inc(v_version_1364_);
lean_inc(v_lintDriverArgs_1363_);
lean_inc(v_lintDriver_1362_);
lean_inc(v_testDriverArgs_1361_);
lean_inc(v_testDriver_1360_);
lean_inc(v_releaseRepo_1358_);
lean_inc(v_irDir_1357_);
lean_inc(v_binDir_1356_);
lean_inc(v_nativeLibDir_1355_);
lean_inc(v_leanLibDir_1354_);
lean_inc(v_buildDir_1353_);
lean_inc(v_srcDir_1352_);
lean_inc(v_moreGlobalServerArgs_1351_);
lean_inc(v_extraDepTargets_1349_);
lean_inc(v_toLeanConfig_1347_);
lean_inc(v_toWorkspaceConfig_1346_);
lean_dec(v_cfg_1345_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 11, v_val_1344_);
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_toWorkspaceConfig_1346_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_toLeanConfig_1347_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_extraDepTargets_1349_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v_moreGlobalServerArgs_1351_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v_srcDir_1352_);
lean_ctor_set(v_reuseFailAlloc_1383_, 5, v_buildDir_1353_);
lean_ctor_set(v_reuseFailAlloc_1383_, 6, v_leanLibDir_1354_);
lean_ctor_set(v_reuseFailAlloc_1383_, 7, v_nativeLibDir_1355_);
lean_ctor_set(v_reuseFailAlloc_1383_, 8, v_binDir_1356_);
lean_ctor_set(v_reuseFailAlloc_1383_, 9, v_irDir_1357_);
lean_ctor_set(v_reuseFailAlloc_1383_, 10, v_releaseRepo_1358_);
lean_ctor_set(v_reuseFailAlloc_1383_, 11, v_val_1344_);
lean_ctor_set(v_reuseFailAlloc_1383_, 12, v_testDriver_1360_);
lean_ctor_set(v_reuseFailAlloc_1383_, 13, v_testDriverArgs_1361_);
lean_ctor_set(v_reuseFailAlloc_1383_, 14, v_lintDriver_1362_);
lean_ctor_set(v_reuseFailAlloc_1383_, 15, v_lintDriverArgs_1363_);
lean_ctor_set(v_reuseFailAlloc_1383_, 16, v_version_1364_);
lean_ctor_set(v_reuseFailAlloc_1383_, 17, v_versionTags_1365_);
lean_ctor_set(v_reuseFailAlloc_1383_, 18, v_description_1366_);
lean_ctor_set(v_reuseFailAlloc_1383_, 19, v_keywords_1367_);
lean_ctor_set(v_reuseFailAlloc_1383_, 20, v_homepage_1368_);
lean_ctor_set(v_reuseFailAlloc_1383_, 21, v_license_1369_);
lean_ctor_set(v_reuseFailAlloc_1383_, 22, v_licenseFiles_1370_);
lean_ctor_set(v_reuseFailAlloc_1383_, 23, v_readmeFile_1371_);
lean_ctor_set(v_reuseFailAlloc_1383_, 24, v_enableArtifactCache_x3f_1373_);
lean_ctor_set(v_reuseFailAlloc_1383_, 25, v_restoreAllArtifacts_x3f_1374_);
lean_ctor_set_uint8(v_reuseFailAlloc_1383_, sizeof(void*)*26, v_bootstrap_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1383_, sizeof(void*)*26 + 1, v_precompileModules_1350_);
lean_ctor_set_uint8(v_reuseFailAlloc_1383_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1383_, sizeof(void*)*26 + 3, v_reservoir_1372_);
lean_ctor_set_uint8(v_reuseFailAlloc_1383_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1375_);
lean_ctor_set_uint8(v_reuseFailAlloc_1383_, sizeof(void*)*26 + 5, v_allowImportAll_1376_);
lean_ctor_set_uint8(v_reuseFailAlloc_1383_, sizeof(void*)*26 + 6, v_fixedToolchain_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__2(lean_object* v_f_1386_, lean_object* v_cfg_1387_){
_start:
{
lean_object* v_toWorkspaceConfig_1388_; lean_object* v_toLeanConfig_1389_; uint8_t v_bootstrap_1390_; lean_object* v_extraDepTargets_1391_; uint8_t v_precompileModules_1392_; lean_object* v_moreGlobalServerArgs_1393_; lean_object* v_srcDir_1394_; lean_object* v_buildDir_1395_; lean_object* v_leanLibDir_1396_; lean_object* v_nativeLibDir_1397_; lean_object* v_binDir_1398_; lean_object* v_irDir_1399_; lean_object* v_releaseRepo_1400_; lean_object* v_buildArchive_1401_; uint8_t v_preferReleaseBuild_1402_; lean_object* v_testDriver_1403_; lean_object* v_testDriverArgs_1404_; lean_object* v_lintDriver_1405_; lean_object* v_lintDriverArgs_1406_; lean_object* v_version_1407_; lean_object* v_versionTags_1408_; lean_object* v_description_1409_; lean_object* v_keywords_1410_; lean_object* v_homepage_1411_; lean_object* v_license_1412_; lean_object* v_licenseFiles_1413_; lean_object* v_readmeFile_1414_; uint8_t v_reservoir_1415_; lean_object* v_enableArtifactCache_x3f_1416_; lean_object* v_restoreAllArtifacts_x3f_1417_; uint8_t v_libPrefixOnWindows_1418_; uint8_t v_allowImportAll_1419_; uint8_t v_fixedToolchain_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1428_; 
v_toWorkspaceConfig_1388_ = lean_ctor_get(v_cfg_1387_, 0);
v_toLeanConfig_1389_ = lean_ctor_get(v_cfg_1387_, 1);
v_bootstrap_1390_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*26);
v_extraDepTargets_1391_ = lean_ctor_get(v_cfg_1387_, 2);
v_precompileModules_1392_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1393_ = lean_ctor_get(v_cfg_1387_, 3);
v_srcDir_1394_ = lean_ctor_get(v_cfg_1387_, 4);
v_buildDir_1395_ = lean_ctor_get(v_cfg_1387_, 5);
v_leanLibDir_1396_ = lean_ctor_get(v_cfg_1387_, 6);
v_nativeLibDir_1397_ = lean_ctor_get(v_cfg_1387_, 7);
v_binDir_1398_ = lean_ctor_get(v_cfg_1387_, 8);
v_irDir_1399_ = lean_ctor_get(v_cfg_1387_, 9);
v_releaseRepo_1400_ = lean_ctor_get(v_cfg_1387_, 10);
v_buildArchive_1401_ = lean_ctor_get(v_cfg_1387_, 11);
v_preferReleaseBuild_1402_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*26 + 2);
v_testDriver_1403_ = lean_ctor_get(v_cfg_1387_, 12);
v_testDriverArgs_1404_ = lean_ctor_get(v_cfg_1387_, 13);
v_lintDriver_1405_ = lean_ctor_get(v_cfg_1387_, 14);
v_lintDriverArgs_1406_ = lean_ctor_get(v_cfg_1387_, 15);
v_version_1407_ = lean_ctor_get(v_cfg_1387_, 16);
v_versionTags_1408_ = lean_ctor_get(v_cfg_1387_, 17);
v_description_1409_ = lean_ctor_get(v_cfg_1387_, 18);
v_keywords_1410_ = lean_ctor_get(v_cfg_1387_, 19);
v_homepage_1411_ = lean_ctor_get(v_cfg_1387_, 20);
v_license_1412_ = lean_ctor_get(v_cfg_1387_, 21);
v_licenseFiles_1413_ = lean_ctor_get(v_cfg_1387_, 22);
v_readmeFile_1414_ = lean_ctor_get(v_cfg_1387_, 23);
v_reservoir_1415_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1416_ = lean_ctor_get(v_cfg_1387_, 24);
v_restoreAllArtifacts_x3f_1417_ = lean_ctor_get(v_cfg_1387_, 25);
v_libPrefixOnWindows_1418_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*26 + 4);
v_allowImportAll_1419_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*26 + 5);
v_fixedToolchain_1420_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*26 + 6);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_cfg_1387_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1422_ = v_cfg_1387_;
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1417_);
lean_inc(v_enableArtifactCache_x3f_1416_);
lean_inc(v_readmeFile_1414_);
lean_inc(v_licenseFiles_1413_);
lean_inc(v_license_1412_);
lean_inc(v_homepage_1411_);
lean_inc(v_keywords_1410_);
lean_inc(v_description_1409_);
lean_inc(v_versionTags_1408_);
lean_inc(v_version_1407_);
lean_inc(v_lintDriverArgs_1406_);
lean_inc(v_lintDriver_1405_);
lean_inc(v_testDriverArgs_1404_);
lean_inc(v_testDriver_1403_);
lean_inc(v_buildArchive_1401_);
lean_inc(v_releaseRepo_1400_);
lean_inc(v_irDir_1399_);
lean_inc(v_binDir_1398_);
lean_inc(v_nativeLibDir_1397_);
lean_inc(v_leanLibDir_1396_);
lean_inc(v_buildDir_1395_);
lean_inc(v_srcDir_1394_);
lean_inc(v_moreGlobalServerArgs_1393_);
lean_inc(v_extraDepTargets_1391_);
lean_inc(v_toLeanConfig_1389_);
lean_inc(v_toWorkspaceConfig_1388_);
lean_dec(v_cfg_1387_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = lean_apply_1(v_f_1386_, v_buildArchive_1401_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 11, v___x_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_toWorkspaceConfig_1388_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_toLeanConfig_1389_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_extraDepTargets_1391_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v_moreGlobalServerArgs_1393_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v_srcDir_1394_);
lean_ctor_set(v_reuseFailAlloc_1427_, 5, v_buildDir_1395_);
lean_ctor_set(v_reuseFailAlloc_1427_, 6, v_leanLibDir_1396_);
lean_ctor_set(v_reuseFailAlloc_1427_, 7, v_nativeLibDir_1397_);
lean_ctor_set(v_reuseFailAlloc_1427_, 8, v_binDir_1398_);
lean_ctor_set(v_reuseFailAlloc_1427_, 9, v_irDir_1399_);
lean_ctor_set(v_reuseFailAlloc_1427_, 10, v_releaseRepo_1400_);
lean_ctor_set(v_reuseFailAlloc_1427_, 11, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1427_, 12, v_testDriver_1403_);
lean_ctor_set(v_reuseFailAlloc_1427_, 13, v_testDriverArgs_1404_);
lean_ctor_set(v_reuseFailAlloc_1427_, 14, v_lintDriver_1405_);
lean_ctor_set(v_reuseFailAlloc_1427_, 15, v_lintDriverArgs_1406_);
lean_ctor_set(v_reuseFailAlloc_1427_, 16, v_version_1407_);
lean_ctor_set(v_reuseFailAlloc_1427_, 17, v_versionTags_1408_);
lean_ctor_set(v_reuseFailAlloc_1427_, 18, v_description_1409_);
lean_ctor_set(v_reuseFailAlloc_1427_, 19, v_keywords_1410_);
lean_ctor_set(v_reuseFailAlloc_1427_, 20, v_homepage_1411_);
lean_ctor_set(v_reuseFailAlloc_1427_, 21, v_license_1412_);
lean_ctor_set(v_reuseFailAlloc_1427_, 22, v_licenseFiles_1413_);
lean_ctor_set(v_reuseFailAlloc_1427_, 23, v_readmeFile_1414_);
lean_ctor_set(v_reuseFailAlloc_1427_, 24, v_enableArtifactCache_x3f_1416_);
lean_ctor_set(v_reuseFailAlloc_1427_, 25, v_restoreAllArtifacts_x3f_1417_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*26, v_bootstrap_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*26 + 1, v_precompileModules_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1402_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*26 + 3, v_reservoir_1415_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1418_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*26 + 5, v_allowImportAll_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*26 + 6, v_fixedToolchain_1420_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object* v_p_1437_, lean_object* v_n_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = ((lean_object*)(l_Lake_PackageConfig_buildArchive___proj___closed__3));
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object* v_p_1440_, lean_object* v_n_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1440_, v_n_1441_);
lean_dec(v_n_1441_);
lean_dec(v_p_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object* v_p_1443_, lean_object* v_n_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1443_, v_n_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object* v_p_1446_, lean_object* v_n_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lake_PackageConfig_buildArchive_instConfigField(v_p_1446_, v_n_1447_);
lean_dec(v_n_1447_);
lean_dec(v_p_1446_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object* v_p_1449_, lean_object* v_n_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1449_, v_n_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object* v_p_1452_, lean_object* v_n_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField(v_p_1452_, v_n_1453_);
lean_dec(v_n_1453_);
lean_dec(v_p_1452_);
return v_res_1454_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(lean_object* v_cfg_1455_){
_start:
{
uint8_t v_preferReleaseBuild_1456_; 
v_preferReleaseBuild_1456_ = lean_ctor_get_uint8(v_cfg_1455_, sizeof(void*)*26 + 2);
return v_preferReleaseBuild_1456_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0___boxed(lean_object* v_cfg_1457_){
_start:
{
uint8_t v_res_1458_; lean_object* v_r_1459_; 
v_res_1458_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(v_cfg_1457_);
lean_dec_ref(v_cfg_1457_);
v_r_1459_ = lean_box(v_res_1458_);
return v_r_1459_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(uint8_t v_val_1460_, lean_object* v_cfg_1461_){
_start:
{
lean_object* v_toWorkspaceConfig_1462_; lean_object* v_toLeanConfig_1463_; uint8_t v_bootstrap_1464_; lean_object* v_extraDepTargets_1465_; uint8_t v_precompileModules_1466_; lean_object* v_moreGlobalServerArgs_1467_; lean_object* v_srcDir_1468_; lean_object* v_buildDir_1469_; lean_object* v_leanLibDir_1470_; lean_object* v_nativeLibDir_1471_; lean_object* v_binDir_1472_; lean_object* v_irDir_1473_; lean_object* v_releaseRepo_1474_; lean_object* v_buildArchive_1475_; lean_object* v_testDriver_1476_; lean_object* v_testDriverArgs_1477_; lean_object* v_lintDriver_1478_; lean_object* v_lintDriverArgs_1479_; lean_object* v_version_1480_; lean_object* v_versionTags_1481_; lean_object* v_description_1482_; lean_object* v_keywords_1483_; lean_object* v_homepage_1484_; lean_object* v_license_1485_; lean_object* v_licenseFiles_1486_; lean_object* v_readmeFile_1487_; uint8_t v_reservoir_1488_; lean_object* v_enableArtifactCache_x3f_1489_; lean_object* v_restoreAllArtifacts_x3f_1490_; uint8_t v_libPrefixOnWindows_1491_; uint8_t v_allowImportAll_1492_; uint8_t v_fixedToolchain_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
v_toWorkspaceConfig_1462_ = lean_ctor_get(v_cfg_1461_, 0);
v_toLeanConfig_1463_ = lean_ctor_get(v_cfg_1461_, 1);
v_bootstrap_1464_ = lean_ctor_get_uint8(v_cfg_1461_, sizeof(void*)*26);
v_extraDepTargets_1465_ = lean_ctor_get(v_cfg_1461_, 2);
v_precompileModules_1466_ = lean_ctor_get_uint8(v_cfg_1461_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1467_ = lean_ctor_get(v_cfg_1461_, 3);
v_srcDir_1468_ = lean_ctor_get(v_cfg_1461_, 4);
v_buildDir_1469_ = lean_ctor_get(v_cfg_1461_, 5);
v_leanLibDir_1470_ = lean_ctor_get(v_cfg_1461_, 6);
v_nativeLibDir_1471_ = lean_ctor_get(v_cfg_1461_, 7);
v_binDir_1472_ = lean_ctor_get(v_cfg_1461_, 8);
v_irDir_1473_ = lean_ctor_get(v_cfg_1461_, 9);
v_releaseRepo_1474_ = lean_ctor_get(v_cfg_1461_, 10);
v_buildArchive_1475_ = lean_ctor_get(v_cfg_1461_, 11);
v_testDriver_1476_ = lean_ctor_get(v_cfg_1461_, 12);
v_testDriverArgs_1477_ = lean_ctor_get(v_cfg_1461_, 13);
v_lintDriver_1478_ = lean_ctor_get(v_cfg_1461_, 14);
v_lintDriverArgs_1479_ = lean_ctor_get(v_cfg_1461_, 15);
v_version_1480_ = lean_ctor_get(v_cfg_1461_, 16);
v_versionTags_1481_ = lean_ctor_get(v_cfg_1461_, 17);
v_description_1482_ = lean_ctor_get(v_cfg_1461_, 18);
v_keywords_1483_ = lean_ctor_get(v_cfg_1461_, 19);
v_homepage_1484_ = lean_ctor_get(v_cfg_1461_, 20);
v_license_1485_ = lean_ctor_get(v_cfg_1461_, 21);
v_licenseFiles_1486_ = lean_ctor_get(v_cfg_1461_, 22);
v_readmeFile_1487_ = lean_ctor_get(v_cfg_1461_, 23);
v_reservoir_1488_ = lean_ctor_get_uint8(v_cfg_1461_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1489_ = lean_ctor_get(v_cfg_1461_, 24);
v_restoreAllArtifacts_x3f_1490_ = lean_ctor_get(v_cfg_1461_, 25);
v_libPrefixOnWindows_1491_ = lean_ctor_get_uint8(v_cfg_1461_, sizeof(void*)*26 + 4);
v_allowImportAll_1492_ = lean_ctor_get_uint8(v_cfg_1461_, sizeof(void*)*26 + 5);
v_fixedToolchain_1493_ = lean_ctor_get_uint8(v_cfg_1461_, sizeof(void*)*26 + 6);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_cfg_1461_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v_cfg_1461_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1490_);
lean_inc(v_enableArtifactCache_x3f_1489_);
lean_inc(v_readmeFile_1487_);
lean_inc(v_licenseFiles_1486_);
lean_inc(v_license_1485_);
lean_inc(v_homepage_1484_);
lean_inc(v_keywords_1483_);
lean_inc(v_description_1482_);
lean_inc(v_versionTags_1481_);
lean_inc(v_version_1480_);
lean_inc(v_lintDriverArgs_1479_);
lean_inc(v_lintDriver_1478_);
lean_inc(v_testDriverArgs_1477_);
lean_inc(v_testDriver_1476_);
lean_inc(v_buildArchive_1475_);
lean_inc(v_releaseRepo_1474_);
lean_inc(v_irDir_1473_);
lean_inc(v_binDir_1472_);
lean_inc(v_nativeLibDir_1471_);
lean_inc(v_leanLibDir_1470_);
lean_inc(v_buildDir_1469_);
lean_inc(v_srcDir_1468_);
lean_inc(v_moreGlobalServerArgs_1467_);
lean_inc(v_extraDepTargets_1465_);
lean_inc(v_toLeanConfig_1463_);
lean_inc(v_toWorkspaceConfig_1462_);
lean_dec(v_cfg_1461_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_toWorkspaceConfig_1462_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_toLeanConfig_1463_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_extraDepTargets_1465_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_moreGlobalServerArgs_1467_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_srcDir_1468_);
lean_ctor_set(v_reuseFailAlloc_1499_, 5, v_buildDir_1469_);
lean_ctor_set(v_reuseFailAlloc_1499_, 6, v_leanLibDir_1470_);
lean_ctor_set(v_reuseFailAlloc_1499_, 7, v_nativeLibDir_1471_);
lean_ctor_set(v_reuseFailAlloc_1499_, 8, v_binDir_1472_);
lean_ctor_set(v_reuseFailAlloc_1499_, 9, v_irDir_1473_);
lean_ctor_set(v_reuseFailAlloc_1499_, 10, v_releaseRepo_1474_);
lean_ctor_set(v_reuseFailAlloc_1499_, 11, v_buildArchive_1475_);
lean_ctor_set(v_reuseFailAlloc_1499_, 12, v_testDriver_1476_);
lean_ctor_set(v_reuseFailAlloc_1499_, 13, v_testDriverArgs_1477_);
lean_ctor_set(v_reuseFailAlloc_1499_, 14, v_lintDriver_1478_);
lean_ctor_set(v_reuseFailAlloc_1499_, 15, v_lintDriverArgs_1479_);
lean_ctor_set(v_reuseFailAlloc_1499_, 16, v_version_1480_);
lean_ctor_set(v_reuseFailAlloc_1499_, 17, v_versionTags_1481_);
lean_ctor_set(v_reuseFailAlloc_1499_, 18, v_description_1482_);
lean_ctor_set(v_reuseFailAlloc_1499_, 19, v_keywords_1483_);
lean_ctor_set(v_reuseFailAlloc_1499_, 20, v_homepage_1484_);
lean_ctor_set(v_reuseFailAlloc_1499_, 21, v_license_1485_);
lean_ctor_set(v_reuseFailAlloc_1499_, 22, v_licenseFiles_1486_);
lean_ctor_set(v_reuseFailAlloc_1499_, 23, v_readmeFile_1487_);
lean_ctor_set(v_reuseFailAlloc_1499_, 24, v_enableArtifactCache_x3f_1489_);
lean_ctor_set(v_reuseFailAlloc_1499_, 25, v_restoreAllArtifacts_x3f_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*26, v_bootstrap_1464_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*26 + 1, v_precompileModules_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*26 + 3, v_reservoir_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*26 + 5, v_allowImportAll_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*26 + 6, v_fixedToolchain_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*26 + 2, v_val_1460_);
return v___x_1498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1___boxed(lean_object* v_val_1501_, lean_object* v_cfg_1502_){
_start:
{
uint8_t v_val_134__boxed_1503_; lean_object* v_res_1504_; 
v_val_134__boxed_1503_ = lean_unbox(v_val_1501_);
v_res_1504_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(v_val_134__boxed_1503_, v_cfg_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__2(lean_object* v_f_1505_, lean_object* v_cfg_1506_){
_start:
{
lean_object* v_toWorkspaceConfig_1507_; lean_object* v_toLeanConfig_1508_; uint8_t v_bootstrap_1509_; lean_object* v_extraDepTargets_1510_; uint8_t v_precompileModules_1511_; lean_object* v_moreGlobalServerArgs_1512_; lean_object* v_srcDir_1513_; lean_object* v_buildDir_1514_; lean_object* v_leanLibDir_1515_; lean_object* v_nativeLibDir_1516_; lean_object* v_binDir_1517_; lean_object* v_irDir_1518_; lean_object* v_releaseRepo_1519_; lean_object* v_buildArchive_1520_; uint8_t v_preferReleaseBuild_1521_; lean_object* v_testDriver_1522_; lean_object* v_testDriverArgs_1523_; lean_object* v_lintDriver_1524_; lean_object* v_lintDriverArgs_1525_; lean_object* v_version_1526_; lean_object* v_versionTags_1527_; lean_object* v_description_1528_; lean_object* v_keywords_1529_; lean_object* v_homepage_1530_; lean_object* v_license_1531_; lean_object* v_licenseFiles_1532_; lean_object* v_readmeFile_1533_; uint8_t v_reservoir_1534_; lean_object* v_enableArtifactCache_x3f_1535_; lean_object* v_restoreAllArtifacts_x3f_1536_; uint8_t v_libPrefixOnWindows_1537_; uint8_t v_allowImportAll_1538_; uint8_t v_fixedToolchain_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1549_; 
v_toWorkspaceConfig_1507_ = lean_ctor_get(v_cfg_1506_, 0);
v_toLeanConfig_1508_ = lean_ctor_get(v_cfg_1506_, 1);
v_bootstrap_1509_ = lean_ctor_get_uint8(v_cfg_1506_, sizeof(void*)*26);
v_extraDepTargets_1510_ = lean_ctor_get(v_cfg_1506_, 2);
v_precompileModules_1511_ = lean_ctor_get_uint8(v_cfg_1506_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1512_ = lean_ctor_get(v_cfg_1506_, 3);
v_srcDir_1513_ = lean_ctor_get(v_cfg_1506_, 4);
v_buildDir_1514_ = lean_ctor_get(v_cfg_1506_, 5);
v_leanLibDir_1515_ = lean_ctor_get(v_cfg_1506_, 6);
v_nativeLibDir_1516_ = lean_ctor_get(v_cfg_1506_, 7);
v_binDir_1517_ = lean_ctor_get(v_cfg_1506_, 8);
v_irDir_1518_ = lean_ctor_get(v_cfg_1506_, 9);
v_releaseRepo_1519_ = lean_ctor_get(v_cfg_1506_, 10);
v_buildArchive_1520_ = lean_ctor_get(v_cfg_1506_, 11);
v_preferReleaseBuild_1521_ = lean_ctor_get_uint8(v_cfg_1506_, sizeof(void*)*26 + 2);
v_testDriver_1522_ = lean_ctor_get(v_cfg_1506_, 12);
v_testDriverArgs_1523_ = lean_ctor_get(v_cfg_1506_, 13);
v_lintDriver_1524_ = lean_ctor_get(v_cfg_1506_, 14);
v_lintDriverArgs_1525_ = lean_ctor_get(v_cfg_1506_, 15);
v_version_1526_ = lean_ctor_get(v_cfg_1506_, 16);
v_versionTags_1527_ = lean_ctor_get(v_cfg_1506_, 17);
v_description_1528_ = lean_ctor_get(v_cfg_1506_, 18);
v_keywords_1529_ = lean_ctor_get(v_cfg_1506_, 19);
v_homepage_1530_ = lean_ctor_get(v_cfg_1506_, 20);
v_license_1531_ = lean_ctor_get(v_cfg_1506_, 21);
v_licenseFiles_1532_ = lean_ctor_get(v_cfg_1506_, 22);
v_readmeFile_1533_ = lean_ctor_get(v_cfg_1506_, 23);
v_reservoir_1534_ = lean_ctor_get_uint8(v_cfg_1506_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1535_ = lean_ctor_get(v_cfg_1506_, 24);
v_restoreAllArtifacts_x3f_1536_ = lean_ctor_get(v_cfg_1506_, 25);
v_libPrefixOnWindows_1537_ = lean_ctor_get_uint8(v_cfg_1506_, sizeof(void*)*26 + 4);
v_allowImportAll_1538_ = lean_ctor_get_uint8(v_cfg_1506_, sizeof(void*)*26 + 5);
v_fixedToolchain_1539_ = lean_ctor_get_uint8(v_cfg_1506_, sizeof(void*)*26 + 6);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_cfg_1506_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1541_ = v_cfg_1506_;
v_isShared_1542_ = v_isSharedCheck_1549_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1536_);
lean_inc(v_enableArtifactCache_x3f_1535_);
lean_inc(v_readmeFile_1533_);
lean_inc(v_licenseFiles_1532_);
lean_inc(v_license_1531_);
lean_inc(v_homepage_1530_);
lean_inc(v_keywords_1529_);
lean_inc(v_description_1528_);
lean_inc(v_versionTags_1527_);
lean_inc(v_version_1526_);
lean_inc(v_lintDriverArgs_1525_);
lean_inc(v_lintDriver_1524_);
lean_inc(v_testDriverArgs_1523_);
lean_inc(v_testDriver_1522_);
lean_inc(v_buildArchive_1520_);
lean_inc(v_releaseRepo_1519_);
lean_inc(v_irDir_1518_);
lean_inc(v_binDir_1517_);
lean_inc(v_nativeLibDir_1516_);
lean_inc(v_leanLibDir_1515_);
lean_inc(v_buildDir_1514_);
lean_inc(v_srcDir_1513_);
lean_inc(v_moreGlobalServerArgs_1512_);
lean_inc(v_extraDepTargets_1510_);
lean_inc(v_toLeanConfig_1508_);
lean_inc(v_toWorkspaceConfig_1507_);
lean_dec(v_cfg_1506_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1549_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1543_ = lean_box(v_preferReleaseBuild_1521_);
v___x_1544_ = lean_apply_1(v_f_1505_, v___x_1543_);
if (v_isShared_1542_ == 0)
{
v___x_1546_ = v___x_1541_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_toWorkspaceConfig_1507_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_toLeanConfig_1508_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_extraDepTargets_1510_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_moreGlobalServerArgs_1512_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_srcDir_1513_);
lean_ctor_set(v_reuseFailAlloc_1548_, 5, v_buildDir_1514_);
lean_ctor_set(v_reuseFailAlloc_1548_, 6, v_leanLibDir_1515_);
lean_ctor_set(v_reuseFailAlloc_1548_, 7, v_nativeLibDir_1516_);
lean_ctor_set(v_reuseFailAlloc_1548_, 8, v_binDir_1517_);
lean_ctor_set(v_reuseFailAlloc_1548_, 9, v_irDir_1518_);
lean_ctor_set(v_reuseFailAlloc_1548_, 10, v_releaseRepo_1519_);
lean_ctor_set(v_reuseFailAlloc_1548_, 11, v_buildArchive_1520_);
lean_ctor_set(v_reuseFailAlloc_1548_, 12, v_testDriver_1522_);
lean_ctor_set(v_reuseFailAlloc_1548_, 13, v_testDriverArgs_1523_);
lean_ctor_set(v_reuseFailAlloc_1548_, 14, v_lintDriver_1524_);
lean_ctor_set(v_reuseFailAlloc_1548_, 15, v_lintDriverArgs_1525_);
lean_ctor_set(v_reuseFailAlloc_1548_, 16, v_version_1526_);
lean_ctor_set(v_reuseFailAlloc_1548_, 17, v_versionTags_1527_);
lean_ctor_set(v_reuseFailAlloc_1548_, 18, v_description_1528_);
lean_ctor_set(v_reuseFailAlloc_1548_, 19, v_keywords_1529_);
lean_ctor_set(v_reuseFailAlloc_1548_, 20, v_homepage_1530_);
lean_ctor_set(v_reuseFailAlloc_1548_, 21, v_license_1531_);
lean_ctor_set(v_reuseFailAlloc_1548_, 22, v_licenseFiles_1532_);
lean_ctor_set(v_reuseFailAlloc_1548_, 23, v_readmeFile_1533_);
lean_ctor_set(v_reuseFailAlloc_1548_, 24, v_enableArtifactCache_x3f_1535_);
lean_ctor_set(v_reuseFailAlloc_1548_, 25, v_restoreAllArtifacts_x3f_1536_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*26, v_bootstrap_1509_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*26 + 1, v_precompileModules_1511_);
v___x_1546_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
uint8_t v___x_1547_; 
v___x_1547_ = lean_unbox(v___x_1544_);
lean_ctor_set_uint8(v___x_1546_, sizeof(void*)*26 + 2, v___x_1547_);
lean_ctor_set_uint8(v___x_1546_, sizeof(void*)*26 + 3, v_reservoir_1534_);
lean_ctor_set_uint8(v___x_1546_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1537_);
lean_ctor_set_uint8(v___x_1546_, sizeof(void*)*26 + 5, v_allowImportAll_1538_);
lean_ctor_set_uint8(v___x_1546_, sizeof(void*)*26 + 6, v_fixedToolchain_1539_);
return v___x_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object* v_p_1558_, lean_object* v_n_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = ((lean_object*)(l_Lake_PackageConfig_preferReleaseBuild___proj___closed__3));
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object* v_p_1561_, lean_object* v_n_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1561_, v_n_1562_);
lean_dec(v_n_1562_);
lean_dec(v_p_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object* v_p_1564_, lean_object* v_n_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1564_, v_n_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object* v_p_1567_, lean_object* v_n_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField(v_p_1567_, v_n_1568_);
lean_dec(v_n_1568_);
lean_dec(v_p_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0(lean_object* v_cfg_1570_){
_start:
{
lean_object* v_testDriver_1571_; 
v_testDriver_1571_ = lean_ctor_get(v_cfg_1570_, 12);
lean_inc_ref(v_testDriver_1571_);
return v_testDriver_1571_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0___boxed(lean_object* v_cfg_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lake_PackageConfig_testDriver___proj___lam__0(v_cfg_1572_);
lean_dec_ref(v_cfg_1572_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__1(lean_object* v_val_1574_, lean_object* v_cfg_1575_){
_start:
{
lean_object* v_toWorkspaceConfig_1576_; lean_object* v_toLeanConfig_1577_; uint8_t v_bootstrap_1578_; lean_object* v_extraDepTargets_1579_; uint8_t v_precompileModules_1580_; lean_object* v_moreGlobalServerArgs_1581_; lean_object* v_srcDir_1582_; lean_object* v_buildDir_1583_; lean_object* v_leanLibDir_1584_; lean_object* v_nativeLibDir_1585_; lean_object* v_binDir_1586_; lean_object* v_irDir_1587_; lean_object* v_releaseRepo_1588_; lean_object* v_buildArchive_1589_; uint8_t v_preferReleaseBuild_1590_; lean_object* v_testDriverArgs_1591_; lean_object* v_lintDriver_1592_; lean_object* v_lintDriverArgs_1593_; lean_object* v_version_1594_; lean_object* v_versionTags_1595_; lean_object* v_description_1596_; lean_object* v_keywords_1597_; lean_object* v_homepage_1598_; lean_object* v_license_1599_; lean_object* v_licenseFiles_1600_; lean_object* v_readmeFile_1601_; uint8_t v_reservoir_1602_; lean_object* v_enableArtifactCache_x3f_1603_; lean_object* v_restoreAllArtifacts_x3f_1604_; uint8_t v_libPrefixOnWindows_1605_; uint8_t v_allowImportAll_1606_; uint8_t v_fixedToolchain_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_toWorkspaceConfig_1576_ = lean_ctor_get(v_cfg_1575_, 0);
v_toLeanConfig_1577_ = lean_ctor_get(v_cfg_1575_, 1);
v_bootstrap_1578_ = lean_ctor_get_uint8(v_cfg_1575_, sizeof(void*)*26);
v_extraDepTargets_1579_ = lean_ctor_get(v_cfg_1575_, 2);
v_precompileModules_1580_ = lean_ctor_get_uint8(v_cfg_1575_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1581_ = lean_ctor_get(v_cfg_1575_, 3);
v_srcDir_1582_ = lean_ctor_get(v_cfg_1575_, 4);
v_buildDir_1583_ = lean_ctor_get(v_cfg_1575_, 5);
v_leanLibDir_1584_ = lean_ctor_get(v_cfg_1575_, 6);
v_nativeLibDir_1585_ = lean_ctor_get(v_cfg_1575_, 7);
v_binDir_1586_ = lean_ctor_get(v_cfg_1575_, 8);
v_irDir_1587_ = lean_ctor_get(v_cfg_1575_, 9);
v_releaseRepo_1588_ = lean_ctor_get(v_cfg_1575_, 10);
v_buildArchive_1589_ = lean_ctor_get(v_cfg_1575_, 11);
v_preferReleaseBuild_1590_ = lean_ctor_get_uint8(v_cfg_1575_, sizeof(void*)*26 + 2);
v_testDriverArgs_1591_ = lean_ctor_get(v_cfg_1575_, 13);
v_lintDriver_1592_ = lean_ctor_get(v_cfg_1575_, 14);
v_lintDriverArgs_1593_ = lean_ctor_get(v_cfg_1575_, 15);
v_version_1594_ = lean_ctor_get(v_cfg_1575_, 16);
v_versionTags_1595_ = lean_ctor_get(v_cfg_1575_, 17);
v_description_1596_ = lean_ctor_get(v_cfg_1575_, 18);
v_keywords_1597_ = lean_ctor_get(v_cfg_1575_, 19);
v_homepage_1598_ = lean_ctor_get(v_cfg_1575_, 20);
v_license_1599_ = lean_ctor_get(v_cfg_1575_, 21);
v_licenseFiles_1600_ = lean_ctor_get(v_cfg_1575_, 22);
v_readmeFile_1601_ = lean_ctor_get(v_cfg_1575_, 23);
v_reservoir_1602_ = lean_ctor_get_uint8(v_cfg_1575_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1603_ = lean_ctor_get(v_cfg_1575_, 24);
v_restoreAllArtifacts_x3f_1604_ = lean_ctor_get(v_cfg_1575_, 25);
v_libPrefixOnWindows_1605_ = lean_ctor_get_uint8(v_cfg_1575_, sizeof(void*)*26 + 4);
v_allowImportAll_1606_ = lean_ctor_get_uint8(v_cfg_1575_, sizeof(void*)*26 + 5);
v_fixedToolchain_1607_ = lean_ctor_get_uint8(v_cfg_1575_, sizeof(void*)*26 + 6);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_cfg_1575_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v_cfg_1575_, 12);
lean_dec(v_unused_1615_);
v___x_1609_ = v_cfg_1575_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1604_);
lean_inc(v_enableArtifactCache_x3f_1603_);
lean_inc(v_readmeFile_1601_);
lean_inc(v_licenseFiles_1600_);
lean_inc(v_license_1599_);
lean_inc(v_homepage_1598_);
lean_inc(v_keywords_1597_);
lean_inc(v_description_1596_);
lean_inc(v_versionTags_1595_);
lean_inc(v_version_1594_);
lean_inc(v_lintDriverArgs_1593_);
lean_inc(v_lintDriver_1592_);
lean_inc(v_testDriverArgs_1591_);
lean_inc(v_buildArchive_1589_);
lean_inc(v_releaseRepo_1588_);
lean_inc(v_irDir_1587_);
lean_inc(v_binDir_1586_);
lean_inc(v_nativeLibDir_1585_);
lean_inc(v_leanLibDir_1584_);
lean_inc(v_buildDir_1583_);
lean_inc(v_srcDir_1582_);
lean_inc(v_moreGlobalServerArgs_1581_);
lean_inc(v_extraDepTargets_1579_);
lean_inc(v_toLeanConfig_1577_);
lean_inc(v_toWorkspaceConfig_1576_);
lean_dec(v_cfg_1575_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 12, v_val_1574_);
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_toWorkspaceConfig_1576_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_toLeanConfig_1577_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_extraDepTargets_1579_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_moreGlobalServerArgs_1581_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_srcDir_1582_);
lean_ctor_set(v_reuseFailAlloc_1613_, 5, v_buildDir_1583_);
lean_ctor_set(v_reuseFailAlloc_1613_, 6, v_leanLibDir_1584_);
lean_ctor_set(v_reuseFailAlloc_1613_, 7, v_nativeLibDir_1585_);
lean_ctor_set(v_reuseFailAlloc_1613_, 8, v_binDir_1586_);
lean_ctor_set(v_reuseFailAlloc_1613_, 9, v_irDir_1587_);
lean_ctor_set(v_reuseFailAlloc_1613_, 10, v_releaseRepo_1588_);
lean_ctor_set(v_reuseFailAlloc_1613_, 11, v_buildArchive_1589_);
lean_ctor_set(v_reuseFailAlloc_1613_, 12, v_val_1574_);
lean_ctor_set(v_reuseFailAlloc_1613_, 13, v_testDriverArgs_1591_);
lean_ctor_set(v_reuseFailAlloc_1613_, 14, v_lintDriver_1592_);
lean_ctor_set(v_reuseFailAlloc_1613_, 15, v_lintDriverArgs_1593_);
lean_ctor_set(v_reuseFailAlloc_1613_, 16, v_version_1594_);
lean_ctor_set(v_reuseFailAlloc_1613_, 17, v_versionTags_1595_);
lean_ctor_set(v_reuseFailAlloc_1613_, 18, v_description_1596_);
lean_ctor_set(v_reuseFailAlloc_1613_, 19, v_keywords_1597_);
lean_ctor_set(v_reuseFailAlloc_1613_, 20, v_homepage_1598_);
lean_ctor_set(v_reuseFailAlloc_1613_, 21, v_license_1599_);
lean_ctor_set(v_reuseFailAlloc_1613_, 22, v_licenseFiles_1600_);
lean_ctor_set(v_reuseFailAlloc_1613_, 23, v_readmeFile_1601_);
lean_ctor_set(v_reuseFailAlloc_1613_, 24, v_enableArtifactCache_x3f_1603_);
lean_ctor_set(v_reuseFailAlloc_1613_, 25, v_restoreAllArtifacts_x3f_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1613_, sizeof(void*)*26, v_bootstrap_1578_);
lean_ctor_set_uint8(v_reuseFailAlloc_1613_, sizeof(void*)*26 + 1, v_precompileModules_1580_);
lean_ctor_set_uint8(v_reuseFailAlloc_1613_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1590_);
lean_ctor_set_uint8(v_reuseFailAlloc_1613_, sizeof(void*)*26 + 3, v_reservoir_1602_);
lean_ctor_set_uint8(v_reuseFailAlloc_1613_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1613_, sizeof(void*)*26 + 5, v_allowImportAll_1606_);
lean_ctor_set_uint8(v_reuseFailAlloc_1613_, sizeof(void*)*26 + 6, v_fixedToolchain_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__2(lean_object* v_f_1616_, lean_object* v_cfg_1617_){
_start:
{
lean_object* v_toWorkspaceConfig_1618_; lean_object* v_toLeanConfig_1619_; uint8_t v_bootstrap_1620_; lean_object* v_extraDepTargets_1621_; uint8_t v_precompileModules_1622_; lean_object* v_moreGlobalServerArgs_1623_; lean_object* v_srcDir_1624_; lean_object* v_buildDir_1625_; lean_object* v_leanLibDir_1626_; lean_object* v_nativeLibDir_1627_; lean_object* v_binDir_1628_; lean_object* v_irDir_1629_; lean_object* v_releaseRepo_1630_; lean_object* v_buildArchive_1631_; uint8_t v_preferReleaseBuild_1632_; lean_object* v_testDriver_1633_; lean_object* v_testDriverArgs_1634_; lean_object* v_lintDriver_1635_; lean_object* v_lintDriverArgs_1636_; lean_object* v_version_1637_; lean_object* v_versionTags_1638_; lean_object* v_description_1639_; lean_object* v_keywords_1640_; lean_object* v_homepage_1641_; lean_object* v_license_1642_; lean_object* v_licenseFiles_1643_; lean_object* v_readmeFile_1644_; uint8_t v_reservoir_1645_; lean_object* v_enableArtifactCache_x3f_1646_; lean_object* v_restoreAllArtifacts_x3f_1647_; uint8_t v_libPrefixOnWindows_1648_; uint8_t v_allowImportAll_1649_; uint8_t v_fixedToolchain_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
v_toWorkspaceConfig_1618_ = lean_ctor_get(v_cfg_1617_, 0);
v_toLeanConfig_1619_ = lean_ctor_get(v_cfg_1617_, 1);
v_bootstrap_1620_ = lean_ctor_get_uint8(v_cfg_1617_, sizeof(void*)*26);
v_extraDepTargets_1621_ = lean_ctor_get(v_cfg_1617_, 2);
v_precompileModules_1622_ = lean_ctor_get_uint8(v_cfg_1617_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1623_ = lean_ctor_get(v_cfg_1617_, 3);
v_srcDir_1624_ = lean_ctor_get(v_cfg_1617_, 4);
v_buildDir_1625_ = lean_ctor_get(v_cfg_1617_, 5);
v_leanLibDir_1626_ = lean_ctor_get(v_cfg_1617_, 6);
v_nativeLibDir_1627_ = lean_ctor_get(v_cfg_1617_, 7);
v_binDir_1628_ = lean_ctor_get(v_cfg_1617_, 8);
v_irDir_1629_ = lean_ctor_get(v_cfg_1617_, 9);
v_releaseRepo_1630_ = lean_ctor_get(v_cfg_1617_, 10);
v_buildArchive_1631_ = lean_ctor_get(v_cfg_1617_, 11);
v_preferReleaseBuild_1632_ = lean_ctor_get_uint8(v_cfg_1617_, sizeof(void*)*26 + 2);
v_testDriver_1633_ = lean_ctor_get(v_cfg_1617_, 12);
v_testDriverArgs_1634_ = lean_ctor_get(v_cfg_1617_, 13);
v_lintDriver_1635_ = lean_ctor_get(v_cfg_1617_, 14);
v_lintDriverArgs_1636_ = lean_ctor_get(v_cfg_1617_, 15);
v_version_1637_ = lean_ctor_get(v_cfg_1617_, 16);
v_versionTags_1638_ = lean_ctor_get(v_cfg_1617_, 17);
v_description_1639_ = lean_ctor_get(v_cfg_1617_, 18);
v_keywords_1640_ = lean_ctor_get(v_cfg_1617_, 19);
v_homepage_1641_ = lean_ctor_get(v_cfg_1617_, 20);
v_license_1642_ = lean_ctor_get(v_cfg_1617_, 21);
v_licenseFiles_1643_ = lean_ctor_get(v_cfg_1617_, 22);
v_readmeFile_1644_ = lean_ctor_get(v_cfg_1617_, 23);
v_reservoir_1645_ = lean_ctor_get_uint8(v_cfg_1617_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1646_ = lean_ctor_get(v_cfg_1617_, 24);
v_restoreAllArtifacts_x3f_1647_ = lean_ctor_get(v_cfg_1617_, 25);
v_libPrefixOnWindows_1648_ = lean_ctor_get_uint8(v_cfg_1617_, sizeof(void*)*26 + 4);
v_allowImportAll_1649_ = lean_ctor_get_uint8(v_cfg_1617_, sizeof(void*)*26 + 5);
v_fixedToolchain_1650_ = lean_ctor_get_uint8(v_cfg_1617_, sizeof(void*)*26 + 6);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_cfg_1617_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1652_ = v_cfg_1617_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1647_);
lean_inc(v_enableArtifactCache_x3f_1646_);
lean_inc(v_readmeFile_1644_);
lean_inc(v_licenseFiles_1643_);
lean_inc(v_license_1642_);
lean_inc(v_homepage_1641_);
lean_inc(v_keywords_1640_);
lean_inc(v_description_1639_);
lean_inc(v_versionTags_1638_);
lean_inc(v_version_1637_);
lean_inc(v_lintDriverArgs_1636_);
lean_inc(v_lintDriver_1635_);
lean_inc(v_testDriverArgs_1634_);
lean_inc(v_testDriver_1633_);
lean_inc(v_buildArchive_1631_);
lean_inc(v_releaseRepo_1630_);
lean_inc(v_irDir_1629_);
lean_inc(v_binDir_1628_);
lean_inc(v_nativeLibDir_1627_);
lean_inc(v_leanLibDir_1626_);
lean_inc(v_buildDir_1625_);
lean_inc(v_srcDir_1624_);
lean_inc(v_moreGlobalServerArgs_1623_);
lean_inc(v_extraDepTargets_1621_);
lean_inc(v_toLeanConfig_1619_);
lean_inc(v_toWorkspaceConfig_1618_);
lean_dec(v_cfg_1617_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_apply_1(v_f_1616_, v_testDriver_1633_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 12, v___x_1654_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_toWorkspaceConfig_1618_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_toLeanConfig_1619_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_extraDepTargets_1621_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_moreGlobalServerArgs_1623_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_srcDir_1624_);
lean_ctor_set(v_reuseFailAlloc_1657_, 5, v_buildDir_1625_);
lean_ctor_set(v_reuseFailAlloc_1657_, 6, v_leanLibDir_1626_);
lean_ctor_set(v_reuseFailAlloc_1657_, 7, v_nativeLibDir_1627_);
lean_ctor_set(v_reuseFailAlloc_1657_, 8, v_binDir_1628_);
lean_ctor_set(v_reuseFailAlloc_1657_, 9, v_irDir_1629_);
lean_ctor_set(v_reuseFailAlloc_1657_, 10, v_releaseRepo_1630_);
lean_ctor_set(v_reuseFailAlloc_1657_, 11, v_buildArchive_1631_);
lean_ctor_set(v_reuseFailAlloc_1657_, 12, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1657_, 13, v_testDriverArgs_1634_);
lean_ctor_set(v_reuseFailAlloc_1657_, 14, v_lintDriver_1635_);
lean_ctor_set(v_reuseFailAlloc_1657_, 15, v_lintDriverArgs_1636_);
lean_ctor_set(v_reuseFailAlloc_1657_, 16, v_version_1637_);
lean_ctor_set(v_reuseFailAlloc_1657_, 17, v_versionTags_1638_);
lean_ctor_set(v_reuseFailAlloc_1657_, 18, v_description_1639_);
lean_ctor_set(v_reuseFailAlloc_1657_, 19, v_keywords_1640_);
lean_ctor_set(v_reuseFailAlloc_1657_, 20, v_homepage_1641_);
lean_ctor_set(v_reuseFailAlloc_1657_, 21, v_license_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 22, v_licenseFiles_1643_);
lean_ctor_set(v_reuseFailAlloc_1657_, 23, v_readmeFile_1644_);
lean_ctor_set(v_reuseFailAlloc_1657_, 24, v_enableArtifactCache_x3f_1646_);
lean_ctor_set(v_reuseFailAlloc_1657_, 25, v_restoreAllArtifacts_x3f_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*26, v_bootstrap_1620_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*26 + 1, v_precompileModules_1622_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1632_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*26 + 3, v_reservoir_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*26 + 5, v_allowImportAll_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*26 + 6, v_fixedToolchain_1650_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3(lean_object* v_x_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__3));
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3___boxed(lean_object* v_x_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lake_PackageConfig_testDriver___proj___lam__3(v_x_1661_);
lean_dec_ref(v_x_1661_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object* v_p_1672_, lean_object* v_n_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = ((lean_object*)(l_Lake_PackageConfig_testDriver___proj___closed__4));
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object* v_p_1675_, lean_object* v_n_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lake_PackageConfig_testDriver___proj(v_p_1675_, v_n_1676_);
lean_dec(v_n_1676_);
lean_dec(v_p_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object* v_p_1678_, lean_object* v_n_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lake_PackageConfig_testDriver___proj(v_p_1678_, v_n_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object* v_p_1681_, lean_object* v_n_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lake_PackageConfig_testDriver_instConfigField(v_p_1681_, v_n_1682_);
lean_dec(v_n_1682_);
lean_dec(v_p_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object* v_p_1684_, lean_object* v_n_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lake_PackageConfig_testDriver___proj(v_p_1684_, v_n_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object* v_p_1687_, lean_object* v_n_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lake_PackageConfig_testRunner_instConfigField(v_p_1687_, v_n_1688_);
lean_dec(v_n_1688_);
lean_dec(v_p_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0(lean_object* v_cfg_1690_){
_start:
{
lean_object* v_testDriverArgs_1691_; 
v_testDriverArgs_1691_ = lean_ctor_get(v_cfg_1690_, 13);
lean_inc_ref(v_testDriverArgs_1691_);
return v_testDriverArgs_1691_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lake_PackageConfig_testDriverArgs___proj___lam__0(v_cfg_1692_);
lean_dec_ref(v_cfg_1692_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__1(lean_object* v_val_1694_, lean_object* v_cfg_1695_){
_start:
{
lean_object* v_toWorkspaceConfig_1696_; lean_object* v_toLeanConfig_1697_; uint8_t v_bootstrap_1698_; lean_object* v_extraDepTargets_1699_; uint8_t v_precompileModules_1700_; lean_object* v_moreGlobalServerArgs_1701_; lean_object* v_srcDir_1702_; lean_object* v_buildDir_1703_; lean_object* v_leanLibDir_1704_; lean_object* v_nativeLibDir_1705_; lean_object* v_binDir_1706_; lean_object* v_irDir_1707_; lean_object* v_releaseRepo_1708_; lean_object* v_buildArchive_1709_; uint8_t v_preferReleaseBuild_1710_; lean_object* v_testDriver_1711_; lean_object* v_lintDriver_1712_; lean_object* v_lintDriverArgs_1713_; lean_object* v_version_1714_; lean_object* v_versionTags_1715_; lean_object* v_description_1716_; lean_object* v_keywords_1717_; lean_object* v_homepage_1718_; lean_object* v_license_1719_; lean_object* v_licenseFiles_1720_; lean_object* v_readmeFile_1721_; uint8_t v_reservoir_1722_; lean_object* v_enableArtifactCache_x3f_1723_; lean_object* v_restoreAllArtifacts_x3f_1724_; uint8_t v_libPrefixOnWindows_1725_; uint8_t v_allowImportAll_1726_; uint8_t v_fixedToolchain_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_toWorkspaceConfig_1696_ = lean_ctor_get(v_cfg_1695_, 0);
v_toLeanConfig_1697_ = lean_ctor_get(v_cfg_1695_, 1);
v_bootstrap_1698_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*26);
v_extraDepTargets_1699_ = lean_ctor_get(v_cfg_1695_, 2);
v_precompileModules_1700_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1701_ = lean_ctor_get(v_cfg_1695_, 3);
v_srcDir_1702_ = lean_ctor_get(v_cfg_1695_, 4);
v_buildDir_1703_ = lean_ctor_get(v_cfg_1695_, 5);
v_leanLibDir_1704_ = lean_ctor_get(v_cfg_1695_, 6);
v_nativeLibDir_1705_ = lean_ctor_get(v_cfg_1695_, 7);
v_binDir_1706_ = lean_ctor_get(v_cfg_1695_, 8);
v_irDir_1707_ = lean_ctor_get(v_cfg_1695_, 9);
v_releaseRepo_1708_ = lean_ctor_get(v_cfg_1695_, 10);
v_buildArchive_1709_ = lean_ctor_get(v_cfg_1695_, 11);
v_preferReleaseBuild_1710_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*26 + 2);
v_testDriver_1711_ = lean_ctor_get(v_cfg_1695_, 12);
v_lintDriver_1712_ = lean_ctor_get(v_cfg_1695_, 14);
v_lintDriverArgs_1713_ = lean_ctor_get(v_cfg_1695_, 15);
v_version_1714_ = lean_ctor_get(v_cfg_1695_, 16);
v_versionTags_1715_ = lean_ctor_get(v_cfg_1695_, 17);
v_description_1716_ = lean_ctor_get(v_cfg_1695_, 18);
v_keywords_1717_ = lean_ctor_get(v_cfg_1695_, 19);
v_homepage_1718_ = lean_ctor_get(v_cfg_1695_, 20);
v_license_1719_ = lean_ctor_get(v_cfg_1695_, 21);
v_licenseFiles_1720_ = lean_ctor_get(v_cfg_1695_, 22);
v_readmeFile_1721_ = lean_ctor_get(v_cfg_1695_, 23);
v_reservoir_1722_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1723_ = lean_ctor_get(v_cfg_1695_, 24);
v_restoreAllArtifacts_x3f_1724_ = lean_ctor_get(v_cfg_1695_, 25);
v_libPrefixOnWindows_1725_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*26 + 4);
v_allowImportAll_1726_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*26 + 5);
v_fixedToolchain_1727_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*26 + 6);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_cfg_1695_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v_cfg_1695_, 13);
lean_dec(v_unused_1735_);
v___x_1729_ = v_cfg_1695_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1724_);
lean_inc(v_enableArtifactCache_x3f_1723_);
lean_inc(v_readmeFile_1721_);
lean_inc(v_licenseFiles_1720_);
lean_inc(v_license_1719_);
lean_inc(v_homepage_1718_);
lean_inc(v_keywords_1717_);
lean_inc(v_description_1716_);
lean_inc(v_versionTags_1715_);
lean_inc(v_version_1714_);
lean_inc(v_lintDriverArgs_1713_);
lean_inc(v_lintDriver_1712_);
lean_inc(v_testDriver_1711_);
lean_inc(v_buildArchive_1709_);
lean_inc(v_releaseRepo_1708_);
lean_inc(v_irDir_1707_);
lean_inc(v_binDir_1706_);
lean_inc(v_nativeLibDir_1705_);
lean_inc(v_leanLibDir_1704_);
lean_inc(v_buildDir_1703_);
lean_inc(v_srcDir_1702_);
lean_inc(v_moreGlobalServerArgs_1701_);
lean_inc(v_extraDepTargets_1699_);
lean_inc(v_toLeanConfig_1697_);
lean_inc(v_toWorkspaceConfig_1696_);
lean_dec(v_cfg_1695_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 13, v_val_1694_);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_toWorkspaceConfig_1696_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_toLeanConfig_1697_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_extraDepTargets_1699_);
lean_ctor_set(v_reuseFailAlloc_1733_, 3, v_moreGlobalServerArgs_1701_);
lean_ctor_set(v_reuseFailAlloc_1733_, 4, v_srcDir_1702_);
lean_ctor_set(v_reuseFailAlloc_1733_, 5, v_buildDir_1703_);
lean_ctor_set(v_reuseFailAlloc_1733_, 6, v_leanLibDir_1704_);
lean_ctor_set(v_reuseFailAlloc_1733_, 7, v_nativeLibDir_1705_);
lean_ctor_set(v_reuseFailAlloc_1733_, 8, v_binDir_1706_);
lean_ctor_set(v_reuseFailAlloc_1733_, 9, v_irDir_1707_);
lean_ctor_set(v_reuseFailAlloc_1733_, 10, v_releaseRepo_1708_);
lean_ctor_set(v_reuseFailAlloc_1733_, 11, v_buildArchive_1709_);
lean_ctor_set(v_reuseFailAlloc_1733_, 12, v_testDriver_1711_);
lean_ctor_set(v_reuseFailAlloc_1733_, 13, v_val_1694_);
lean_ctor_set(v_reuseFailAlloc_1733_, 14, v_lintDriver_1712_);
lean_ctor_set(v_reuseFailAlloc_1733_, 15, v_lintDriverArgs_1713_);
lean_ctor_set(v_reuseFailAlloc_1733_, 16, v_version_1714_);
lean_ctor_set(v_reuseFailAlloc_1733_, 17, v_versionTags_1715_);
lean_ctor_set(v_reuseFailAlloc_1733_, 18, v_description_1716_);
lean_ctor_set(v_reuseFailAlloc_1733_, 19, v_keywords_1717_);
lean_ctor_set(v_reuseFailAlloc_1733_, 20, v_homepage_1718_);
lean_ctor_set(v_reuseFailAlloc_1733_, 21, v_license_1719_);
lean_ctor_set(v_reuseFailAlloc_1733_, 22, v_licenseFiles_1720_);
lean_ctor_set(v_reuseFailAlloc_1733_, 23, v_readmeFile_1721_);
lean_ctor_set(v_reuseFailAlloc_1733_, 24, v_enableArtifactCache_x3f_1723_);
lean_ctor_set(v_reuseFailAlloc_1733_, 25, v_restoreAllArtifacts_x3f_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*26, v_bootstrap_1698_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*26 + 1, v_precompileModules_1700_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1710_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*26 + 3, v_reservoir_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1725_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*26 + 5, v_allowImportAll_1726_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*26 + 6, v_fixedToolchain_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__2(lean_object* v_f_1736_, lean_object* v_cfg_1737_){
_start:
{
lean_object* v_toWorkspaceConfig_1738_; lean_object* v_toLeanConfig_1739_; uint8_t v_bootstrap_1740_; lean_object* v_extraDepTargets_1741_; uint8_t v_precompileModules_1742_; lean_object* v_moreGlobalServerArgs_1743_; lean_object* v_srcDir_1744_; lean_object* v_buildDir_1745_; lean_object* v_leanLibDir_1746_; lean_object* v_nativeLibDir_1747_; lean_object* v_binDir_1748_; lean_object* v_irDir_1749_; lean_object* v_releaseRepo_1750_; lean_object* v_buildArchive_1751_; uint8_t v_preferReleaseBuild_1752_; lean_object* v_testDriver_1753_; lean_object* v_testDriverArgs_1754_; lean_object* v_lintDriver_1755_; lean_object* v_lintDriverArgs_1756_; lean_object* v_version_1757_; lean_object* v_versionTags_1758_; lean_object* v_description_1759_; lean_object* v_keywords_1760_; lean_object* v_homepage_1761_; lean_object* v_license_1762_; lean_object* v_licenseFiles_1763_; lean_object* v_readmeFile_1764_; uint8_t v_reservoir_1765_; lean_object* v_enableArtifactCache_x3f_1766_; lean_object* v_restoreAllArtifacts_x3f_1767_; uint8_t v_libPrefixOnWindows_1768_; uint8_t v_allowImportAll_1769_; uint8_t v_fixedToolchain_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1778_; 
v_toWorkspaceConfig_1738_ = lean_ctor_get(v_cfg_1737_, 0);
v_toLeanConfig_1739_ = lean_ctor_get(v_cfg_1737_, 1);
v_bootstrap_1740_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*26);
v_extraDepTargets_1741_ = lean_ctor_get(v_cfg_1737_, 2);
v_precompileModules_1742_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1743_ = lean_ctor_get(v_cfg_1737_, 3);
v_srcDir_1744_ = lean_ctor_get(v_cfg_1737_, 4);
v_buildDir_1745_ = lean_ctor_get(v_cfg_1737_, 5);
v_leanLibDir_1746_ = lean_ctor_get(v_cfg_1737_, 6);
v_nativeLibDir_1747_ = lean_ctor_get(v_cfg_1737_, 7);
v_binDir_1748_ = lean_ctor_get(v_cfg_1737_, 8);
v_irDir_1749_ = lean_ctor_get(v_cfg_1737_, 9);
v_releaseRepo_1750_ = lean_ctor_get(v_cfg_1737_, 10);
v_buildArchive_1751_ = lean_ctor_get(v_cfg_1737_, 11);
v_preferReleaseBuild_1752_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*26 + 2);
v_testDriver_1753_ = lean_ctor_get(v_cfg_1737_, 12);
v_testDriverArgs_1754_ = lean_ctor_get(v_cfg_1737_, 13);
v_lintDriver_1755_ = lean_ctor_get(v_cfg_1737_, 14);
v_lintDriverArgs_1756_ = lean_ctor_get(v_cfg_1737_, 15);
v_version_1757_ = lean_ctor_get(v_cfg_1737_, 16);
v_versionTags_1758_ = lean_ctor_get(v_cfg_1737_, 17);
v_description_1759_ = lean_ctor_get(v_cfg_1737_, 18);
v_keywords_1760_ = lean_ctor_get(v_cfg_1737_, 19);
v_homepage_1761_ = lean_ctor_get(v_cfg_1737_, 20);
v_license_1762_ = lean_ctor_get(v_cfg_1737_, 21);
v_licenseFiles_1763_ = lean_ctor_get(v_cfg_1737_, 22);
v_readmeFile_1764_ = lean_ctor_get(v_cfg_1737_, 23);
v_reservoir_1765_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1766_ = lean_ctor_get(v_cfg_1737_, 24);
v_restoreAllArtifacts_x3f_1767_ = lean_ctor_get(v_cfg_1737_, 25);
v_libPrefixOnWindows_1768_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*26 + 4);
v_allowImportAll_1769_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*26 + 5);
v_fixedToolchain_1770_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*26 + 6);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_cfg_1737_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1772_ = v_cfg_1737_;
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1767_);
lean_inc(v_enableArtifactCache_x3f_1766_);
lean_inc(v_readmeFile_1764_);
lean_inc(v_licenseFiles_1763_);
lean_inc(v_license_1762_);
lean_inc(v_homepage_1761_);
lean_inc(v_keywords_1760_);
lean_inc(v_description_1759_);
lean_inc(v_versionTags_1758_);
lean_inc(v_version_1757_);
lean_inc(v_lintDriverArgs_1756_);
lean_inc(v_lintDriver_1755_);
lean_inc(v_testDriverArgs_1754_);
lean_inc(v_testDriver_1753_);
lean_inc(v_buildArchive_1751_);
lean_inc(v_releaseRepo_1750_);
lean_inc(v_irDir_1749_);
lean_inc(v_binDir_1748_);
lean_inc(v_nativeLibDir_1747_);
lean_inc(v_leanLibDir_1746_);
lean_inc(v_buildDir_1745_);
lean_inc(v_srcDir_1744_);
lean_inc(v_moreGlobalServerArgs_1743_);
lean_inc(v_extraDepTargets_1741_);
lean_inc(v_toLeanConfig_1739_);
lean_inc(v_toWorkspaceConfig_1738_);
lean_dec(v_cfg_1737_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1774_ = lean_apply_1(v_f_1736_, v_testDriverArgs_1754_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 13, v___x_1774_);
v___x_1776_ = v___x_1772_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_toWorkspaceConfig_1738_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_toLeanConfig_1739_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_extraDepTargets_1741_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v_moreGlobalServerArgs_1743_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v_srcDir_1744_);
lean_ctor_set(v_reuseFailAlloc_1777_, 5, v_buildDir_1745_);
lean_ctor_set(v_reuseFailAlloc_1777_, 6, v_leanLibDir_1746_);
lean_ctor_set(v_reuseFailAlloc_1777_, 7, v_nativeLibDir_1747_);
lean_ctor_set(v_reuseFailAlloc_1777_, 8, v_binDir_1748_);
lean_ctor_set(v_reuseFailAlloc_1777_, 9, v_irDir_1749_);
lean_ctor_set(v_reuseFailAlloc_1777_, 10, v_releaseRepo_1750_);
lean_ctor_set(v_reuseFailAlloc_1777_, 11, v_buildArchive_1751_);
lean_ctor_set(v_reuseFailAlloc_1777_, 12, v_testDriver_1753_);
lean_ctor_set(v_reuseFailAlloc_1777_, 13, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1777_, 14, v_lintDriver_1755_);
lean_ctor_set(v_reuseFailAlloc_1777_, 15, v_lintDriverArgs_1756_);
lean_ctor_set(v_reuseFailAlloc_1777_, 16, v_version_1757_);
lean_ctor_set(v_reuseFailAlloc_1777_, 17, v_versionTags_1758_);
lean_ctor_set(v_reuseFailAlloc_1777_, 18, v_description_1759_);
lean_ctor_set(v_reuseFailAlloc_1777_, 19, v_keywords_1760_);
lean_ctor_set(v_reuseFailAlloc_1777_, 20, v_homepage_1761_);
lean_ctor_set(v_reuseFailAlloc_1777_, 21, v_license_1762_);
lean_ctor_set(v_reuseFailAlloc_1777_, 22, v_licenseFiles_1763_);
lean_ctor_set(v_reuseFailAlloc_1777_, 23, v_readmeFile_1764_);
lean_ctor_set(v_reuseFailAlloc_1777_, 24, v_enableArtifactCache_x3f_1766_);
lean_ctor_set(v_reuseFailAlloc_1777_, 25, v_restoreAllArtifacts_x3f_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*26, v_bootstrap_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*26 + 1, v_precompileModules_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*26 + 3, v_reservoir_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1768_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*26 + 5, v_allowImportAll_1769_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*26 + 6, v_fixedToolchain_1770_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object* v_p_1787_, lean_object* v_n_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = ((lean_object*)(l_Lake_PackageConfig_testDriverArgs___proj___closed__3));
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object* v_p_1790_, lean_object* v_n_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1790_, v_n_1791_);
lean_dec(v_n_1791_);
lean_dec(v_p_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object* v_p_1793_, lean_object* v_n_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1793_, v_n_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object* v_p_1796_, lean_object* v_n_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lake_PackageConfig_testDriverArgs_instConfigField(v_p_1796_, v_n_1797_);
lean_dec(v_n_1797_);
lean_dec(v_p_1796_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0(lean_object* v_cfg_1799_){
_start:
{
lean_object* v_lintDriver_1800_; 
v_lintDriver_1800_ = lean_ctor_get(v_cfg_1799_, 14);
lean_inc_ref(v_lintDriver_1800_);
return v_lintDriver_1800_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0___boxed(lean_object* v_cfg_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lake_PackageConfig_lintDriver___proj___lam__0(v_cfg_1801_);
lean_dec_ref(v_cfg_1801_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__1(lean_object* v_val_1803_, lean_object* v_cfg_1804_){
_start:
{
lean_object* v_toWorkspaceConfig_1805_; lean_object* v_toLeanConfig_1806_; uint8_t v_bootstrap_1807_; lean_object* v_extraDepTargets_1808_; uint8_t v_precompileModules_1809_; lean_object* v_moreGlobalServerArgs_1810_; lean_object* v_srcDir_1811_; lean_object* v_buildDir_1812_; lean_object* v_leanLibDir_1813_; lean_object* v_nativeLibDir_1814_; lean_object* v_binDir_1815_; lean_object* v_irDir_1816_; lean_object* v_releaseRepo_1817_; lean_object* v_buildArchive_1818_; uint8_t v_preferReleaseBuild_1819_; lean_object* v_testDriver_1820_; lean_object* v_testDriverArgs_1821_; lean_object* v_lintDriverArgs_1822_; lean_object* v_version_1823_; lean_object* v_versionTags_1824_; lean_object* v_description_1825_; lean_object* v_keywords_1826_; lean_object* v_homepage_1827_; lean_object* v_license_1828_; lean_object* v_licenseFiles_1829_; lean_object* v_readmeFile_1830_; uint8_t v_reservoir_1831_; lean_object* v_enableArtifactCache_x3f_1832_; lean_object* v_restoreAllArtifacts_x3f_1833_; uint8_t v_libPrefixOnWindows_1834_; uint8_t v_allowImportAll_1835_; uint8_t v_fixedToolchain_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_toWorkspaceConfig_1805_ = lean_ctor_get(v_cfg_1804_, 0);
v_toLeanConfig_1806_ = lean_ctor_get(v_cfg_1804_, 1);
v_bootstrap_1807_ = lean_ctor_get_uint8(v_cfg_1804_, sizeof(void*)*26);
v_extraDepTargets_1808_ = lean_ctor_get(v_cfg_1804_, 2);
v_precompileModules_1809_ = lean_ctor_get_uint8(v_cfg_1804_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1810_ = lean_ctor_get(v_cfg_1804_, 3);
v_srcDir_1811_ = lean_ctor_get(v_cfg_1804_, 4);
v_buildDir_1812_ = lean_ctor_get(v_cfg_1804_, 5);
v_leanLibDir_1813_ = lean_ctor_get(v_cfg_1804_, 6);
v_nativeLibDir_1814_ = lean_ctor_get(v_cfg_1804_, 7);
v_binDir_1815_ = lean_ctor_get(v_cfg_1804_, 8);
v_irDir_1816_ = lean_ctor_get(v_cfg_1804_, 9);
v_releaseRepo_1817_ = lean_ctor_get(v_cfg_1804_, 10);
v_buildArchive_1818_ = lean_ctor_get(v_cfg_1804_, 11);
v_preferReleaseBuild_1819_ = lean_ctor_get_uint8(v_cfg_1804_, sizeof(void*)*26 + 2);
v_testDriver_1820_ = lean_ctor_get(v_cfg_1804_, 12);
v_testDriverArgs_1821_ = lean_ctor_get(v_cfg_1804_, 13);
v_lintDriverArgs_1822_ = lean_ctor_get(v_cfg_1804_, 15);
v_version_1823_ = lean_ctor_get(v_cfg_1804_, 16);
v_versionTags_1824_ = lean_ctor_get(v_cfg_1804_, 17);
v_description_1825_ = lean_ctor_get(v_cfg_1804_, 18);
v_keywords_1826_ = lean_ctor_get(v_cfg_1804_, 19);
v_homepage_1827_ = lean_ctor_get(v_cfg_1804_, 20);
v_license_1828_ = lean_ctor_get(v_cfg_1804_, 21);
v_licenseFiles_1829_ = lean_ctor_get(v_cfg_1804_, 22);
v_readmeFile_1830_ = lean_ctor_get(v_cfg_1804_, 23);
v_reservoir_1831_ = lean_ctor_get_uint8(v_cfg_1804_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1832_ = lean_ctor_get(v_cfg_1804_, 24);
v_restoreAllArtifacts_x3f_1833_ = lean_ctor_get(v_cfg_1804_, 25);
v_libPrefixOnWindows_1834_ = lean_ctor_get_uint8(v_cfg_1804_, sizeof(void*)*26 + 4);
v_allowImportAll_1835_ = lean_ctor_get_uint8(v_cfg_1804_, sizeof(void*)*26 + 5);
v_fixedToolchain_1836_ = lean_ctor_get_uint8(v_cfg_1804_, sizeof(void*)*26 + 6);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_cfg_1804_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v_cfg_1804_, 14);
lean_dec(v_unused_1844_);
v___x_1838_ = v_cfg_1804_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1833_);
lean_inc(v_enableArtifactCache_x3f_1832_);
lean_inc(v_readmeFile_1830_);
lean_inc(v_licenseFiles_1829_);
lean_inc(v_license_1828_);
lean_inc(v_homepage_1827_);
lean_inc(v_keywords_1826_);
lean_inc(v_description_1825_);
lean_inc(v_versionTags_1824_);
lean_inc(v_version_1823_);
lean_inc(v_lintDriverArgs_1822_);
lean_inc(v_testDriverArgs_1821_);
lean_inc(v_testDriver_1820_);
lean_inc(v_buildArchive_1818_);
lean_inc(v_releaseRepo_1817_);
lean_inc(v_irDir_1816_);
lean_inc(v_binDir_1815_);
lean_inc(v_nativeLibDir_1814_);
lean_inc(v_leanLibDir_1813_);
lean_inc(v_buildDir_1812_);
lean_inc(v_srcDir_1811_);
lean_inc(v_moreGlobalServerArgs_1810_);
lean_inc(v_extraDepTargets_1808_);
lean_inc(v_toLeanConfig_1806_);
lean_inc(v_toWorkspaceConfig_1805_);
lean_dec(v_cfg_1804_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 14, v_val_1803_);
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_toWorkspaceConfig_1805_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_toLeanConfig_1806_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_extraDepTargets_1808_);
lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_moreGlobalServerArgs_1810_);
lean_ctor_set(v_reuseFailAlloc_1842_, 4, v_srcDir_1811_);
lean_ctor_set(v_reuseFailAlloc_1842_, 5, v_buildDir_1812_);
lean_ctor_set(v_reuseFailAlloc_1842_, 6, v_leanLibDir_1813_);
lean_ctor_set(v_reuseFailAlloc_1842_, 7, v_nativeLibDir_1814_);
lean_ctor_set(v_reuseFailAlloc_1842_, 8, v_binDir_1815_);
lean_ctor_set(v_reuseFailAlloc_1842_, 9, v_irDir_1816_);
lean_ctor_set(v_reuseFailAlloc_1842_, 10, v_releaseRepo_1817_);
lean_ctor_set(v_reuseFailAlloc_1842_, 11, v_buildArchive_1818_);
lean_ctor_set(v_reuseFailAlloc_1842_, 12, v_testDriver_1820_);
lean_ctor_set(v_reuseFailAlloc_1842_, 13, v_testDriverArgs_1821_);
lean_ctor_set(v_reuseFailAlloc_1842_, 14, v_val_1803_);
lean_ctor_set(v_reuseFailAlloc_1842_, 15, v_lintDriverArgs_1822_);
lean_ctor_set(v_reuseFailAlloc_1842_, 16, v_version_1823_);
lean_ctor_set(v_reuseFailAlloc_1842_, 17, v_versionTags_1824_);
lean_ctor_set(v_reuseFailAlloc_1842_, 18, v_description_1825_);
lean_ctor_set(v_reuseFailAlloc_1842_, 19, v_keywords_1826_);
lean_ctor_set(v_reuseFailAlloc_1842_, 20, v_homepage_1827_);
lean_ctor_set(v_reuseFailAlloc_1842_, 21, v_license_1828_);
lean_ctor_set(v_reuseFailAlloc_1842_, 22, v_licenseFiles_1829_);
lean_ctor_set(v_reuseFailAlloc_1842_, 23, v_readmeFile_1830_);
lean_ctor_set(v_reuseFailAlloc_1842_, 24, v_enableArtifactCache_x3f_1832_);
lean_ctor_set(v_reuseFailAlloc_1842_, 25, v_restoreAllArtifacts_x3f_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*26, v_bootstrap_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*26 + 1, v_precompileModules_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*26 + 3, v_reservoir_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*26 + 5, v_allowImportAll_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*26 + 6, v_fixedToolchain_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__2(lean_object* v_f_1845_, lean_object* v_cfg_1846_){
_start:
{
lean_object* v_toWorkspaceConfig_1847_; lean_object* v_toLeanConfig_1848_; uint8_t v_bootstrap_1849_; lean_object* v_extraDepTargets_1850_; uint8_t v_precompileModules_1851_; lean_object* v_moreGlobalServerArgs_1852_; lean_object* v_srcDir_1853_; lean_object* v_buildDir_1854_; lean_object* v_leanLibDir_1855_; lean_object* v_nativeLibDir_1856_; lean_object* v_binDir_1857_; lean_object* v_irDir_1858_; lean_object* v_releaseRepo_1859_; lean_object* v_buildArchive_1860_; uint8_t v_preferReleaseBuild_1861_; lean_object* v_testDriver_1862_; lean_object* v_testDriverArgs_1863_; lean_object* v_lintDriver_1864_; lean_object* v_lintDriverArgs_1865_; lean_object* v_version_1866_; lean_object* v_versionTags_1867_; lean_object* v_description_1868_; lean_object* v_keywords_1869_; lean_object* v_homepage_1870_; lean_object* v_license_1871_; lean_object* v_licenseFiles_1872_; lean_object* v_readmeFile_1873_; uint8_t v_reservoir_1874_; lean_object* v_enableArtifactCache_x3f_1875_; lean_object* v_restoreAllArtifacts_x3f_1876_; uint8_t v_libPrefixOnWindows_1877_; uint8_t v_allowImportAll_1878_; uint8_t v_fixedToolchain_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1887_; 
v_toWorkspaceConfig_1847_ = lean_ctor_get(v_cfg_1846_, 0);
v_toLeanConfig_1848_ = lean_ctor_get(v_cfg_1846_, 1);
v_bootstrap_1849_ = lean_ctor_get_uint8(v_cfg_1846_, sizeof(void*)*26);
v_extraDepTargets_1850_ = lean_ctor_get(v_cfg_1846_, 2);
v_precompileModules_1851_ = lean_ctor_get_uint8(v_cfg_1846_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1852_ = lean_ctor_get(v_cfg_1846_, 3);
v_srcDir_1853_ = lean_ctor_get(v_cfg_1846_, 4);
v_buildDir_1854_ = lean_ctor_get(v_cfg_1846_, 5);
v_leanLibDir_1855_ = lean_ctor_get(v_cfg_1846_, 6);
v_nativeLibDir_1856_ = lean_ctor_get(v_cfg_1846_, 7);
v_binDir_1857_ = lean_ctor_get(v_cfg_1846_, 8);
v_irDir_1858_ = lean_ctor_get(v_cfg_1846_, 9);
v_releaseRepo_1859_ = lean_ctor_get(v_cfg_1846_, 10);
v_buildArchive_1860_ = lean_ctor_get(v_cfg_1846_, 11);
v_preferReleaseBuild_1861_ = lean_ctor_get_uint8(v_cfg_1846_, sizeof(void*)*26 + 2);
v_testDriver_1862_ = lean_ctor_get(v_cfg_1846_, 12);
v_testDriverArgs_1863_ = lean_ctor_get(v_cfg_1846_, 13);
v_lintDriver_1864_ = lean_ctor_get(v_cfg_1846_, 14);
v_lintDriverArgs_1865_ = lean_ctor_get(v_cfg_1846_, 15);
v_version_1866_ = lean_ctor_get(v_cfg_1846_, 16);
v_versionTags_1867_ = lean_ctor_get(v_cfg_1846_, 17);
v_description_1868_ = lean_ctor_get(v_cfg_1846_, 18);
v_keywords_1869_ = lean_ctor_get(v_cfg_1846_, 19);
v_homepage_1870_ = lean_ctor_get(v_cfg_1846_, 20);
v_license_1871_ = lean_ctor_get(v_cfg_1846_, 21);
v_licenseFiles_1872_ = lean_ctor_get(v_cfg_1846_, 22);
v_readmeFile_1873_ = lean_ctor_get(v_cfg_1846_, 23);
v_reservoir_1874_ = lean_ctor_get_uint8(v_cfg_1846_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1875_ = lean_ctor_get(v_cfg_1846_, 24);
v_restoreAllArtifacts_x3f_1876_ = lean_ctor_get(v_cfg_1846_, 25);
v_libPrefixOnWindows_1877_ = lean_ctor_get_uint8(v_cfg_1846_, sizeof(void*)*26 + 4);
v_allowImportAll_1878_ = lean_ctor_get_uint8(v_cfg_1846_, sizeof(void*)*26 + 5);
v_fixedToolchain_1879_ = lean_ctor_get_uint8(v_cfg_1846_, sizeof(void*)*26 + 6);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_cfg_1846_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1881_ = v_cfg_1846_;
v_isShared_1882_ = v_isSharedCheck_1887_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1876_);
lean_inc(v_enableArtifactCache_x3f_1875_);
lean_inc(v_readmeFile_1873_);
lean_inc(v_licenseFiles_1872_);
lean_inc(v_license_1871_);
lean_inc(v_homepage_1870_);
lean_inc(v_keywords_1869_);
lean_inc(v_description_1868_);
lean_inc(v_versionTags_1867_);
lean_inc(v_version_1866_);
lean_inc(v_lintDriverArgs_1865_);
lean_inc(v_lintDriver_1864_);
lean_inc(v_testDriverArgs_1863_);
lean_inc(v_testDriver_1862_);
lean_inc(v_buildArchive_1860_);
lean_inc(v_releaseRepo_1859_);
lean_inc(v_irDir_1858_);
lean_inc(v_binDir_1857_);
lean_inc(v_nativeLibDir_1856_);
lean_inc(v_leanLibDir_1855_);
lean_inc(v_buildDir_1854_);
lean_inc(v_srcDir_1853_);
lean_inc(v_moreGlobalServerArgs_1852_);
lean_inc(v_extraDepTargets_1850_);
lean_inc(v_toLeanConfig_1848_);
lean_inc(v_toWorkspaceConfig_1847_);
lean_dec(v_cfg_1846_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1887_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = lean_apply_1(v_f_1845_, v_lintDriver_1864_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 14, v___x_1883_);
v___x_1885_ = v___x_1881_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_toWorkspaceConfig_1847_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_toLeanConfig_1848_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v_extraDepTargets_1850_);
lean_ctor_set(v_reuseFailAlloc_1886_, 3, v_moreGlobalServerArgs_1852_);
lean_ctor_set(v_reuseFailAlloc_1886_, 4, v_srcDir_1853_);
lean_ctor_set(v_reuseFailAlloc_1886_, 5, v_buildDir_1854_);
lean_ctor_set(v_reuseFailAlloc_1886_, 6, v_leanLibDir_1855_);
lean_ctor_set(v_reuseFailAlloc_1886_, 7, v_nativeLibDir_1856_);
lean_ctor_set(v_reuseFailAlloc_1886_, 8, v_binDir_1857_);
lean_ctor_set(v_reuseFailAlloc_1886_, 9, v_irDir_1858_);
lean_ctor_set(v_reuseFailAlloc_1886_, 10, v_releaseRepo_1859_);
lean_ctor_set(v_reuseFailAlloc_1886_, 11, v_buildArchive_1860_);
lean_ctor_set(v_reuseFailAlloc_1886_, 12, v_testDriver_1862_);
lean_ctor_set(v_reuseFailAlloc_1886_, 13, v_testDriverArgs_1863_);
lean_ctor_set(v_reuseFailAlloc_1886_, 14, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1886_, 15, v_lintDriverArgs_1865_);
lean_ctor_set(v_reuseFailAlloc_1886_, 16, v_version_1866_);
lean_ctor_set(v_reuseFailAlloc_1886_, 17, v_versionTags_1867_);
lean_ctor_set(v_reuseFailAlloc_1886_, 18, v_description_1868_);
lean_ctor_set(v_reuseFailAlloc_1886_, 19, v_keywords_1869_);
lean_ctor_set(v_reuseFailAlloc_1886_, 20, v_homepage_1870_);
lean_ctor_set(v_reuseFailAlloc_1886_, 21, v_license_1871_);
lean_ctor_set(v_reuseFailAlloc_1886_, 22, v_licenseFiles_1872_);
lean_ctor_set(v_reuseFailAlloc_1886_, 23, v_readmeFile_1873_);
lean_ctor_set(v_reuseFailAlloc_1886_, 24, v_enableArtifactCache_x3f_1875_);
lean_ctor_set(v_reuseFailAlloc_1886_, 25, v_restoreAllArtifacts_x3f_1876_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*26, v_bootstrap_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*26 + 1, v_precompileModules_1851_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1861_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*26 + 3, v_reservoir_1874_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1877_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*26 + 5, v_allowImportAll_1878_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*26 + 6, v_fixedToolchain_1879_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object* v_p_1896_, lean_object* v_n_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = ((lean_object*)(l_Lake_PackageConfig_lintDriver___proj___closed__3));
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object* v_p_1899_, lean_object* v_n_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1899_, v_n_1900_);
lean_dec(v_n_1900_);
lean_dec(v_p_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object* v_p_1902_, lean_object* v_n_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1902_, v_n_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object* v_p_1905_, lean_object* v_n_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lake_PackageConfig_lintDriver_instConfigField(v_p_1905_, v_n_1906_);
lean_dec(v_n_1906_);
lean_dec(v_p_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(lean_object* v_cfg_1908_){
_start:
{
lean_object* v_lintDriverArgs_1909_; 
v_lintDriverArgs_1909_ = lean_ctor_get(v_cfg_1908_, 15);
lean_inc_ref(v_lintDriverArgs_1909_);
return v_lintDriverArgs_1909_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(v_cfg_1910_);
lean_dec_ref(v_cfg_1910_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__1(lean_object* v_val_1912_, lean_object* v_cfg_1913_){
_start:
{
lean_object* v_toWorkspaceConfig_1914_; lean_object* v_toLeanConfig_1915_; uint8_t v_bootstrap_1916_; lean_object* v_extraDepTargets_1917_; uint8_t v_precompileModules_1918_; lean_object* v_moreGlobalServerArgs_1919_; lean_object* v_srcDir_1920_; lean_object* v_buildDir_1921_; lean_object* v_leanLibDir_1922_; lean_object* v_nativeLibDir_1923_; lean_object* v_binDir_1924_; lean_object* v_irDir_1925_; lean_object* v_releaseRepo_1926_; lean_object* v_buildArchive_1927_; uint8_t v_preferReleaseBuild_1928_; lean_object* v_testDriver_1929_; lean_object* v_testDriverArgs_1930_; lean_object* v_lintDriver_1931_; lean_object* v_version_1932_; lean_object* v_versionTags_1933_; lean_object* v_description_1934_; lean_object* v_keywords_1935_; lean_object* v_homepage_1936_; lean_object* v_license_1937_; lean_object* v_licenseFiles_1938_; lean_object* v_readmeFile_1939_; uint8_t v_reservoir_1940_; lean_object* v_enableArtifactCache_x3f_1941_; lean_object* v_restoreAllArtifacts_x3f_1942_; uint8_t v_libPrefixOnWindows_1943_; uint8_t v_allowImportAll_1944_; uint8_t v_fixedToolchain_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_toWorkspaceConfig_1914_ = lean_ctor_get(v_cfg_1913_, 0);
v_toLeanConfig_1915_ = lean_ctor_get(v_cfg_1913_, 1);
v_bootstrap_1916_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*26);
v_extraDepTargets_1917_ = lean_ctor_get(v_cfg_1913_, 2);
v_precompileModules_1918_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1919_ = lean_ctor_get(v_cfg_1913_, 3);
v_srcDir_1920_ = lean_ctor_get(v_cfg_1913_, 4);
v_buildDir_1921_ = lean_ctor_get(v_cfg_1913_, 5);
v_leanLibDir_1922_ = lean_ctor_get(v_cfg_1913_, 6);
v_nativeLibDir_1923_ = lean_ctor_get(v_cfg_1913_, 7);
v_binDir_1924_ = lean_ctor_get(v_cfg_1913_, 8);
v_irDir_1925_ = lean_ctor_get(v_cfg_1913_, 9);
v_releaseRepo_1926_ = lean_ctor_get(v_cfg_1913_, 10);
v_buildArchive_1927_ = lean_ctor_get(v_cfg_1913_, 11);
v_preferReleaseBuild_1928_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*26 + 2);
v_testDriver_1929_ = lean_ctor_get(v_cfg_1913_, 12);
v_testDriverArgs_1930_ = lean_ctor_get(v_cfg_1913_, 13);
v_lintDriver_1931_ = lean_ctor_get(v_cfg_1913_, 14);
v_version_1932_ = lean_ctor_get(v_cfg_1913_, 16);
v_versionTags_1933_ = lean_ctor_get(v_cfg_1913_, 17);
v_description_1934_ = lean_ctor_get(v_cfg_1913_, 18);
v_keywords_1935_ = lean_ctor_get(v_cfg_1913_, 19);
v_homepage_1936_ = lean_ctor_get(v_cfg_1913_, 20);
v_license_1937_ = lean_ctor_get(v_cfg_1913_, 21);
v_licenseFiles_1938_ = lean_ctor_get(v_cfg_1913_, 22);
v_readmeFile_1939_ = lean_ctor_get(v_cfg_1913_, 23);
v_reservoir_1940_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1941_ = lean_ctor_get(v_cfg_1913_, 24);
v_restoreAllArtifacts_x3f_1942_ = lean_ctor_get(v_cfg_1913_, 25);
v_libPrefixOnWindows_1943_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*26 + 4);
v_allowImportAll_1944_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*26 + 5);
v_fixedToolchain_1945_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*26 + 6);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_cfg_1913_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; 
v_unused_1953_ = lean_ctor_get(v_cfg_1913_, 15);
lean_dec(v_unused_1953_);
v___x_1947_ = v_cfg_1913_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1942_);
lean_inc(v_enableArtifactCache_x3f_1941_);
lean_inc(v_readmeFile_1939_);
lean_inc(v_licenseFiles_1938_);
lean_inc(v_license_1937_);
lean_inc(v_homepage_1936_);
lean_inc(v_keywords_1935_);
lean_inc(v_description_1934_);
lean_inc(v_versionTags_1933_);
lean_inc(v_version_1932_);
lean_inc(v_lintDriver_1931_);
lean_inc(v_testDriverArgs_1930_);
lean_inc(v_testDriver_1929_);
lean_inc(v_buildArchive_1927_);
lean_inc(v_releaseRepo_1926_);
lean_inc(v_irDir_1925_);
lean_inc(v_binDir_1924_);
lean_inc(v_nativeLibDir_1923_);
lean_inc(v_leanLibDir_1922_);
lean_inc(v_buildDir_1921_);
lean_inc(v_srcDir_1920_);
lean_inc(v_moreGlobalServerArgs_1919_);
lean_inc(v_extraDepTargets_1917_);
lean_inc(v_toLeanConfig_1915_);
lean_inc(v_toWorkspaceConfig_1914_);
lean_dec(v_cfg_1913_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 15, v_val_1912_);
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_toWorkspaceConfig_1914_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_toLeanConfig_1915_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_extraDepTargets_1917_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_moreGlobalServerArgs_1919_);
lean_ctor_set(v_reuseFailAlloc_1951_, 4, v_srcDir_1920_);
lean_ctor_set(v_reuseFailAlloc_1951_, 5, v_buildDir_1921_);
lean_ctor_set(v_reuseFailAlloc_1951_, 6, v_leanLibDir_1922_);
lean_ctor_set(v_reuseFailAlloc_1951_, 7, v_nativeLibDir_1923_);
lean_ctor_set(v_reuseFailAlloc_1951_, 8, v_binDir_1924_);
lean_ctor_set(v_reuseFailAlloc_1951_, 9, v_irDir_1925_);
lean_ctor_set(v_reuseFailAlloc_1951_, 10, v_releaseRepo_1926_);
lean_ctor_set(v_reuseFailAlloc_1951_, 11, v_buildArchive_1927_);
lean_ctor_set(v_reuseFailAlloc_1951_, 12, v_testDriver_1929_);
lean_ctor_set(v_reuseFailAlloc_1951_, 13, v_testDriverArgs_1930_);
lean_ctor_set(v_reuseFailAlloc_1951_, 14, v_lintDriver_1931_);
lean_ctor_set(v_reuseFailAlloc_1951_, 15, v_val_1912_);
lean_ctor_set(v_reuseFailAlloc_1951_, 16, v_version_1932_);
lean_ctor_set(v_reuseFailAlloc_1951_, 17, v_versionTags_1933_);
lean_ctor_set(v_reuseFailAlloc_1951_, 18, v_description_1934_);
lean_ctor_set(v_reuseFailAlloc_1951_, 19, v_keywords_1935_);
lean_ctor_set(v_reuseFailAlloc_1951_, 20, v_homepage_1936_);
lean_ctor_set(v_reuseFailAlloc_1951_, 21, v_license_1937_);
lean_ctor_set(v_reuseFailAlloc_1951_, 22, v_licenseFiles_1938_);
lean_ctor_set(v_reuseFailAlloc_1951_, 23, v_readmeFile_1939_);
lean_ctor_set(v_reuseFailAlloc_1951_, 24, v_enableArtifactCache_x3f_1941_);
lean_ctor_set(v_reuseFailAlloc_1951_, 25, v_restoreAllArtifacts_x3f_1942_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*26, v_bootstrap_1916_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*26 + 1, v_precompileModules_1918_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*26 + 3, v_reservoir_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1943_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*26 + 5, v_allowImportAll_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*26 + 6, v_fixedToolchain_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__2(lean_object* v_f_1954_, lean_object* v_cfg_1955_){
_start:
{
lean_object* v_toWorkspaceConfig_1956_; lean_object* v_toLeanConfig_1957_; uint8_t v_bootstrap_1958_; lean_object* v_extraDepTargets_1959_; uint8_t v_precompileModules_1960_; lean_object* v_moreGlobalServerArgs_1961_; lean_object* v_srcDir_1962_; lean_object* v_buildDir_1963_; lean_object* v_leanLibDir_1964_; lean_object* v_nativeLibDir_1965_; lean_object* v_binDir_1966_; lean_object* v_irDir_1967_; lean_object* v_releaseRepo_1968_; lean_object* v_buildArchive_1969_; uint8_t v_preferReleaseBuild_1970_; lean_object* v_testDriver_1971_; lean_object* v_testDriverArgs_1972_; lean_object* v_lintDriver_1973_; lean_object* v_lintDriverArgs_1974_; lean_object* v_version_1975_; lean_object* v_versionTags_1976_; lean_object* v_description_1977_; lean_object* v_keywords_1978_; lean_object* v_homepage_1979_; lean_object* v_license_1980_; lean_object* v_licenseFiles_1981_; lean_object* v_readmeFile_1982_; uint8_t v_reservoir_1983_; lean_object* v_enableArtifactCache_x3f_1984_; lean_object* v_restoreAllArtifacts_x3f_1985_; uint8_t v_libPrefixOnWindows_1986_; uint8_t v_allowImportAll_1987_; uint8_t v_fixedToolchain_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1996_; 
v_toWorkspaceConfig_1956_ = lean_ctor_get(v_cfg_1955_, 0);
v_toLeanConfig_1957_ = lean_ctor_get(v_cfg_1955_, 1);
v_bootstrap_1958_ = lean_ctor_get_uint8(v_cfg_1955_, sizeof(void*)*26);
v_extraDepTargets_1959_ = lean_ctor_get(v_cfg_1955_, 2);
v_precompileModules_1960_ = lean_ctor_get_uint8(v_cfg_1955_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1961_ = lean_ctor_get(v_cfg_1955_, 3);
v_srcDir_1962_ = lean_ctor_get(v_cfg_1955_, 4);
v_buildDir_1963_ = lean_ctor_get(v_cfg_1955_, 5);
v_leanLibDir_1964_ = lean_ctor_get(v_cfg_1955_, 6);
v_nativeLibDir_1965_ = lean_ctor_get(v_cfg_1955_, 7);
v_binDir_1966_ = lean_ctor_get(v_cfg_1955_, 8);
v_irDir_1967_ = lean_ctor_get(v_cfg_1955_, 9);
v_releaseRepo_1968_ = lean_ctor_get(v_cfg_1955_, 10);
v_buildArchive_1969_ = lean_ctor_get(v_cfg_1955_, 11);
v_preferReleaseBuild_1970_ = lean_ctor_get_uint8(v_cfg_1955_, sizeof(void*)*26 + 2);
v_testDriver_1971_ = lean_ctor_get(v_cfg_1955_, 12);
v_testDriverArgs_1972_ = lean_ctor_get(v_cfg_1955_, 13);
v_lintDriver_1973_ = lean_ctor_get(v_cfg_1955_, 14);
v_lintDriverArgs_1974_ = lean_ctor_get(v_cfg_1955_, 15);
v_version_1975_ = lean_ctor_get(v_cfg_1955_, 16);
v_versionTags_1976_ = lean_ctor_get(v_cfg_1955_, 17);
v_description_1977_ = lean_ctor_get(v_cfg_1955_, 18);
v_keywords_1978_ = lean_ctor_get(v_cfg_1955_, 19);
v_homepage_1979_ = lean_ctor_get(v_cfg_1955_, 20);
v_license_1980_ = lean_ctor_get(v_cfg_1955_, 21);
v_licenseFiles_1981_ = lean_ctor_get(v_cfg_1955_, 22);
v_readmeFile_1982_ = lean_ctor_get(v_cfg_1955_, 23);
v_reservoir_1983_ = lean_ctor_get_uint8(v_cfg_1955_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1984_ = lean_ctor_get(v_cfg_1955_, 24);
v_restoreAllArtifacts_x3f_1985_ = lean_ctor_get(v_cfg_1955_, 25);
v_libPrefixOnWindows_1986_ = lean_ctor_get_uint8(v_cfg_1955_, sizeof(void*)*26 + 4);
v_allowImportAll_1987_ = lean_ctor_get_uint8(v_cfg_1955_, sizeof(void*)*26 + 5);
v_fixedToolchain_1988_ = lean_ctor_get_uint8(v_cfg_1955_, sizeof(void*)*26 + 6);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_cfg_1955_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1990_ = v_cfg_1955_;
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1985_);
lean_inc(v_enableArtifactCache_x3f_1984_);
lean_inc(v_readmeFile_1982_);
lean_inc(v_licenseFiles_1981_);
lean_inc(v_license_1980_);
lean_inc(v_homepage_1979_);
lean_inc(v_keywords_1978_);
lean_inc(v_description_1977_);
lean_inc(v_versionTags_1976_);
lean_inc(v_version_1975_);
lean_inc(v_lintDriverArgs_1974_);
lean_inc(v_lintDriver_1973_);
lean_inc(v_testDriverArgs_1972_);
lean_inc(v_testDriver_1971_);
lean_inc(v_buildArchive_1969_);
lean_inc(v_releaseRepo_1968_);
lean_inc(v_irDir_1967_);
lean_inc(v_binDir_1966_);
lean_inc(v_nativeLibDir_1965_);
lean_inc(v_leanLibDir_1964_);
lean_inc(v_buildDir_1963_);
lean_inc(v_srcDir_1962_);
lean_inc(v_moreGlobalServerArgs_1961_);
lean_inc(v_extraDepTargets_1959_);
lean_inc(v_toLeanConfig_1957_);
lean_inc(v_toWorkspaceConfig_1956_);
lean_dec(v_cfg_1955_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_apply_1(v_f_1954_, v_lintDriverArgs_1974_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 15, v___x_1992_);
v___x_1994_ = v___x_1990_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_toWorkspaceConfig_1956_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_toLeanConfig_1957_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_extraDepTargets_1959_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v_moreGlobalServerArgs_1961_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v_srcDir_1962_);
lean_ctor_set(v_reuseFailAlloc_1995_, 5, v_buildDir_1963_);
lean_ctor_set(v_reuseFailAlloc_1995_, 6, v_leanLibDir_1964_);
lean_ctor_set(v_reuseFailAlloc_1995_, 7, v_nativeLibDir_1965_);
lean_ctor_set(v_reuseFailAlloc_1995_, 8, v_binDir_1966_);
lean_ctor_set(v_reuseFailAlloc_1995_, 9, v_irDir_1967_);
lean_ctor_set(v_reuseFailAlloc_1995_, 10, v_releaseRepo_1968_);
lean_ctor_set(v_reuseFailAlloc_1995_, 11, v_buildArchive_1969_);
lean_ctor_set(v_reuseFailAlloc_1995_, 12, v_testDriver_1971_);
lean_ctor_set(v_reuseFailAlloc_1995_, 13, v_testDriverArgs_1972_);
lean_ctor_set(v_reuseFailAlloc_1995_, 14, v_lintDriver_1973_);
lean_ctor_set(v_reuseFailAlloc_1995_, 15, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_1995_, 16, v_version_1975_);
lean_ctor_set(v_reuseFailAlloc_1995_, 17, v_versionTags_1976_);
lean_ctor_set(v_reuseFailAlloc_1995_, 18, v_description_1977_);
lean_ctor_set(v_reuseFailAlloc_1995_, 19, v_keywords_1978_);
lean_ctor_set(v_reuseFailAlloc_1995_, 20, v_homepage_1979_);
lean_ctor_set(v_reuseFailAlloc_1995_, 21, v_license_1980_);
lean_ctor_set(v_reuseFailAlloc_1995_, 22, v_licenseFiles_1981_);
lean_ctor_set(v_reuseFailAlloc_1995_, 23, v_readmeFile_1982_);
lean_ctor_set(v_reuseFailAlloc_1995_, 24, v_enableArtifactCache_x3f_1984_);
lean_ctor_set(v_reuseFailAlloc_1995_, 25, v_restoreAllArtifacts_x3f_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*26, v_bootstrap_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*26 + 1, v_precompileModules_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*26 + 3, v_reservoir_1983_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*26 + 5, v_allowImportAll_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*26 + 6, v_fixedToolchain_1988_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object* v_p_2005_, lean_object* v_n_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = ((lean_object*)(l_Lake_PackageConfig_lintDriverArgs___proj___closed__3));
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object* v_p_2008_, lean_object* v_n_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2008_, v_n_2009_);
lean_dec(v_n_2009_);
lean_dec(v_p_2008_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object* v_p_2011_, lean_object* v_n_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2011_, v_n_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object* v_p_2014_, lean_object* v_n_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField(v_p_2014_, v_n_2015_);
lean_dec(v_n_2015_);
lean_dec(v_p_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0(lean_object* v_cfg_2017_){
_start:
{
lean_object* v_version_2018_; 
v_version_2018_ = lean_ctor_get(v_cfg_2017_, 16);
lean_inc_ref(v_version_2018_);
return v_version_2018_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0___boxed(lean_object* v_cfg_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lake_PackageConfig_version___proj___lam__0(v_cfg_2019_);
lean_dec_ref(v_cfg_2019_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__1(lean_object* v_val_2021_, lean_object* v_cfg_2022_){
_start:
{
lean_object* v_toWorkspaceConfig_2023_; lean_object* v_toLeanConfig_2024_; uint8_t v_bootstrap_2025_; lean_object* v_extraDepTargets_2026_; uint8_t v_precompileModules_2027_; lean_object* v_moreGlobalServerArgs_2028_; lean_object* v_srcDir_2029_; lean_object* v_buildDir_2030_; lean_object* v_leanLibDir_2031_; lean_object* v_nativeLibDir_2032_; lean_object* v_binDir_2033_; lean_object* v_irDir_2034_; lean_object* v_releaseRepo_2035_; lean_object* v_buildArchive_2036_; uint8_t v_preferReleaseBuild_2037_; lean_object* v_testDriver_2038_; lean_object* v_testDriverArgs_2039_; lean_object* v_lintDriver_2040_; lean_object* v_lintDriverArgs_2041_; lean_object* v_versionTags_2042_; lean_object* v_description_2043_; lean_object* v_keywords_2044_; lean_object* v_homepage_2045_; lean_object* v_license_2046_; lean_object* v_licenseFiles_2047_; lean_object* v_readmeFile_2048_; uint8_t v_reservoir_2049_; lean_object* v_enableArtifactCache_x3f_2050_; lean_object* v_restoreAllArtifacts_x3f_2051_; uint8_t v_libPrefixOnWindows_2052_; uint8_t v_allowImportAll_2053_; uint8_t v_fixedToolchain_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
v_toWorkspaceConfig_2023_ = lean_ctor_get(v_cfg_2022_, 0);
v_toLeanConfig_2024_ = lean_ctor_get(v_cfg_2022_, 1);
v_bootstrap_2025_ = lean_ctor_get_uint8(v_cfg_2022_, sizeof(void*)*26);
v_extraDepTargets_2026_ = lean_ctor_get(v_cfg_2022_, 2);
v_precompileModules_2027_ = lean_ctor_get_uint8(v_cfg_2022_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2028_ = lean_ctor_get(v_cfg_2022_, 3);
v_srcDir_2029_ = lean_ctor_get(v_cfg_2022_, 4);
v_buildDir_2030_ = lean_ctor_get(v_cfg_2022_, 5);
v_leanLibDir_2031_ = lean_ctor_get(v_cfg_2022_, 6);
v_nativeLibDir_2032_ = lean_ctor_get(v_cfg_2022_, 7);
v_binDir_2033_ = lean_ctor_get(v_cfg_2022_, 8);
v_irDir_2034_ = lean_ctor_get(v_cfg_2022_, 9);
v_releaseRepo_2035_ = lean_ctor_get(v_cfg_2022_, 10);
v_buildArchive_2036_ = lean_ctor_get(v_cfg_2022_, 11);
v_preferReleaseBuild_2037_ = lean_ctor_get_uint8(v_cfg_2022_, sizeof(void*)*26 + 2);
v_testDriver_2038_ = lean_ctor_get(v_cfg_2022_, 12);
v_testDriverArgs_2039_ = lean_ctor_get(v_cfg_2022_, 13);
v_lintDriver_2040_ = lean_ctor_get(v_cfg_2022_, 14);
v_lintDriverArgs_2041_ = lean_ctor_get(v_cfg_2022_, 15);
v_versionTags_2042_ = lean_ctor_get(v_cfg_2022_, 17);
v_description_2043_ = lean_ctor_get(v_cfg_2022_, 18);
v_keywords_2044_ = lean_ctor_get(v_cfg_2022_, 19);
v_homepage_2045_ = lean_ctor_get(v_cfg_2022_, 20);
v_license_2046_ = lean_ctor_get(v_cfg_2022_, 21);
v_licenseFiles_2047_ = lean_ctor_get(v_cfg_2022_, 22);
v_readmeFile_2048_ = lean_ctor_get(v_cfg_2022_, 23);
v_reservoir_2049_ = lean_ctor_get_uint8(v_cfg_2022_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2050_ = lean_ctor_get(v_cfg_2022_, 24);
v_restoreAllArtifacts_x3f_2051_ = lean_ctor_get(v_cfg_2022_, 25);
v_libPrefixOnWindows_2052_ = lean_ctor_get_uint8(v_cfg_2022_, sizeof(void*)*26 + 4);
v_allowImportAll_2053_ = lean_ctor_get_uint8(v_cfg_2022_, sizeof(void*)*26 + 5);
v_fixedToolchain_2054_ = lean_ctor_get_uint8(v_cfg_2022_, sizeof(void*)*26 + 6);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_cfg_2022_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_cfg_2022_, 16);
lean_dec(v_unused_2062_);
v___x_2056_ = v_cfg_2022_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2051_);
lean_inc(v_enableArtifactCache_x3f_2050_);
lean_inc(v_readmeFile_2048_);
lean_inc(v_licenseFiles_2047_);
lean_inc(v_license_2046_);
lean_inc(v_homepage_2045_);
lean_inc(v_keywords_2044_);
lean_inc(v_description_2043_);
lean_inc(v_versionTags_2042_);
lean_inc(v_lintDriverArgs_2041_);
lean_inc(v_lintDriver_2040_);
lean_inc(v_testDriverArgs_2039_);
lean_inc(v_testDriver_2038_);
lean_inc(v_buildArchive_2036_);
lean_inc(v_releaseRepo_2035_);
lean_inc(v_irDir_2034_);
lean_inc(v_binDir_2033_);
lean_inc(v_nativeLibDir_2032_);
lean_inc(v_leanLibDir_2031_);
lean_inc(v_buildDir_2030_);
lean_inc(v_srcDir_2029_);
lean_inc(v_moreGlobalServerArgs_2028_);
lean_inc(v_extraDepTargets_2026_);
lean_inc(v_toLeanConfig_2024_);
lean_inc(v_toWorkspaceConfig_2023_);
lean_dec(v_cfg_2022_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 16, v_val_2021_);
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_toWorkspaceConfig_2023_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_toLeanConfig_2024_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_extraDepTargets_2026_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v_moreGlobalServerArgs_2028_);
lean_ctor_set(v_reuseFailAlloc_2060_, 4, v_srcDir_2029_);
lean_ctor_set(v_reuseFailAlloc_2060_, 5, v_buildDir_2030_);
lean_ctor_set(v_reuseFailAlloc_2060_, 6, v_leanLibDir_2031_);
lean_ctor_set(v_reuseFailAlloc_2060_, 7, v_nativeLibDir_2032_);
lean_ctor_set(v_reuseFailAlloc_2060_, 8, v_binDir_2033_);
lean_ctor_set(v_reuseFailAlloc_2060_, 9, v_irDir_2034_);
lean_ctor_set(v_reuseFailAlloc_2060_, 10, v_releaseRepo_2035_);
lean_ctor_set(v_reuseFailAlloc_2060_, 11, v_buildArchive_2036_);
lean_ctor_set(v_reuseFailAlloc_2060_, 12, v_testDriver_2038_);
lean_ctor_set(v_reuseFailAlloc_2060_, 13, v_testDriverArgs_2039_);
lean_ctor_set(v_reuseFailAlloc_2060_, 14, v_lintDriver_2040_);
lean_ctor_set(v_reuseFailAlloc_2060_, 15, v_lintDriverArgs_2041_);
lean_ctor_set(v_reuseFailAlloc_2060_, 16, v_val_2021_);
lean_ctor_set(v_reuseFailAlloc_2060_, 17, v_versionTags_2042_);
lean_ctor_set(v_reuseFailAlloc_2060_, 18, v_description_2043_);
lean_ctor_set(v_reuseFailAlloc_2060_, 19, v_keywords_2044_);
lean_ctor_set(v_reuseFailAlloc_2060_, 20, v_homepage_2045_);
lean_ctor_set(v_reuseFailAlloc_2060_, 21, v_license_2046_);
lean_ctor_set(v_reuseFailAlloc_2060_, 22, v_licenseFiles_2047_);
lean_ctor_set(v_reuseFailAlloc_2060_, 23, v_readmeFile_2048_);
lean_ctor_set(v_reuseFailAlloc_2060_, 24, v_enableArtifactCache_x3f_2050_);
lean_ctor_set(v_reuseFailAlloc_2060_, 25, v_restoreAllArtifacts_x3f_2051_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*26, v_bootstrap_2025_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*26 + 1, v_precompileModules_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*26 + 3, v_reservoir_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2052_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*26 + 5, v_allowImportAll_2053_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*26 + 6, v_fixedToolchain_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__2(lean_object* v_f_2063_, lean_object* v_cfg_2064_){
_start:
{
lean_object* v_toWorkspaceConfig_2065_; lean_object* v_toLeanConfig_2066_; uint8_t v_bootstrap_2067_; lean_object* v_extraDepTargets_2068_; uint8_t v_precompileModules_2069_; lean_object* v_moreGlobalServerArgs_2070_; lean_object* v_srcDir_2071_; lean_object* v_buildDir_2072_; lean_object* v_leanLibDir_2073_; lean_object* v_nativeLibDir_2074_; lean_object* v_binDir_2075_; lean_object* v_irDir_2076_; lean_object* v_releaseRepo_2077_; lean_object* v_buildArchive_2078_; uint8_t v_preferReleaseBuild_2079_; lean_object* v_testDriver_2080_; lean_object* v_testDriverArgs_2081_; lean_object* v_lintDriver_2082_; lean_object* v_lintDriverArgs_2083_; lean_object* v_version_2084_; lean_object* v_versionTags_2085_; lean_object* v_description_2086_; lean_object* v_keywords_2087_; lean_object* v_homepage_2088_; lean_object* v_license_2089_; lean_object* v_licenseFiles_2090_; lean_object* v_readmeFile_2091_; uint8_t v_reservoir_2092_; lean_object* v_enableArtifactCache_x3f_2093_; lean_object* v_restoreAllArtifacts_x3f_2094_; uint8_t v_libPrefixOnWindows_2095_; uint8_t v_allowImportAll_2096_; uint8_t v_fixedToolchain_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2105_; 
v_toWorkspaceConfig_2065_ = lean_ctor_get(v_cfg_2064_, 0);
v_toLeanConfig_2066_ = lean_ctor_get(v_cfg_2064_, 1);
v_bootstrap_2067_ = lean_ctor_get_uint8(v_cfg_2064_, sizeof(void*)*26);
v_extraDepTargets_2068_ = lean_ctor_get(v_cfg_2064_, 2);
v_precompileModules_2069_ = lean_ctor_get_uint8(v_cfg_2064_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2070_ = lean_ctor_get(v_cfg_2064_, 3);
v_srcDir_2071_ = lean_ctor_get(v_cfg_2064_, 4);
v_buildDir_2072_ = lean_ctor_get(v_cfg_2064_, 5);
v_leanLibDir_2073_ = lean_ctor_get(v_cfg_2064_, 6);
v_nativeLibDir_2074_ = lean_ctor_get(v_cfg_2064_, 7);
v_binDir_2075_ = lean_ctor_get(v_cfg_2064_, 8);
v_irDir_2076_ = lean_ctor_get(v_cfg_2064_, 9);
v_releaseRepo_2077_ = lean_ctor_get(v_cfg_2064_, 10);
v_buildArchive_2078_ = lean_ctor_get(v_cfg_2064_, 11);
v_preferReleaseBuild_2079_ = lean_ctor_get_uint8(v_cfg_2064_, sizeof(void*)*26 + 2);
v_testDriver_2080_ = lean_ctor_get(v_cfg_2064_, 12);
v_testDriverArgs_2081_ = lean_ctor_get(v_cfg_2064_, 13);
v_lintDriver_2082_ = lean_ctor_get(v_cfg_2064_, 14);
v_lintDriverArgs_2083_ = lean_ctor_get(v_cfg_2064_, 15);
v_version_2084_ = lean_ctor_get(v_cfg_2064_, 16);
v_versionTags_2085_ = lean_ctor_get(v_cfg_2064_, 17);
v_description_2086_ = lean_ctor_get(v_cfg_2064_, 18);
v_keywords_2087_ = lean_ctor_get(v_cfg_2064_, 19);
v_homepage_2088_ = lean_ctor_get(v_cfg_2064_, 20);
v_license_2089_ = lean_ctor_get(v_cfg_2064_, 21);
v_licenseFiles_2090_ = lean_ctor_get(v_cfg_2064_, 22);
v_readmeFile_2091_ = lean_ctor_get(v_cfg_2064_, 23);
v_reservoir_2092_ = lean_ctor_get_uint8(v_cfg_2064_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2093_ = lean_ctor_get(v_cfg_2064_, 24);
v_restoreAllArtifacts_x3f_2094_ = lean_ctor_get(v_cfg_2064_, 25);
v_libPrefixOnWindows_2095_ = lean_ctor_get_uint8(v_cfg_2064_, sizeof(void*)*26 + 4);
v_allowImportAll_2096_ = lean_ctor_get_uint8(v_cfg_2064_, sizeof(void*)*26 + 5);
v_fixedToolchain_2097_ = lean_ctor_get_uint8(v_cfg_2064_, sizeof(void*)*26 + 6);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_cfg_2064_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2099_ = v_cfg_2064_;
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2094_);
lean_inc(v_enableArtifactCache_x3f_2093_);
lean_inc(v_readmeFile_2091_);
lean_inc(v_licenseFiles_2090_);
lean_inc(v_license_2089_);
lean_inc(v_homepage_2088_);
lean_inc(v_keywords_2087_);
lean_inc(v_description_2086_);
lean_inc(v_versionTags_2085_);
lean_inc(v_version_2084_);
lean_inc(v_lintDriverArgs_2083_);
lean_inc(v_lintDriver_2082_);
lean_inc(v_testDriverArgs_2081_);
lean_inc(v_testDriver_2080_);
lean_inc(v_buildArchive_2078_);
lean_inc(v_releaseRepo_2077_);
lean_inc(v_irDir_2076_);
lean_inc(v_binDir_2075_);
lean_inc(v_nativeLibDir_2074_);
lean_inc(v_leanLibDir_2073_);
lean_inc(v_buildDir_2072_);
lean_inc(v_srcDir_2071_);
lean_inc(v_moreGlobalServerArgs_2070_);
lean_inc(v_extraDepTargets_2068_);
lean_inc(v_toLeanConfig_2066_);
lean_inc(v_toWorkspaceConfig_2065_);
lean_dec(v_cfg_2064_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2103_; 
v___x_2101_ = lean_apply_1(v_f_2063_, v_version_2084_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 16, v___x_2101_);
v___x_2103_ = v___x_2099_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_toWorkspaceConfig_2065_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_toLeanConfig_2066_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v_extraDepTargets_2068_);
lean_ctor_set(v_reuseFailAlloc_2104_, 3, v_moreGlobalServerArgs_2070_);
lean_ctor_set(v_reuseFailAlloc_2104_, 4, v_srcDir_2071_);
lean_ctor_set(v_reuseFailAlloc_2104_, 5, v_buildDir_2072_);
lean_ctor_set(v_reuseFailAlloc_2104_, 6, v_leanLibDir_2073_);
lean_ctor_set(v_reuseFailAlloc_2104_, 7, v_nativeLibDir_2074_);
lean_ctor_set(v_reuseFailAlloc_2104_, 8, v_binDir_2075_);
lean_ctor_set(v_reuseFailAlloc_2104_, 9, v_irDir_2076_);
lean_ctor_set(v_reuseFailAlloc_2104_, 10, v_releaseRepo_2077_);
lean_ctor_set(v_reuseFailAlloc_2104_, 11, v_buildArchive_2078_);
lean_ctor_set(v_reuseFailAlloc_2104_, 12, v_testDriver_2080_);
lean_ctor_set(v_reuseFailAlloc_2104_, 13, v_testDriverArgs_2081_);
lean_ctor_set(v_reuseFailAlloc_2104_, 14, v_lintDriver_2082_);
lean_ctor_set(v_reuseFailAlloc_2104_, 15, v_lintDriverArgs_2083_);
lean_ctor_set(v_reuseFailAlloc_2104_, 16, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2104_, 17, v_versionTags_2085_);
lean_ctor_set(v_reuseFailAlloc_2104_, 18, v_description_2086_);
lean_ctor_set(v_reuseFailAlloc_2104_, 19, v_keywords_2087_);
lean_ctor_set(v_reuseFailAlloc_2104_, 20, v_homepage_2088_);
lean_ctor_set(v_reuseFailAlloc_2104_, 21, v_license_2089_);
lean_ctor_set(v_reuseFailAlloc_2104_, 22, v_licenseFiles_2090_);
lean_ctor_set(v_reuseFailAlloc_2104_, 23, v_readmeFile_2091_);
lean_ctor_set(v_reuseFailAlloc_2104_, 24, v_enableArtifactCache_x3f_2093_);
lean_ctor_set(v_reuseFailAlloc_2104_, 25, v_restoreAllArtifacts_x3f_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*26, v_bootstrap_2067_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*26 + 1, v_precompileModules_2069_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*26 + 3, v_reservoir_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2095_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*26 + 5, v_allowImportAll_2096_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*26 + 6, v_fixedToolchain_2097_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3(lean_object* v_x_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__5));
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3___boxed(lean_object* v_x_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lake_PackageConfig_version___proj___lam__3(v_x_2108_);
lean_dec_ref(v_x_2108_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object* v_p_2119_, lean_object* v_n_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___closed__4));
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object* v_p_2122_, lean_object* v_n_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lake_PackageConfig_version___proj(v_p_2122_, v_n_2123_);
lean_dec(v_n_2123_);
lean_dec(v_p_2122_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object* v_p_2125_, lean_object* v_n_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lake_PackageConfig_version___proj(v_p_2125_, v_n_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object* v_p_2128_, lean_object* v_n_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lake_PackageConfig_version_instConfigField(v_p_2128_, v_n_2129_);
lean_dec(v_n_2129_);
lean_dec(v_p_2128_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0(lean_object* v_cfg_2131_){
_start:
{
lean_object* v_versionTags_2132_; 
v_versionTags_2132_ = lean_ctor_get(v_cfg_2131_, 17);
lean_inc_ref(v_versionTags_2132_);
return v_versionTags_2132_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0___boxed(lean_object* v_cfg_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lake_PackageConfig_versionTags___proj___lam__0(v_cfg_2133_);
lean_dec_ref(v_cfg_2133_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__1(lean_object* v_val_2135_, lean_object* v_cfg_2136_){
_start:
{
lean_object* v_toWorkspaceConfig_2137_; lean_object* v_toLeanConfig_2138_; uint8_t v_bootstrap_2139_; lean_object* v_extraDepTargets_2140_; uint8_t v_precompileModules_2141_; lean_object* v_moreGlobalServerArgs_2142_; lean_object* v_srcDir_2143_; lean_object* v_buildDir_2144_; lean_object* v_leanLibDir_2145_; lean_object* v_nativeLibDir_2146_; lean_object* v_binDir_2147_; lean_object* v_irDir_2148_; lean_object* v_releaseRepo_2149_; lean_object* v_buildArchive_2150_; uint8_t v_preferReleaseBuild_2151_; lean_object* v_testDriver_2152_; lean_object* v_testDriverArgs_2153_; lean_object* v_lintDriver_2154_; lean_object* v_lintDriverArgs_2155_; lean_object* v_version_2156_; lean_object* v_description_2157_; lean_object* v_keywords_2158_; lean_object* v_homepage_2159_; lean_object* v_license_2160_; lean_object* v_licenseFiles_2161_; lean_object* v_readmeFile_2162_; uint8_t v_reservoir_2163_; lean_object* v_enableArtifactCache_x3f_2164_; lean_object* v_restoreAllArtifacts_x3f_2165_; uint8_t v_libPrefixOnWindows_2166_; uint8_t v_allowImportAll_2167_; uint8_t v_fixedToolchain_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
v_toWorkspaceConfig_2137_ = lean_ctor_get(v_cfg_2136_, 0);
v_toLeanConfig_2138_ = lean_ctor_get(v_cfg_2136_, 1);
v_bootstrap_2139_ = lean_ctor_get_uint8(v_cfg_2136_, sizeof(void*)*26);
v_extraDepTargets_2140_ = lean_ctor_get(v_cfg_2136_, 2);
v_precompileModules_2141_ = lean_ctor_get_uint8(v_cfg_2136_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2142_ = lean_ctor_get(v_cfg_2136_, 3);
v_srcDir_2143_ = lean_ctor_get(v_cfg_2136_, 4);
v_buildDir_2144_ = lean_ctor_get(v_cfg_2136_, 5);
v_leanLibDir_2145_ = lean_ctor_get(v_cfg_2136_, 6);
v_nativeLibDir_2146_ = lean_ctor_get(v_cfg_2136_, 7);
v_binDir_2147_ = lean_ctor_get(v_cfg_2136_, 8);
v_irDir_2148_ = lean_ctor_get(v_cfg_2136_, 9);
v_releaseRepo_2149_ = lean_ctor_get(v_cfg_2136_, 10);
v_buildArchive_2150_ = lean_ctor_get(v_cfg_2136_, 11);
v_preferReleaseBuild_2151_ = lean_ctor_get_uint8(v_cfg_2136_, sizeof(void*)*26 + 2);
v_testDriver_2152_ = lean_ctor_get(v_cfg_2136_, 12);
v_testDriverArgs_2153_ = lean_ctor_get(v_cfg_2136_, 13);
v_lintDriver_2154_ = lean_ctor_get(v_cfg_2136_, 14);
v_lintDriverArgs_2155_ = lean_ctor_get(v_cfg_2136_, 15);
v_version_2156_ = lean_ctor_get(v_cfg_2136_, 16);
v_description_2157_ = lean_ctor_get(v_cfg_2136_, 18);
v_keywords_2158_ = lean_ctor_get(v_cfg_2136_, 19);
v_homepage_2159_ = lean_ctor_get(v_cfg_2136_, 20);
v_license_2160_ = lean_ctor_get(v_cfg_2136_, 21);
v_licenseFiles_2161_ = lean_ctor_get(v_cfg_2136_, 22);
v_readmeFile_2162_ = lean_ctor_get(v_cfg_2136_, 23);
v_reservoir_2163_ = lean_ctor_get_uint8(v_cfg_2136_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2164_ = lean_ctor_get(v_cfg_2136_, 24);
v_restoreAllArtifacts_x3f_2165_ = lean_ctor_get(v_cfg_2136_, 25);
v_libPrefixOnWindows_2166_ = lean_ctor_get_uint8(v_cfg_2136_, sizeof(void*)*26 + 4);
v_allowImportAll_2167_ = lean_ctor_get_uint8(v_cfg_2136_, sizeof(void*)*26 + 5);
v_fixedToolchain_2168_ = lean_ctor_get_uint8(v_cfg_2136_, sizeof(void*)*26 + 6);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_cfg_2136_);
if (v_isSharedCheck_2175_ == 0)
{
lean_object* v_unused_2176_; 
v_unused_2176_ = lean_ctor_get(v_cfg_2136_, 17);
lean_dec(v_unused_2176_);
v___x_2170_ = v_cfg_2136_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2165_);
lean_inc(v_enableArtifactCache_x3f_2164_);
lean_inc(v_readmeFile_2162_);
lean_inc(v_licenseFiles_2161_);
lean_inc(v_license_2160_);
lean_inc(v_homepage_2159_);
lean_inc(v_keywords_2158_);
lean_inc(v_description_2157_);
lean_inc(v_version_2156_);
lean_inc(v_lintDriverArgs_2155_);
lean_inc(v_lintDriver_2154_);
lean_inc(v_testDriverArgs_2153_);
lean_inc(v_testDriver_2152_);
lean_inc(v_buildArchive_2150_);
lean_inc(v_releaseRepo_2149_);
lean_inc(v_irDir_2148_);
lean_inc(v_binDir_2147_);
lean_inc(v_nativeLibDir_2146_);
lean_inc(v_leanLibDir_2145_);
lean_inc(v_buildDir_2144_);
lean_inc(v_srcDir_2143_);
lean_inc(v_moreGlobalServerArgs_2142_);
lean_inc(v_extraDepTargets_2140_);
lean_inc(v_toLeanConfig_2138_);
lean_inc(v_toWorkspaceConfig_2137_);
lean_dec(v_cfg_2136_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 17, v_val_2135_);
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_toWorkspaceConfig_2137_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_toLeanConfig_2138_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_extraDepTargets_2140_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v_moreGlobalServerArgs_2142_);
lean_ctor_set(v_reuseFailAlloc_2174_, 4, v_srcDir_2143_);
lean_ctor_set(v_reuseFailAlloc_2174_, 5, v_buildDir_2144_);
lean_ctor_set(v_reuseFailAlloc_2174_, 6, v_leanLibDir_2145_);
lean_ctor_set(v_reuseFailAlloc_2174_, 7, v_nativeLibDir_2146_);
lean_ctor_set(v_reuseFailAlloc_2174_, 8, v_binDir_2147_);
lean_ctor_set(v_reuseFailAlloc_2174_, 9, v_irDir_2148_);
lean_ctor_set(v_reuseFailAlloc_2174_, 10, v_releaseRepo_2149_);
lean_ctor_set(v_reuseFailAlloc_2174_, 11, v_buildArchive_2150_);
lean_ctor_set(v_reuseFailAlloc_2174_, 12, v_testDriver_2152_);
lean_ctor_set(v_reuseFailAlloc_2174_, 13, v_testDriverArgs_2153_);
lean_ctor_set(v_reuseFailAlloc_2174_, 14, v_lintDriver_2154_);
lean_ctor_set(v_reuseFailAlloc_2174_, 15, v_lintDriverArgs_2155_);
lean_ctor_set(v_reuseFailAlloc_2174_, 16, v_version_2156_);
lean_ctor_set(v_reuseFailAlloc_2174_, 17, v_val_2135_);
lean_ctor_set(v_reuseFailAlloc_2174_, 18, v_description_2157_);
lean_ctor_set(v_reuseFailAlloc_2174_, 19, v_keywords_2158_);
lean_ctor_set(v_reuseFailAlloc_2174_, 20, v_homepage_2159_);
lean_ctor_set(v_reuseFailAlloc_2174_, 21, v_license_2160_);
lean_ctor_set(v_reuseFailAlloc_2174_, 22, v_licenseFiles_2161_);
lean_ctor_set(v_reuseFailAlloc_2174_, 23, v_readmeFile_2162_);
lean_ctor_set(v_reuseFailAlloc_2174_, 24, v_enableArtifactCache_x3f_2164_);
lean_ctor_set(v_reuseFailAlloc_2174_, 25, v_restoreAllArtifacts_x3f_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*26, v_bootstrap_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*26 + 1, v_precompileModules_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*26 + 3, v_reservoir_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*26 + 5, v_allowImportAll_2167_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*26 + 6, v_fixedToolchain_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__2(lean_object* v_f_2177_, lean_object* v_cfg_2178_){
_start:
{
lean_object* v_toWorkspaceConfig_2179_; lean_object* v_toLeanConfig_2180_; uint8_t v_bootstrap_2181_; lean_object* v_extraDepTargets_2182_; uint8_t v_precompileModules_2183_; lean_object* v_moreGlobalServerArgs_2184_; lean_object* v_srcDir_2185_; lean_object* v_buildDir_2186_; lean_object* v_leanLibDir_2187_; lean_object* v_nativeLibDir_2188_; lean_object* v_binDir_2189_; lean_object* v_irDir_2190_; lean_object* v_releaseRepo_2191_; lean_object* v_buildArchive_2192_; uint8_t v_preferReleaseBuild_2193_; lean_object* v_testDriver_2194_; lean_object* v_testDriverArgs_2195_; lean_object* v_lintDriver_2196_; lean_object* v_lintDriverArgs_2197_; lean_object* v_version_2198_; lean_object* v_versionTags_2199_; lean_object* v_description_2200_; lean_object* v_keywords_2201_; lean_object* v_homepage_2202_; lean_object* v_license_2203_; lean_object* v_licenseFiles_2204_; lean_object* v_readmeFile_2205_; uint8_t v_reservoir_2206_; lean_object* v_enableArtifactCache_x3f_2207_; lean_object* v_restoreAllArtifacts_x3f_2208_; uint8_t v_libPrefixOnWindows_2209_; uint8_t v_allowImportAll_2210_; uint8_t v_fixedToolchain_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2219_; 
v_toWorkspaceConfig_2179_ = lean_ctor_get(v_cfg_2178_, 0);
v_toLeanConfig_2180_ = lean_ctor_get(v_cfg_2178_, 1);
v_bootstrap_2181_ = lean_ctor_get_uint8(v_cfg_2178_, sizeof(void*)*26);
v_extraDepTargets_2182_ = lean_ctor_get(v_cfg_2178_, 2);
v_precompileModules_2183_ = lean_ctor_get_uint8(v_cfg_2178_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2184_ = lean_ctor_get(v_cfg_2178_, 3);
v_srcDir_2185_ = lean_ctor_get(v_cfg_2178_, 4);
v_buildDir_2186_ = lean_ctor_get(v_cfg_2178_, 5);
v_leanLibDir_2187_ = lean_ctor_get(v_cfg_2178_, 6);
v_nativeLibDir_2188_ = lean_ctor_get(v_cfg_2178_, 7);
v_binDir_2189_ = lean_ctor_get(v_cfg_2178_, 8);
v_irDir_2190_ = lean_ctor_get(v_cfg_2178_, 9);
v_releaseRepo_2191_ = lean_ctor_get(v_cfg_2178_, 10);
v_buildArchive_2192_ = lean_ctor_get(v_cfg_2178_, 11);
v_preferReleaseBuild_2193_ = lean_ctor_get_uint8(v_cfg_2178_, sizeof(void*)*26 + 2);
v_testDriver_2194_ = lean_ctor_get(v_cfg_2178_, 12);
v_testDriverArgs_2195_ = lean_ctor_get(v_cfg_2178_, 13);
v_lintDriver_2196_ = lean_ctor_get(v_cfg_2178_, 14);
v_lintDriverArgs_2197_ = lean_ctor_get(v_cfg_2178_, 15);
v_version_2198_ = lean_ctor_get(v_cfg_2178_, 16);
v_versionTags_2199_ = lean_ctor_get(v_cfg_2178_, 17);
v_description_2200_ = lean_ctor_get(v_cfg_2178_, 18);
v_keywords_2201_ = lean_ctor_get(v_cfg_2178_, 19);
v_homepage_2202_ = lean_ctor_get(v_cfg_2178_, 20);
v_license_2203_ = lean_ctor_get(v_cfg_2178_, 21);
v_licenseFiles_2204_ = lean_ctor_get(v_cfg_2178_, 22);
v_readmeFile_2205_ = lean_ctor_get(v_cfg_2178_, 23);
v_reservoir_2206_ = lean_ctor_get_uint8(v_cfg_2178_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2207_ = lean_ctor_get(v_cfg_2178_, 24);
v_restoreAllArtifacts_x3f_2208_ = lean_ctor_get(v_cfg_2178_, 25);
v_libPrefixOnWindows_2209_ = lean_ctor_get_uint8(v_cfg_2178_, sizeof(void*)*26 + 4);
v_allowImportAll_2210_ = lean_ctor_get_uint8(v_cfg_2178_, sizeof(void*)*26 + 5);
v_fixedToolchain_2211_ = lean_ctor_get_uint8(v_cfg_2178_, sizeof(void*)*26 + 6);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_cfg_2178_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2213_ = v_cfg_2178_;
v_isShared_2214_ = v_isSharedCheck_2219_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2208_);
lean_inc(v_enableArtifactCache_x3f_2207_);
lean_inc(v_readmeFile_2205_);
lean_inc(v_licenseFiles_2204_);
lean_inc(v_license_2203_);
lean_inc(v_homepage_2202_);
lean_inc(v_keywords_2201_);
lean_inc(v_description_2200_);
lean_inc(v_versionTags_2199_);
lean_inc(v_version_2198_);
lean_inc(v_lintDriverArgs_2197_);
lean_inc(v_lintDriver_2196_);
lean_inc(v_testDriverArgs_2195_);
lean_inc(v_testDriver_2194_);
lean_inc(v_buildArchive_2192_);
lean_inc(v_releaseRepo_2191_);
lean_inc(v_irDir_2190_);
lean_inc(v_binDir_2189_);
lean_inc(v_nativeLibDir_2188_);
lean_inc(v_leanLibDir_2187_);
lean_inc(v_buildDir_2186_);
lean_inc(v_srcDir_2185_);
lean_inc(v_moreGlobalServerArgs_2184_);
lean_inc(v_extraDepTargets_2182_);
lean_inc(v_toLeanConfig_2180_);
lean_inc(v_toWorkspaceConfig_2179_);
lean_dec(v_cfg_2178_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2219_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2215_ = lean_apply_1(v_f_2177_, v_versionTags_2199_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 17, v___x_2215_);
v___x_2217_ = v___x_2213_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_toWorkspaceConfig_2179_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_toLeanConfig_2180_);
lean_ctor_set(v_reuseFailAlloc_2218_, 2, v_extraDepTargets_2182_);
lean_ctor_set(v_reuseFailAlloc_2218_, 3, v_moreGlobalServerArgs_2184_);
lean_ctor_set(v_reuseFailAlloc_2218_, 4, v_srcDir_2185_);
lean_ctor_set(v_reuseFailAlloc_2218_, 5, v_buildDir_2186_);
lean_ctor_set(v_reuseFailAlloc_2218_, 6, v_leanLibDir_2187_);
lean_ctor_set(v_reuseFailAlloc_2218_, 7, v_nativeLibDir_2188_);
lean_ctor_set(v_reuseFailAlloc_2218_, 8, v_binDir_2189_);
lean_ctor_set(v_reuseFailAlloc_2218_, 9, v_irDir_2190_);
lean_ctor_set(v_reuseFailAlloc_2218_, 10, v_releaseRepo_2191_);
lean_ctor_set(v_reuseFailAlloc_2218_, 11, v_buildArchive_2192_);
lean_ctor_set(v_reuseFailAlloc_2218_, 12, v_testDriver_2194_);
lean_ctor_set(v_reuseFailAlloc_2218_, 13, v_testDriverArgs_2195_);
lean_ctor_set(v_reuseFailAlloc_2218_, 14, v_lintDriver_2196_);
lean_ctor_set(v_reuseFailAlloc_2218_, 15, v_lintDriverArgs_2197_);
lean_ctor_set(v_reuseFailAlloc_2218_, 16, v_version_2198_);
lean_ctor_set(v_reuseFailAlloc_2218_, 17, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2218_, 18, v_description_2200_);
lean_ctor_set(v_reuseFailAlloc_2218_, 19, v_keywords_2201_);
lean_ctor_set(v_reuseFailAlloc_2218_, 20, v_homepage_2202_);
lean_ctor_set(v_reuseFailAlloc_2218_, 21, v_license_2203_);
lean_ctor_set(v_reuseFailAlloc_2218_, 22, v_licenseFiles_2204_);
lean_ctor_set(v_reuseFailAlloc_2218_, 23, v_readmeFile_2205_);
lean_ctor_set(v_reuseFailAlloc_2218_, 24, v_enableArtifactCache_x3f_2207_);
lean_ctor_set(v_reuseFailAlloc_2218_, 25, v_restoreAllArtifacts_x3f_2208_);
lean_ctor_set_uint8(v_reuseFailAlloc_2218_, sizeof(void*)*26, v_bootstrap_2181_);
lean_ctor_set_uint8(v_reuseFailAlloc_2218_, sizeof(void*)*26 + 1, v_precompileModules_2183_);
lean_ctor_set_uint8(v_reuseFailAlloc_2218_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2193_);
lean_ctor_set_uint8(v_reuseFailAlloc_2218_, sizeof(void*)*26 + 3, v_reservoir_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2218_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2209_);
lean_ctor_set_uint8(v_reuseFailAlloc_2218_, sizeof(void*)*26 + 5, v_allowImportAll_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2218_, sizeof(void*)*26 + 6, v_fixedToolchain_2211_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3(lean_object* v_x_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lake_defaultVersionTags;
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3___boxed(lean_object* v_x_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lake_PackageConfig_versionTags___proj___lam__3(v_x_2222_);
lean_dec_ref(v_x_2222_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object* v_p_2233_, lean_object* v_n_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = ((lean_object*)(l_Lake_PackageConfig_versionTags___proj___closed__4));
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object* v_p_2236_, lean_object* v_n_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lake_PackageConfig_versionTags___proj(v_p_2236_, v_n_2237_);
lean_dec(v_n_2237_);
lean_dec(v_p_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object* v_p_2239_, lean_object* v_n_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lake_PackageConfig_versionTags___proj(v_p_2239_, v_n_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object* v_p_2242_, lean_object* v_n_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lake_PackageConfig_versionTags_instConfigField(v_p_2242_, v_n_2243_);
lean_dec(v_n_2243_);
lean_dec(v_p_2242_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0(lean_object* v_cfg_2245_){
_start:
{
lean_object* v_description_2246_; 
v_description_2246_ = lean_ctor_get(v_cfg_2245_, 18);
lean_inc_ref(v_description_2246_);
return v_description_2246_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0___boxed(lean_object* v_cfg_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lake_PackageConfig_description___proj___lam__0(v_cfg_2247_);
lean_dec_ref(v_cfg_2247_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__1(lean_object* v_val_2249_, lean_object* v_cfg_2250_){
_start:
{
lean_object* v_toWorkspaceConfig_2251_; lean_object* v_toLeanConfig_2252_; uint8_t v_bootstrap_2253_; lean_object* v_extraDepTargets_2254_; uint8_t v_precompileModules_2255_; lean_object* v_moreGlobalServerArgs_2256_; lean_object* v_srcDir_2257_; lean_object* v_buildDir_2258_; lean_object* v_leanLibDir_2259_; lean_object* v_nativeLibDir_2260_; lean_object* v_binDir_2261_; lean_object* v_irDir_2262_; lean_object* v_releaseRepo_2263_; lean_object* v_buildArchive_2264_; uint8_t v_preferReleaseBuild_2265_; lean_object* v_testDriver_2266_; lean_object* v_testDriverArgs_2267_; lean_object* v_lintDriver_2268_; lean_object* v_lintDriverArgs_2269_; lean_object* v_version_2270_; lean_object* v_versionTags_2271_; lean_object* v_keywords_2272_; lean_object* v_homepage_2273_; lean_object* v_license_2274_; lean_object* v_licenseFiles_2275_; lean_object* v_readmeFile_2276_; uint8_t v_reservoir_2277_; lean_object* v_enableArtifactCache_x3f_2278_; lean_object* v_restoreAllArtifacts_x3f_2279_; uint8_t v_libPrefixOnWindows_2280_; uint8_t v_allowImportAll_2281_; uint8_t v_fixedToolchain_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
v_toWorkspaceConfig_2251_ = lean_ctor_get(v_cfg_2250_, 0);
v_toLeanConfig_2252_ = lean_ctor_get(v_cfg_2250_, 1);
v_bootstrap_2253_ = lean_ctor_get_uint8(v_cfg_2250_, sizeof(void*)*26);
v_extraDepTargets_2254_ = lean_ctor_get(v_cfg_2250_, 2);
v_precompileModules_2255_ = lean_ctor_get_uint8(v_cfg_2250_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2256_ = lean_ctor_get(v_cfg_2250_, 3);
v_srcDir_2257_ = lean_ctor_get(v_cfg_2250_, 4);
v_buildDir_2258_ = lean_ctor_get(v_cfg_2250_, 5);
v_leanLibDir_2259_ = lean_ctor_get(v_cfg_2250_, 6);
v_nativeLibDir_2260_ = lean_ctor_get(v_cfg_2250_, 7);
v_binDir_2261_ = lean_ctor_get(v_cfg_2250_, 8);
v_irDir_2262_ = lean_ctor_get(v_cfg_2250_, 9);
v_releaseRepo_2263_ = lean_ctor_get(v_cfg_2250_, 10);
v_buildArchive_2264_ = lean_ctor_get(v_cfg_2250_, 11);
v_preferReleaseBuild_2265_ = lean_ctor_get_uint8(v_cfg_2250_, sizeof(void*)*26 + 2);
v_testDriver_2266_ = lean_ctor_get(v_cfg_2250_, 12);
v_testDriverArgs_2267_ = lean_ctor_get(v_cfg_2250_, 13);
v_lintDriver_2268_ = lean_ctor_get(v_cfg_2250_, 14);
v_lintDriverArgs_2269_ = lean_ctor_get(v_cfg_2250_, 15);
v_version_2270_ = lean_ctor_get(v_cfg_2250_, 16);
v_versionTags_2271_ = lean_ctor_get(v_cfg_2250_, 17);
v_keywords_2272_ = lean_ctor_get(v_cfg_2250_, 19);
v_homepage_2273_ = lean_ctor_get(v_cfg_2250_, 20);
v_license_2274_ = lean_ctor_get(v_cfg_2250_, 21);
v_licenseFiles_2275_ = lean_ctor_get(v_cfg_2250_, 22);
v_readmeFile_2276_ = lean_ctor_get(v_cfg_2250_, 23);
v_reservoir_2277_ = lean_ctor_get_uint8(v_cfg_2250_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2278_ = lean_ctor_get(v_cfg_2250_, 24);
v_restoreAllArtifacts_x3f_2279_ = lean_ctor_get(v_cfg_2250_, 25);
v_libPrefixOnWindows_2280_ = lean_ctor_get_uint8(v_cfg_2250_, sizeof(void*)*26 + 4);
v_allowImportAll_2281_ = lean_ctor_get_uint8(v_cfg_2250_, sizeof(void*)*26 + 5);
v_fixedToolchain_2282_ = lean_ctor_get_uint8(v_cfg_2250_, sizeof(void*)*26 + 6);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_cfg_2250_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; 
v_unused_2290_ = lean_ctor_get(v_cfg_2250_, 18);
lean_dec(v_unused_2290_);
v___x_2284_ = v_cfg_2250_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2279_);
lean_inc(v_enableArtifactCache_x3f_2278_);
lean_inc(v_readmeFile_2276_);
lean_inc(v_licenseFiles_2275_);
lean_inc(v_license_2274_);
lean_inc(v_homepage_2273_);
lean_inc(v_keywords_2272_);
lean_inc(v_versionTags_2271_);
lean_inc(v_version_2270_);
lean_inc(v_lintDriverArgs_2269_);
lean_inc(v_lintDriver_2268_);
lean_inc(v_testDriverArgs_2267_);
lean_inc(v_testDriver_2266_);
lean_inc(v_buildArchive_2264_);
lean_inc(v_releaseRepo_2263_);
lean_inc(v_irDir_2262_);
lean_inc(v_binDir_2261_);
lean_inc(v_nativeLibDir_2260_);
lean_inc(v_leanLibDir_2259_);
lean_inc(v_buildDir_2258_);
lean_inc(v_srcDir_2257_);
lean_inc(v_moreGlobalServerArgs_2256_);
lean_inc(v_extraDepTargets_2254_);
lean_inc(v_toLeanConfig_2252_);
lean_inc(v_toWorkspaceConfig_2251_);
lean_dec(v_cfg_2250_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 18, v_val_2249_);
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_toWorkspaceConfig_2251_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_toLeanConfig_2252_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v_extraDepTargets_2254_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_moreGlobalServerArgs_2256_);
lean_ctor_set(v_reuseFailAlloc_2288_, 4, v_srcDir_2257_);
lean_ctor_set(v_reuseFailAlloc_2288_, 5, v_buildDir_2258_);
lean_ctor_set(v_reuseFailAlloc_2288_, 6, v_leanLibDir_2259_);
lean_ctor_set(v_reuseFailAlloc_2288_, 7, v_nativeLibDir_2260_);
lean_ctor_set(v_reuseFailAlloc_2288_, 8, v_binDir_2261_);
lean_ctor_set(v_reuseFailAlloc_2288_, 9, v_irDir_2262_);
lean_ctor_set(v_reuseFailAlloc_2288_, 10, v_releaseRepo_2263_);
lean_ctor_set(v_reuseFailAlloc_2288_, 11, v_buildArchive_2264_);
lean_ctor_set(v_reuseFailAlloc_2288_, 12, v_testDriver_2266_);
lean_ctor_set(v_reuseFailAlloc_2288_, 13, v_testDriverArgs_2267_);
lean_ctor_set(v_reuseFailAlloc_2288_, 14, v_lintDriver_2268_);
lean_ctor_set(v_reuseFailAlloc_2288_, 15, v_lintDriverArgs_2269_);
lean_ctor_set(v_reuseFailAlloc_2288_, 16, v_version_2270_);
lean_ctor_set(v_reuseFailAlloc_2288_, 17, v_versionTags_2271_);
lean_ctor_set(v_reuseFailAlloc_2288_, 18, v_val_2249_);
lean_ctor_set(v_reuseFailAlloc_2288_, 19, v_keywords_2272_);
lean_ctor_set(v_reuseFailAlloc_2288_, 20, v_homepage_2273_);
lean_ctor_set(v_reuseFailAlloc_2288_, 21, v_license_2274_);
lean_ctor_set(v_reuseFailAlloc_2288_, 22, v_licenseFiles_2275_);
lean_ctor_set(v_reuseFailAlloc_2288_, 23, v_readmeFile_2276_);
lean_ctor_set(v_reuseFailAlloc_2288_, 24, v_enableArtifactCache_x3f_2278_);
lean_ctor_set(v_reuseFailAlloc_2288_, 25, v_restoreAllArtifacts_x3f_2279_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*26, v_bootstrap_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*26 + 1, v_precompileModules_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2265_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*26 + 3, v_reservoir_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2280_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*26 + 5, v_allowImportAll_2281_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*26 + 6, v_fixedToolchain_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__2(lean_object* v_f_2291_, lean_object* v_cfg_2292_){
_start:
{
lean_object* v_toWorkspaceConfig_2293_; lean_object* v_toLeanConfig_2294_; uint8_t v_bootstrap_2295_; lean_object* v_extraDepTargets_2296_; uint8_t v_precompileModules_2297_; lean_object* v_moreGlobalServerArgs_2298_; lean_object* v_srcDir_2299_; lean_object* v_buildDir_2300_; lean_object* v_leanLibDir_2301_; lean_object* v_nativeLibDir_2302_; lean_object* v_binDir_2303_; lean_object* v_irDir_2304_; lean_object* v_releaseRepo_2305_; lean_object* v_buildArchive_2306_; uint8_t v_preferReleaseBuild_2307_; lean_object* v_testDriver_2308_; lean_object* v_testDriverArgs_2309_; lean_object* v_lintDriver_2310_; lean_object* v_lintDriverArgs_2311_; lean_object* v_version_2312_; lean_object* v_versionTags_2313_; lean_object* v_description_2314_; lean_object* v_keywords_2315_; lean_object* v_homepage_2316_; lean_object* v_license_2317_; lean_object* v_licenseFiles_2318_; lean_object* v_readmeFile_2319_; uint8_t v_reservoir_2320_; lean_object* v_enableArtifactCache_x3f_2321_; lean_object* v_restoreAllArtifacts_x3f_2322_; uint8_t v_libPrefixOnWindows_2323_; uint8_t v_allowImportAll_2324_; uint8_t v_fixedToolchain_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2333_; 
v_toWorkspaceConfig_2293_ = lean_ctor_get(v_cfg_2292_, 0);
v_toLeanConfig_2294_ = lean_ctor_get(v_cfg_2292_, 1);
v_bootstrap_2295_ = lean_ctor_get_uint8(v_cfg_2292_, sizeof(void*)*26);
v_extraDepTargets_2296_ = lean_ctor_get(v_cfg_2292_, 2);
v_precompileModules_2297_ = lean_ctor_get_uint8(v_cfg_2292_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2298_ = lean_ctor_get(v_cfg_2292_, 3);
v_srcDir_2299_ = lean_ctor_get(v_cfg_2292_, 4);
v_buildDir_2300_ = lean_ctor_get(v_cfg_2292_, 5);
v_leanLibDir_2301_ = lean_ctor_get(v_cfg_2292_, 6);
v_nativeLibDir_2302_ = lean_ctor_get(v_cfg_2292_, 7);
v_binDir_2303_ = lean_ctor_get(v_cfg_2292_, 8);
v_irDir_2304_ = lean_ctor_get(v_cfg_2292_, 9);
v_releaseRepo_2305_ = lean_ctor_get(v_cfg_2292_, 10);
v_buildArchive_2306_ = lean_ctor_get(v_cfg_2292_, 11);
v_preferReleaseBuild_2307_ = lean_ctor_get_uint8(v_cfg_2292_, sizeof(void*)*26 + 2);
v_testDriver_2308_ = lean_ctor_get(v_cfg_2292_, 12);
v_testDriverArgs_2309_ = lean_ctor_get(v_cfg_2292_, 13);
v_lintDriver_2310_ = lean_ctor_get(v_cfg_2292_, 14);
v_lintDriverArgs_2311_ = lean_ctor_get(v_cfg_2292_, 15);
v_version_2312_ = lean_ctor_get(v_cfg_2292_, 16);
v_versionTags_2313_ = lean_ctor_get(v_cfg_2292_, 17);
v_description_2314_ = lean_ctor_get(v_cfg_2292_, 18);
v_keywords_2315_ = lean_ctor_get(v_cfg_2292_, 19);
v_homepage_2316_ = lean_ctor_get(v_cfg_2292_, 20);
v_license_2317_ = lean_ctor_get(v_cfg_2292_, 21);
v_licenseFiles_2318_ = lean_ctor_get(v_cfg_2292_, 22);
v_readmeFile_2319_ = lean_ctor_get(v_cfg_2292_, 23);
v_reservoir_2320_ = lean_ctor_get_uint8(v_cfg_2292_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2321_ = lean_ctor_get(v_cfg_2292_, 24);
v_restoreAllArtifacts_x3f_2322_ = lean_ctor_get(v_cfg_2292_, 25);
v_libPrefixOnWindows_2323_ = lean_ctor_get_uint8(v_cfg_2292_, sizeof(void*)*26 + 4);
v_allowImportAll_2324_ = lean_ctor_get_uint8(v_cfg_2292_, sizeof(void*)*26 + 5);
v_fixedToolchain_2325_ = lean_ctor_get_uint8(v_cfg_2292_, sizeof(void*)*26 + 6);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_cfg_2292_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2327_ = v_cfg_2292_;
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2322_);
lean_inc(v_enableArtifactCache_x3f_2321_);
lean_inc(v_readmeFile_2319_);
lean_inc(v_licenseFiles_2318_);
lean_inc(v_license_2317_);
lean_inc(v_homepage_2316_);
lean_inc(v_keywords_2315_);
lean_inc(v_description_2314_);
lean_inc(v_versionTags_2313_);
lean_inc(v_version_2312_);
lean_inc(v_lintDriverArgs_2311_);
lean_inc(v_lintDriver_2310_);
lean_inc(v_testDriverArgs_2309_);
lean_inc(v_testDriver_2308_);
lean_inc(v_buildArchive_2306_);
lean_inc(v_releaseRepo_2305_);
lean_inc(v_irDir_2304_);
lean_inc(v_binDir_2303_);
lean_inc(v_nativeLibDir_2302_);
lean_inc(v_leanLibDir_2301_);
lean_inc(v_buildDir_2300_);
lean_inc(v_srcDir_2299_);
lean_inc(v_moreGlobalServerArgs_2298_);
lean_inc(v_extraDepTargets_2296_);
lean_inc(v_toLeanConfig_2294_);
lean_inc(v_toWorkspaceConfig_2293_);
lean_dec(v_cfg_2292_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = lean_apply_1(v_f_2291_, v_description_2314_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 18, v___x_2329_);
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_toWorkspaceConfig_2293_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_toLeanConfig_2294_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_extraDepTargets_2296_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_moreGlobalServerArgs_2298_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v_srcDir_2299_);
lean_ctor_set(v_reuseFailAlloc_2332_, 5, v_buildDir_2300_);
lean_ctor_set(v_reuseFailAlloc_2332_, 6, v_leanLibDir_2301_);
lean_ctor_set(v_reuseFailAlloc_2332_, 7, v_nativeLibDir_2302_);
lean_ctor_set(v_reuseFailAlloc_2332_, 8, v_binDir_2303_);
lean_ctor_set(v_reuseFailAlloc_2332_, 9, v_irDir_2304_);
lean_ctor_set(v_reuseFailAlloc_2332_, 10, v_releaseRepo_2305_);
lean_ctor_set(v_reuseFailAlloc_2332_, 11, v_buildArchive_2306_);
lean_ctor_set(v_reuseFailAlloc_2332_, 12, v_testDriver_2308_);
lean_ctor_set(v_reuseFailAlloc_2332_, 13, v_testDriverArgs_2309_);
lean_ctor_set(v_reuseFailAlloc_2332_, 14, v_lintDriver_2310_);
lean_ctor_set(v_reuseFailAlloc_2332_, 15, v_lintDriverArgs_2311_);
lean_ctor_set(v_reuseFailAlloc_2332_, 16, v_version_2312_);
lean_ctor_set(v_reuseFailAlloc_2332_, 17, v_versionTags_2313_);
lean_ctor_set(v_reuseFailAlloc_2332_, 18, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2332_, 19, v_keywords_2315_);
lean_ctor_set(v_reuseFailAlloc_2332_, 20, v_homepage_2316_);
lean_ctor_set(v_reuseFailAlloc_2332_, 21, v_license_2317_);
lean_ctor_set(v_reuseFailAlloc_2332_, 22, v_licenseFiles_2318_);
lean_ctor_set(v_reuseFailAlloc_2332_, 23, v_readmeFile_2319_);
lean_ctor_set(v_reuseFailAlloc_2332_, 24, v_enableArtifactCache_x3f_2321_);
lean_ctor_set(v_reuseFailAlloc_2332_, 25, v_restoreAllArtifacts_x3f_2322_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*26, v_bootstrap_2295_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*26 + 1, v_precompileModules_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2307_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*26 + 3, v_reservoir_2320_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2323_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*26 + 5, v_allowImportAll_2324_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*26 + 6, v_fixedToolchain_2325_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object* v_p_2342_, lean_object* v_n_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = ((lean_object*)(l_Lake_PackageConfig_description___proj___closed__3));
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object* v_p_2345_, lean_object* v_n_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lake_PackageConfig_description___proj(v_p_2345_, v_n_2346_);
lean_dec(v_n_2346_);
lean_dec(v_p_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object* v_p_2348_, lean_object* v_n_2349_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lake_PackageConfig_description___proj(v_p_2348_, v_n_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object* v_p_2351_, lean_object* v_n_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lake_PackageConfig_description_instConfigField(v_p_2351_, v_n_2352_);
lean_dec(v_n_2352_);
lean_dec(v_p_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0(lean_object* v_cfg_2354_){
_start:
{
lean_object* v_keywords_2355_; 
v_keywords_2355_ = lean_ctor_get(v_cfg_2354_, 19);
lean_inc_ref(v_keywords_2355_);
return v_keywords_2355_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0___boxed(lean_object* v_cfg_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lake_PackageConfig_keywords___proj___lam__0(v_cfg_2356_);
lean_dec_ref(v_cfg_2356_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__1(lean_object* v_val_2358_, lean_object* v_cfg_2359_){
_start:
{
lean_object* v_toWorkspaceConfig_2360_; lean_object* v_toLeanConfig_2361_; uint8_t v_bootstrap_2362_; lean_object* v_extraDepTargets_2363_; uint8_t v_precompileModules_2364_; lean_object* v_moreGlobalServerArgs_2365_; lean_object* v_srcDir_2366_; lean_object* v_buildDir_2367_; lean_object* v_leanLibDir_2368_; lean_object* v_nativeLibDir_2369_; lean_object* v_binDir_2370_; lean_object* v_irDir_2371_; lean_object* v_releaseRepo_2372_; lean_object* v_buildArchive_2373_; uint8_t v_preferReleaseBuild_2374_; lean_object* v_testDriver_2375_; lean_object* v_testDriverArgs_2376_; lean_object* v_lintDriver_2377_; lean_object* v_lintDriverArgs_2378_; lean_object* v_version_2379_; lean_object* v_versionTags_2380_; lean_object* v_description_2381_; lean_object* v_homepage_2382_; lean_object* v_license_2383_; lean_object* v_licenseFiles_2384_; lean_object* v_readmeFile_2385_; uint8_t v_reservoir_2386_; lean_object* v_enableArtifactCache_x3f_2387_; lean_object* v_restoreAllArtifacts_x3f_2388_; uint8_t v_libPrefixOnWindows_2389_; uint8_t v_allowImportAll_2390_; uint8_t v_fixedToolchain_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
v_toWorkspaceConfig_2360_ = lean_ctor_get(v_cfg_2359_, 0);
v_toLeanConfig_2361_ = lean_ctor_get(v_cfg_2359_, 1);
v_bootstrap_2362_ = lean_ctor_get_uint8(v_cfg_2359_, sizeof(void*)*26);
v_extraDepTargets_2363_ = lean_ctor_get(v_cfg_2359_, 2);
v_precompileModules_2364_ = lean_ctor_get_uint8(v_cfg_2359_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2365_ = lean_ctor_get(v_cfg_2359_, 3);
v_srcDir_2366_ = lean_ctor_get(v_cfg_2359_, 4);
v_buildDir_2367_ = lean_ctor_get(v_cfg_2359_, 5);
v_leanLibDir_2368_ = lean_ctor_get(v_cfg_2359_, 6);
v_nativeLibDir_2369_ = lean_ctor_get(v_cfg_2359_, 7);
v_binDir_2370_ = lean_ctor_get(v_cfg_2359_, 8);
v_irDir_2371_ = lean_ctor_get(v_cfg_2359_, 9);
v_releaseRepo_2372_ = lean_ctor_get(v_cfg_2359_, 10);
v_buildArchive_2373_ = lean_ctor_get(v_cfg_2359_, 11);
v_preferReleaseBuild_2374_ = lean_ctor_get_uint8(v_cfg_2359_, sizeof(void*)*26 + 2);
v_testDriver_2375_ = lean_ctor_get(v_cfg_2359_, 12);
v_testDriverArgs_2376_ = lean_ctor_get(v_cfg_2359_, 13);
v_lintDriver_2377_ = lean_ctor_get(v_cfg_2359_, 14);
v_lintDriverArgs_2378_ = lean_ctor_get(v_cfg_2359_, 15);
v_version_2379_ = lean_ctor_get(v_cfg_2359_, 16);
v_versionTags_2380_ = lean_ctor_get(v_cfg_2359_, 17);
v_description_2381_ = lean_ctor_get(v_cfg_2359_, 18);
v_homepage_2382_ = lean_ctor_get(v_cfg_2359_, 20);
v_license_2383_ = lean_ctor_get(v_cfg_2359_, 21);
v_licenseFiles_2384_ = lean_ctor_get(v_cfg_2359_, 22);
v_readmeFile_2385_ = lean_ctor_get(v_cfg_2359_, 23);
v_reservoir_2386_ = lean_ctor_get_uint8(v_cfg_2359_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2387_ = lean_ctor_get(v_cfg_2359_, 24);
v_restoreAllArtifacts_x3f_2388_ = lean_ctor_get(v_cfg_2359_, 25);
v_libPrefixOnWindows_2389_ = lean_ctor_get_uint8(v_cfg_2359_, sizeof(void*)*26 + 4);
v_allowImportAll_2390_ = lean_ctor_get_uint8(v_cfg_2359_, sizeof(void*)*26 + 5);
v_fixedToolchain_2391_ = lean_ctor_get_uint8(v_cfg_2359_, sizeof(void*)*26 + 6);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_cfg_2359_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v_cfg_2359_, 19);
lean_dec(v_unused_2399_);
v___x_2393_ = v_cfg_2359_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2388_);
lean_inc(v_enableArtifactCache_x3f_2387_);
lean_inc(v_readmeFile_2385_);
lean_inc(v_licenseFiles_2384_);
lean_inc(v_license_2383_);
lean_inc(v_homepage_2382_);
lean_inc(v_description_2381_);
lean_inc(v_versionTags_2380_);
lean_inc(v_version_2379_);
lean_inc(v_lintDriverArgs_2378_);
lean_inc(v_lintDriver_2377_);
lean_inc(v_testDriverArgs_2376_);
lean_inc(v_testDriver_2375_);
lean_inc(v_buildArchive_2373_);
lean_inc(v_releaseRepo_2372_);
lean_inc(v_irDir_2371_);
lean_inc(v_binDir_2370_);
lean_inc(v_nativeLibDir_2369_);
lean_inc(v_leanLibDir_2368_);
lean_inc(v_buildDir_2367_);
lean_inc(v_srcDir_2366_);
lean_inc(v_moreGlobalServerArgs_2365_);
lean_inc(v_extraDepTargets_2363_);
lean_inc(v_toLeanConfig_2361_);
lean_inc(v_toWorkspaceConfig_2360_);
lean_dec(v_cfg_2359_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 19, v_val_2358_);
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_toWorkspaceConfig_2360_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_toLeanConfig_2361_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_extraDepTargets_2363_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_moreGlobalServerArgs_2365_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_srcDir_2366_);
lean_ctor_set(v_reuseFailAlloc_2397_, 5, v_buildDir_2367_);
lean_ctor_set(v_reuseFailAlloc_2397_, 6, v_leanLibDir_2368_);
lean_ctor_set(v_reuseFailAlloc_2397_, 7, v_nativeLibDir_2369_);
lean_ctor_set(v_reuseFailAlloc_2397_, 8, v_binDir_2370_);
lean_ctor_set(v_reuseFailAlloc_2397_, 9, v_irDir_2371_);
lean_ctor_set(v_reuseFailAlloc_2397_, 10, v_releaseRepo_2372_);
lean_ctor_set(v_reuseFailAlloc_2397_, 11, v_buildArchive_2373_);
lean_ctor_set(v_reuseFailAlloc_2397_, 12, v_testDriver_2375_);
lean_ctor_set(v_reuseFailAlloc_2397_, 13, v_testDriverArgs_2376_);
lean_ctor_set(v_reuseFailAlloc_2397_, 14, v_lintDriver_2377_);
lean_ctor_set(v_reuseFailAlloc_2397_, 15, v_lintDriverArgs_2378_);
lean_ctor_set(v_reuseFailAlloc_2397_, 16, v_version_2379_);
lean_ctor_set(v_reuseFailAlloc_2397_, 17, v_versionTags_2380_);
lean_ctor_set(v_reuseFailAlloc_2397_, 18, v_description_2381_);
lean_ctor_set(v_reuseFailAlloc_2397_, 19, v_val_2358_);
lean_ctor_set(v_reuseFailAlloc_2397_, 20, v_homepage_2382_);
lean_ctor_set(v_reuseFailAlloc_2397_, 21, v_license_2383_);
lean_ctor_set(v_reuseFailAlloc_2397_, 22, v_licenseFiles_2384_);
lean_ctor_set(v_reuseFailAlloc_2397_, 23, v_readmeFile_2385_);
lean_ctor_set(v_reuseFailAlloc_2397_, 24, v_enableArtifactCache_x3f_2387_);
lean_ctor_set(v_reuseFailAlloc_2397_, 25, v_restoreAllArtifacts_x3f_2388_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, sizeof(void*)*26, v_bootstrap_2362_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, sizeof(void*)*26 + 1, v_precompileModules_2364_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2374_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, sizeof(void*)*26 + 3, v_reservoir_2386_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2389_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, sizeof(void*)*26 + 5, v_allowImportAll_2390_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, sizeof(void*)*26 + 6, v_fixedToolchain_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__2(lean_object* v_f_2400_, lean_object* v_cfg_2401_){
_start:
{
lean_object* v_toWorkspaceConfig_2402_; lean_object* v_toLeanConfig_2403_; uint8_t v_bootstrap_2404_; lean_object* v_extraDepTargets_2405_; uint8_t v_precompileModules_2406_; lean_object* v_moreGlobalServerArgs_2407_; lean_object* v_srcDir_2408_; lean_object* v_buildDir_2409_; lean_object* v_leanLibDir_2410_; lean_object* v_nativeLibDir_2411_; lean_object* v_binDir_2412_; lean_object* v_irDir_2413_; lean_object* v_releaseRepo_2414_; lean_object* v_buildArchive_2415_; uint8_t v_preferReleaseBuild_2416_; lean_object* v_testDriver_2417_; lean_object* v_testDriverArgs_2418_; lean_object* v_lintDriver_2419_; lean_object* v_lintDriverArgs_2420_; lean_object* v_version_2421_; lean_object* v_versionTags_2422_; lean_object* v_description_2423_; lean_object* v_keywords_2424_; lean_object* v_homepage_2425_; lean_object* v_license_2426_; lean_object* v_licenseFiles_2427_; lean_object* v_readmeFile_2428_; uint8_t v_reservoir_2429_; lean_object* v_enableArtifactCache_x3f_2430_; lean_object* v_restoreAllArtifacts_x3f_2431_; uint8_t v_libPrefixOnWindows_2432_; uint8_t v_allowImportAll_2433_; uint8_t v_fixedToolchain_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2442_; 
v_toWorkspaceConfig_2402_ = lean_ctor_get(v_cfg_2401_, 0);
v_toLeanConfig_2403_ = lean_ctor_get(v_cfg_2401_, 1);
v_bootstrap_2404_ = lean_ctor_get_uint8(v_cfg_2401_, sizeof(void*)*26);
v_extraDepTargets_2405_ = lean_ctor_get(v_cfg_2401_, 2);
v_precompileModules_2406_ = lean_ctor_get_uint8(v_cfg_2401_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2407_ = lean_ctor_get(v_cfg_2401_, 3);
v_srcDir_2408_ = lean_ctor_get(v_cfg_2401_, 4);
v_buildDir_2409_ = lean_ctor_get(v_cfg_2401_, 5);
v_leanLibDir_2410_ = lean_ctor_get(v_cfg_2401_, 6);
v_nativeLibDir_2411_ = lean_ctor_get(v_cfg_2401_, 7);
v_binDir_2412_ = lean_ctor_get(v_cfg_2401_, 8);
v_irDir_2413_ = lean_ctor_get(v_cfg_2401_, 9);
v_releaseRepo_2414_ = lean_ctor_get(v_cfg_2401_, 10);
v_buildArchive_2415_ = lean_ctor_get(v_cfg_2401_, 11);
v_preferReleaseBuild_2416_ = lean_ctor_get_uint8(v_cfg_2401_, sizeof(void*)*26 + 2);
v_testDriver_2417_ = lean_ctor_get(v_cfg_2401_, 12);
v_testDriverArgs_2418_ = lean_ctor_get(v_cfg_2401_, 13);
v_lintDriver_2419_ = lean_ctor_get(v_cfg_2401_, 14);
v_lintDriverArgs_2420_ = lean_ctor_get(v_cfg_2401_, 15);
v_version_2421_ = lean_ctor_get(v_cfg_2401_, 16);
v_versionTags_2422_ = lean_ctor_get(v_cfg_2401_, 17);
v_description_2423_ = lean_ctor_get(v_cfg_2401_, 18);
v_keywords_2424_ = lean_ctor_get(v_cfg_2401_, 19);
v_homepage_2425_ = lean_ctor_get(v_cfg_2401_, 20);
v_license_2426_ = lean_ctor_get(v_cfg_2401_, 21);
v_licenseFiles_2427_ = lean_ctor_get(v_cfg_2401_, 22);
v_readmeFile_2428_ = lean_ctor_get(v_cfg_2401_, 23);
v_reservoir_2429_ = lean_ctor_get_uint8(v_cfg_2401_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2430_ = lean_ctor_get(v_cfg_2401_, 24);
v_restoreAllArtifacts_x3f_2431_ = lean_ctor_get(v_cfg_2401_, 25);
v_libPrefixOnWindows_2432_ = lean_ctor_get_uint8(v_cfg_2401_, sizeof(void*)*26 + 4);
v_allowImportAll_2433_ = lean_ctor_get_uint8(v_cfg_2401_, sizeof(void*)*26 + 5);
v_fixedToolchain_2434_ = lean_ctor_get_uint8(v_cfg_2401_, sizeof(void*)*26 + 6);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_cfg_2401_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2436_ = v_cfg_2401_;
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2431_);
lean_inc(v_enableArtifactCache_x3f_2430_);
lean_inc(v_readmeFile_2428_);
lean_inc(v_licenseFiles_2427_);
lean_inc(v_license_2426_);
lean_inc(v_homepage_2425_);
lean_inc(v_keywords_2424_);
lean_inc(v_description_2423_);
lean_inc(v_versionTags_2422_);
lean_inc(v_version_2421_);
lean_inc(v_lintDriverArgs_2420_);
lean_inc(v_lintDriver_2419_);
lean_inc(v_testDriverArgs_2418_);
lean_inc(v_testDriver_2417_);
lean_inc(v_buildArchive_2415_);
lean_inc(v_releaseRepo_2414_);
lean_inc(v_irDir_2413_);
lean_inc(v_binDir_2412_);
lean_inc(v_nativeLibDir_2411_);
lean_inc(v_leanLibDir_2410_);
lean_inc(v_buildDir_2409_);
lean_inc(v_srcDir_2408_);
lean_inc(v_moreGlobalServerArgs_2407_);
lean_inc(v_extraDepTargets_2405_);
lean_inc(v_toLeanConfig_2403_);
lean_inc(v_toWorkspaceConfig_2402_);
lean_dec(v_cfg_2401_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2438_ = lean_apply_1(v_f_2400_, v_keywords_2424_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 19, v___x_2438_);
v___x_2440_ = v___x_2436_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_toWorkspaceConfig_2402_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_toLeanConfig_2403_);
lean_ctor_set(v_reuseFailAlloc_2441_, 2, v_extraDepTargets_2405_);
lean_ctor_set(v_reuseFailAlloc_2441_, 3, v_moreGlobalServerArgs_2407_);
lean_ctor_set(v_reuseFailAlloc_2441_, 4, v_srcDir_2408_);
lean_ctor_set(v_reuseFailAlloc_2441_, 5, v_buildDir_2409_);
lean_ctor_set(v_reuseFailAlloc_2441_, 6, v_leanLibDir_2410_);
lean_ctor_set(v_reuseFailAlloc_2441_, 7, v_nativeLibDir_2411_);
lean_ctor_set(v_reuseFailAlloc_2441_, 8, v_binDir_2412_);
lean_ctor_set(v_reuseFailAlloc_2441_, 9, v_irDir_2413_);
lean_ctor_set(v_reuseFailAlloc_2441_, 10, v_releaseRepo_2414_);
lean_ctor_set(v_reuseFailAlloc_2441_, 11, v_buildArchive_2415_);
lean_ctor_set(v_reuseFailAlloc_2441_, 12, v_testDriver_2417_);
lean_ctor_set(v_reuseFailAlloc_2441_, 13, v_testDriverArgs_2418_);
lean_ctor_set(v_reuseFailAlloc_2441_, 14, v_lintDriver_2419_);
lean_ctor_set(v_reuseFailAlloc_2441_, 15, v_lintDriverArgs_2420_);
lean_ctor_set(v_reuseFailAlloc_2441_, 16, v_version_2421_);
lean_ctor_set(v_reuseFailAlloc_2441_, 17, v_versionTags_2422_);
lean_ctor_set(v_reuseFailAlloc_2441_, 18, v_description_2423_);
lean_ctor_set(v_reuseFailAlloc_2441_, 19, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2441_, 20, v_homepage_2425_);
lean_ctor_set(v_reuseFailAlloc_2441_, 21, v_license_2426_);
lean_ctor_set(v_reuseFailAlloc_2441_, 22, v_licenseFiles_2427_);
lean_ctor_set(v_reuseFailAlloc_2441_, 23, v_readmeFile_2428_);
lean_ctor_set(v_reuseFailAlloc_2441_, 24, v_enableArtifactCache_x3f_2430_);
lean_ctor_set(v_reuseFailAlloc_2441_, 25, v_restoreAllArtifacts_x3f_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2441_, sizeof(void*)*26, v_bootstrap_2404_);
lean_ctor_set_uint8(v_reuseFailAlloc_2441_, sizeof(void*)*26 + 1, v_precompileModules_2406_);
lean_ctor_set_uint8(v_reuseFailAlloc_2441_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2416_);
lean_ctor_set_uint8(v_reuseFailAlloc_2441_, sizeof(void*)*26 + 3, v_reservoir_2429_);
lean_ctor_set_uint8(v_reuseFailAlloc_2441_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2441_, sizeof(void*)*26 + 5, v_allowImportAll_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2441_, sizeof(void*)*26 + 6, v_fixedToolchain_2434_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object* v_p_2451_, lean_object* v_n_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = ((lean_object*)(l_Lake_PackageConfig_keywords___proj___closed__3));
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object* v_p_2454_, lean_object* v_n_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lake_PackageConfig_keywords___proj(v_p_2454_, v_n_2455_);
lean_dec(v_n_2455_);
lean_dec(v_p_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object* v_p_2457_, lean_object* v_n_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lake_PackageConfig_keywords___proj(v_p_2457_, v_n_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object* v_p_2460_, lean_object* v_n_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lake_PackageConfig_keywords_instConfigField(v_p_2460_, v_n_2461_);
lean_dec(v_n_2461_);
lean_dec(v_p_2460_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0(lean_object* v_cfg_2463_){
_start:
{
lean_object* v_homepage_2464_; 
v_homepage_2464_ = lean_ctor_get(v_cfg_2463_, 20);
lean_inc_ref(v_homepage_2464_);
return v_homepage_2464_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0___boxed(lean_object* v_cfg_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lake_PackageConfig_homepage___proj___lam__0(v_cfg_2465_);
lean_dec_ref(v_cfg_2465_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__1(lean_object* v_val_2467_, lean_object* v_cfg_2468_){
_start:
{
lean_object* v_toWorkspaceConfig_2469_; lean_object* v_toLeanConfig_2470_; uint8_t v_bootstrap_2471_; lean_object* v_extraDepTargets_2472_; uint8_t v_precompileModules_2473_; lean_object* v_moreGlobalServerArgs_2474_; lean_object* v_srcDir_2475_; lean_object* v_buildDir_2476_; lean_object* v_leanLibDir_2477_; lean_object* v_nativeLibDir_2478_; lean_object* v_binDir_2479_; lean_object* v_irDir_2480_; lean_object* v_releaseRepo_2481_; lean_object* v_buildArchive_2482_; uint8_t v_preferReleaseBuild_2483_; lean_object* v_testDriver_2484_; lean_object* v_testDriverArgs_2485_; lean_object* v_lintDriver_2486_; lean_object* v_lintDriverArgs_2487_; lean_object* v_version_2488_; lean_object* v_versionTags_2489_; lean_object* v_description_2490_; lean_object* v_keywords_2491_; lean_object* v_license_2492_; lean_object* v_licenseFiles_2493_; lean_object* v_readmeFile_2494_; uint8_t v_reservoir_2495_; lean_object* v_enableArtifactCache_x3f_2496_; lean_object* v_restoreAllArtifacts_x3f_2497_; uint8_t v_libPrefixOnWindows_2498_; uint8_t v_allowImportAll_2499_; uint8_t v_fixedToolchain_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
v_toWorkspaceConfig_2469_ = lean_ctor_get(v_cfg_2468_, 0);
v_toLeanConfig_2470_ = lean_ctor_get(v_cfg_2468_, 1);
v_bootstrap_2471_ = lean_ctor_get_uint8(v_cfg_2468_, sizeof(void*)*26);
v_extraDepTargets_2472_ = lean_ctor_get(v_cfg_2468_, 2);
v_precompileModules_2473_ = lean_ctor_get_uint8(v_cfg_2468_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2474_ = lean_ctor_get(v_cfg_2468_, 3);
v_srcDir_2475_ = lean_ctor_get(v_cfg_2468_, 4);
v_buildDir_2476_ = lean_ctor_get(v_cfg_2468_, 5);
v_leanLibDir_2477_ = lean_ctor_get(v_cfg_2468_, 6);
v_nativeLibDir_2478_ = lean_ctor_get(v_cfg_2468_, 7);
v_binDir_2479_ = lean_ctor_get(v_cfg_2468_, 8);
v_irDir_2480_ = lean_ctor_get(v_cfg_2468_, 9);
v_releaseRepo_2481_ = lean_ctor_get(v_cfg_2468_, 10);
v_buildArchive_2482_ = lean_ctor_get(v_cfg_2468_, 11);
v_preferReleaseBuild_2483_ = lean_ctor_get_uint8(v_cfg_2468_, sizeof(void*)*26 + 2);
v_testDriver_2484_ = lean_ctor_get(v_cfg_2468_, 12);
v_testDriverArgs_2485_ = lean_ctor_get(v_cfg_2468_, 13);
v_lintDriver_2486_ = lean_ctor_get(v_cfg_2468_, 14);
v_lintDriverArgs_2487_ = lean_ctor_get(v_cfg_2468_, 15);
v_version_2488_ = lean_ctor_get(v_cfg_2468_, 16);
v_versionTags_2489_ = lean_ctor_get(v_cfg_2468_, 17);
v_description_2490_ = lean_ctor_get(v_cfg_2468_, 18);
v_keywords_2491_ = lean_ctor_get(v_cfg_2468_, 19);
v_license_2492_ = lean_ctor_get(v_cfg_2468_, 21);
v_licenseFiles_2493_ = lean_ctor_get(v_cfg_2468_, 22);
v_readmeFile_2494_ = lean_ctor_get(v_cfg_2468_, 23);
v_reservoir_2495_ = lean_ctor_get_uint8(v_cfg_2468_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2496_ = lean_ctor_get(v_cfg_2468_, 24);
v_restoreAllArtifacts_x3f_2497_ = lean_ctor_get(v_cfg_2468_, 25);
v_libPrefixOnWindows_2498_ = lean_ctor_get_uint8(v_cfg_2468_, sizeof(void*)*26 + 4);
v_allowImportAll_2499_ = lean_ctor_get_uint8(v_cfg_2468_, sizeof(void*)*26 + 5);
v_fixedToolchain_2500_ = lean_ctor_get_uint8(v_cfg_2468_, sizeof(void*)*26 + 6);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_cfg_2468_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v_cfg_2468_, 20);
lean_dec(v_unused_2508_);
v___x_2502_ = v_cfg_2468_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2497_);
lean_inc(v_enableArtifactCache_x3f_2496_);
lean_inc(v_readmeFile_2494_);
lean_inc(v_licenseFiles_2493_);
lean_inc(v_license_2492_);
lean_inc(v_keywords_2491_);
lean_inc(v_description_2490_);
lean_inc(v_versionTags_2489_);
lean_inc(v_version_2488_);
lean_inc(v_lintDriverArgs_2487_);
lean_inc(v_lintDriver_2486_);
lean_inc(v_testDriverArgs_2485_);
lean_inc(v_testDriver_2484_);
lean_inc(v_buildArchive_2482_);
lean_inc(v_releaseRepo_2481_);
lean_inc(v_irDir_2480_);
lean_inc(v_binDir_2479_);
lean_inc(v_nativeLibDir_2478_);
lean_inc(v_leanLibDir_2477_);
lean_inc(v_buildDir_2476_);
lean_inc(v_srcDir_2475_);
lean_inc(v_moreGlobalServerArgs_2474_);
lean_inc(v_extraDepTargets_2472_);
lean_inc(v_toLeanConfig_2470_);
lean_inc(v_toWorkspaceConfig_2469_);
lean_dec(v_cfg_2468_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 20, v_val_2467_);
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_toWorkspaceConfig_2469_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_toLeanConfig_2470_);
lean_ctor_set(v_reuseFailAlloc_2506_, 2, v_extraDepTargets_2472_);
lean_ctor_set(v_reuseFailAlloc_2506_, 3, v_moreGlobalServerArgs_2474_);
lean_ctor_set(v_reuseFailAlloc_2506_, 4, v_srcDir_2475_);
lean_ctor_set(v_reuseFailAlloc_2506_, 5, v_buildDir_2476_);
lean_ctor_set(v_reuseFailAlloc_2506_, 6, v_leanLibDir_2477_);
lean_ctor_set(v_reuseFailAlloc_2506_, 7, v_nativeLibDir_2478_);
lean_ctor_set(v_reuseFailAlloc_2506_, 8, v_binDir_2479_);
lean_ctor_set(v_reuseFailAlloc_2506_, 9, v_irDir_2480_);
lean_ctor_set(v_reuseFailAlloc_2506_, 10, v_releaseRepo_2481_);
lean_ctor_set(v_reuseFailAlloc_2506_, 11, v_buildArchive_2482_);
lean_ctor_set(v_reuseFailAlloc_2506_, 12, v_testDriver_2484_);
lean_ctor_set(v_reuseFailAlloc_2506_, 13, v_testDriverArgs_2485_);
lean_ctor_set(v_reuseFailAlloc_2506_, 14, v_lintDriver_2486_);
lean_ctor_set(v_reuseFailAlloc_2506_, 15, v_lintDriverArgs_2487_);
lean_ctor_set(v_reuseFailAlloc_2506_, 16, v_version_2488_);
lean_ctor_set(v_reuseFailAlloc_2506_, 17, v_versionTags_2489_);
lean_ctor_set(v_reuseFailAlloc_2506_, 18, v_description_2490_);
lean_ctor_set(v_reuseFailAlloc_2506_, 19, v_keywords_2491_);
lean_ctor_set(v_reuseFailAlloc_2506_, 20, v_val_2467_);
lean_ctor_set(v_reuseFailAlloc_2506_, 21, v_license_2492_);
lean_ctor_set(v_reuseFailAlloc_2506_, 22, v_licenseFiles_2493_);
lean_ctor_set(v_reuseFailAlloc_2506_, 23, v_readmeFile_2494_);
lean_ctor_set(v_reuseFailAlloc_2506_, 24, v_enableArtifactCache_x3f_2496_);
lean_ctor_set(v_reuseFailAlloc_2506_, 25, v_restoreAllArtifacts_x3f_2497_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, sizeof(void*)*26, v_bootstrap_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, sizeof(void*)*26 + 1, v_precompileModules_2473_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, sizeof(void*)*26 + 3, v_reservoir_2495_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2498_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, sizeof(void*)*26 + 5, v_allowImportAll_2499_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, sizeof(void*)*26 + 6, v_fixedToolchain_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__2(lean_object* v_f_2509_, lean_object* v_cfg_2510_){
_start:
{
lean_object* v_toWorkspaceConfig_2511_; lean_object* v_toLeanConfig_2512_; uint8_t v_bootstrap_2513_; lean_object* v_extraDepTargets_2514_; uint8_t v_precompileModules_2515_; lean_object* v_moreGlobalServerArgs_2516_; lean_object* v_srcDir_2517_; lean_object* v_buildDir_2518_; lean_object* v_leanLibDir_2519_; lean_object* v_nativeLibDir_2520_; lean_object* v_binDir_2521_; lean_object* v_irDir_2522_; lean_object* v_releaseRepo_2523_; lean_object* v_buildArchive_2524_; uint8_t v_preferReleaseBuild_2525_; lean_object* v_testDriver_2526_; lean_object* v_testDriverArgs_2527_; lean_object* v_lintDriver_2528_; lean_object* v_lintDriverArgs_2529_; lean_object* v_version_2530_; lean_object* v_versionTags_2531_; lean_object* v_description_2532_; lean_object* v_keywords_2533_; lean_object* v_homepage_2534_; lean_object* v_license_2535_; lean_object* v_licenseFiles_2536_; lean_object* v_readmeFile_2537_; uint8_t v_reservoir_2538_; lean_object* v_enableArtifactCache_x3f_2539_; lean_object* v_restoreAllArtifacts_x3f_2540_; uint8_t v_libPrefixOnWindows_2541_; uint8_t v_allowImportAll_2542_; uint8_t v_fixedToolchain_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2551_; 
v_toWorkspaceConfig_2511_ = lean_ctor_get(v_cfg_2510_, 0);
v_toLeanConfig_2512_ = lean_ctor_get(v_cfg_2510_, 1);
v_bootstrap_2513_ = lean_ctor_get_uint8(v_cfg_2510_, sizeof(void*)*26);
v_extraDepTargets_2514_ = lean_ctor_get(v_cfg_2510_, 2);
v_precompileModules_2515_ = lean_ctor_get_uint8(v_cfg_2510_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2516_ = lean_ctor_get(v_cfg_2510_, 3);
v_srcDir_2517_ = lean_ctor_get(v_cfg_2510_, 4);
v_buildDir_2518_ = lean_ctor_get(v_cfg_2510_, 5);
v_leanLibDir_2519_ = lean_ctor_get(v_cfg_2510_, 6);
v_nativeLibDir_2520_ = lean_ctor_get(v_cfg_2510_, 7);
v_binDir_2521_ = lean_ctor_get(v_cfg_2510_, 8);
v_irDir_2522_ = lean_ctor_get(v_cfg_2510_, 9);
v_releaseRepo_2523_ = lean_ctor_get(v_cfg_2510_, 10);
v_buildArchive_2524_ = lean_ctor_get(v_cfg_2510_, 11);
v_preferReleaseBuild_2525_ = lean_ctor_get_uint8(v_cfg_2510_, sizeof(void*)*26 + 2);
v_testDriver_2526_ = lean_ctor_get(v_cfg_2510_, 12);
v_testDriverArgs_2527_ = lean_ctor_get(v_cfg_2510_, 13);
v_lintDriver_2528_ = lean_ctor_get(v_cfg_2510_, 14);
v_lintDriverArgs_2529_ = lean_ctor_get(v_cfg_2510_, 15);
v_version_2530_ = lean_ctor_get(v_cfg_2510_, 16);
v_versionTags_2531_ = lean_ctor_get(v_cfg_2510_, 17);
v_description_2532_ = lean_ctor_get(v_cfg_2510_, 18);
v_keywords_2533_ = lean_ctor_get(v_cfg_2510_, 19);
v_homepage_2534_ = lean_ctor_get(v_cfg_2510_, 20);
v_license_2535_ = lean_ctor_get(v_cfg_2510_, 21);
v_licenseFiles_2536_ = lean_ctor_get(v_cfg_2510_, 22);
v_readmeFile_2537_ = lean_ctor_get(v_cfg_2510_, 23);
v_reservoir_2538_ = lean_ctor_get_uint8(v_cfg_2510_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2539_ = lean_ctor_get(v_cfg_2510_, 24);
v_restoreAllArtifacts_x3f_2540_ = lean_ctor_get(v_cfg_2510_, 25);
v_libPrefixOnWindows_2541_ = lean_ctor_get_uint8(v_cfg_2510_, sizeof(void*)*26 + 4);
v_allowImportAll_2542_ = lean_ctor_get_uint8(v_cfg_2510_, sizeof(void*)*26 + 5);
v_fixedToolchain_2543_ = lean_ctor_get_uint8(v_cfg_2510_, sizeof(void*)*26 + 6);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_cfg_2510_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2545_ = v_cfg_2510_;
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2540_);
lean_inc(v_enableArtifactCache_x3f_2539_);
lean_inc(v_readmeFile_2537_);
lean_inc(v_licenseFiles_2536_);
lean_inc(v_license_2535_);
lean_inc(v_homepage_2534_);
lean_inc(v_keywords_2533_);
lean_inc(v_description_2532_);
lean_inc(v_versionTags_2531_);
lean_inc(v_version_2530_);
lean_inc(v_lintDriverArgs_2529_);
lean_inc(v_lintDriver_2528_);
lean_inc(v_testDriverArgs_2527_);
lean_inc(v_testDriver_2526_);
lean_inc(v_buildArchive_2524_);
lean_inc(v_releaseRepo_2523_);
lean_inc(v_irDir_2522_);
lean_inc(v_binDir_2521_);
lean_inc(v_nativeLibDir_2520_);
lean_inc(v_leanLibDir_2519_);
lean_inc(v_buildDir_2518_);
lean_inc(v_srcDir_2517_);
lean_inc(v_moreGlobalServerArgs_2516_);
lean_inc(v_extraDepTargets_2514_);
lean_inc(v_toLeanConfig_2512_);
lean_inc(v_toWorkspaceConfig_2511_);
lean_dec(v_cfg_2510_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___x_2547_ = lean_apply_1(v_f_2509_, v_homepage_2534_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 20, v___x_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_toWorkspaceConfig_2511_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_toLeanConfig_2512_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_extraDepTargets_2514_);
lean_ctor_set(v_reuseFailAlloc_2550_, 3, v_moreGlobalServerArgs_2516_);
lean_ctor_set(v_reuseFailAlloc_2550_, 4, v_srcDir_2517_);
lean_ctor_set(v_reuseFailAlloc_2550_, 5, v_buildDir_2518_);
lean_ctor_set(v_reuseFailAlloc_2550_, 6, v_leanLibDir_2519_);
lean_ctor_set(v_reuseFailAlloc_2550_, 7, v_nativeLibDir_2520_);
lean_ctor_set(v_reuseFailAlloc_2550_, 8, v_binDir_2521_);
lean_ctor_set(v_reuseFailAlloc_2550_, 9, v_irDir_2522_);
lean_ctor_set(v_reuseFailAlloc_2550_, 10, v_releaseRepo_2523_);
lean_ctor_set(v_reuseFailAlloc_2550_, 11, v_buildArchive_2524_);
lean_ctor_set(v_reuseFailAlloc_2550_, 12, v_testDriver_2526_);
lean_ctor_set(v_reuseFailAlloc_2550_, 13, v_testDriverArgs_2527_);
lean_ctor_set(v_reuseFailAlloc_2550_, 14, v_lintDriver_2528_);
lean_ctor_set(v_reuseFailAlloc_2550_, 15, v_lintDriverArgs_2529_);
lean_ctor_set(v_reuseFailAlloc_2550_, 16, v_version_2530_);
lean_ctor_set(v_reuseFailAlloc_2550_, 17, v_versionTags_2531_);
lean_ctor_set(v_reuseFailAlloc_2550_, 18, v_description_2532_);
lean_ctor_set(v_reuseFailAlloc_2550_, 19, v_keywords_2533_);
lean_ctor_set(v_reuseFailAlloc_2550_, 20, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2550_, 21, v_license_2535_);
lean_ctor_set(v_reuseFailAlloc_2550_, 22, v_licenseFiles_2536_);
lean_ctor_set(v_reuseFailAlloc_2550_, 23, v_readmeFile_2537_);
lean_ctor_set(v_reuseFailAlloc_2550_, 24, v_enableArtifactCache_x3f_2539_);
lean_ctor_set(v_reuseFailAlloc_2550_, 25, v_restoreAllArtifacts_x3f_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2550_, sizeof(void*)*26, v_bootstrap_2513_);
lean_ctor_set_uint8(v_reuseFailAlloc_2550_, sizeof(void*)*26 + 1, v_precompileModules_2515_);
lean_ctor_set_uint8(v_reuseFailAlloc_2550_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2525_);
lean_ctor_set_uint8(v_reuseFailAlloc_2550_, sizeof(void*)*26 + 3, v_reservoir_2538_);
lean_ctor_set_uint8(v_reuseFailAlloc_2550_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2541_);
lean_ctor_set_uint8(v_reuseFailAlloc_2550_, sizeof(void*)*26 + 5, v_allowImportAll_2542_);
lean_ctor_set_uint8(v_reuseFailAlloc_2550_, sizeof(void*)*26 + 6, v_fixedToolchain_2543_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object* v_p_2560_, lean_object* v_n_2561_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = ((lean_object*)(l_Lake_PackageConfig_homepage___proj___closed__3));
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object* v_p_2563_, lean_object* v_n_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lake_PackageConfig_homepage___proj(v_p_2563_, v_n_2564_);
lean_dec(v_n_2564_);
lean_dec(v_p_2563_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object* v_p_2566_, lean_object* v_n_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lake_PackageConfig_homepage___proj(v_p_2566_, v_n_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object* v_p_2569_, lean_object* v_n_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lake_PackageConfig_homepage_instConfigField(v_p_2569_, v_n_2570_);
lean_dec(v_n_2570_);
lean_dec(v_p_2569_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0(lean_object* v_cfg_2572_){
_start:
{
lean_object* v_license_2573_; 
v_license_2573_ = lean_ctor_get(v_cfg_2572_, 21);
lean_inc_ref(v_license_2573_);
return v_license_2573_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0___boxed(lean_object* v_cfg_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lake_PackageConfig_license___proj___lam__0(v_cfg_2574_);
lean_dec_ref(v_cfg_2574_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__1(lean_object* v_val_2576_, lean_object* v_cfg_2577_){
_start:
{
lean_object* v_toWorkspaceConfig_2578_; lean_object* v_toLeanConfig_2579_; uint8_t v_bootstrap_2580_; lean_object* v_extraDepTargets_2581_; uint8_t v_precompileModules_2582_; lean_object* v_moreGlobalServerArgs_2583_; lean_object* v_srcDir_2584_; lean_object* v_buildDir_2585_; lean_object* v_leanLibDir_2586_; lean_object* v_nativeLibDir_2587_; lean_object* v_binDir_2588_; lean_object* v_irDir_2589_; lean_object* v_releaseRepo_2590_; lean_object* v_buildArchive_2591_; uint8_t v_preferReleaseBuild_2592_; lean_object* v_testDriver_2593_; lean_object* v_testDriverArgs_2594_; lean_object* v_lintDriver_2595_; lean_object* v_lintDriverArgs_2596_; lean_object* v_version_2597_; lean_object* v_versionTags_2598_; lean_object* v_description_2599_; lean_object* v_keywords_2600_; lean_object* v_homepage_2601_; lean_object* v_licenseFiles_2602_; lean_object* v_readmeFile_2603_; uint8_t v_reservoir_2604_; lean_object* v_enableArtifactCache_x3f_2605_; lean_object* v_restoreAllArtifacts_x3f_2606_; uint8_t v_libPrefixOnWindows_2607_; uint8_t v_allowImportAll_2608_; uint8_t v_fixedToolchain_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_toWorkspaceConfig_2578_ = lean_ctor_get(v_cfg_2577_, 0);
v_toLeanConfig_2579_ = lean_ctor_get(v_cfg_2577_, 1);
v_bootstrap_2580_ = lean_ctor_get_uint8(v_cfg_2577_, sizeof(void*)*26);
v_extraDepTargets_2581_ = lean_ctor_get(v_cfg_2577_, 2);
v_precompileModules_2582_ = lean_ctor_get_uint8(v_cfg_2577_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2583_ = lean_ctor_get(v_cfg_2577_, 3);
v_srcDir_2584_ = lean_ctor_get(v_cfg_2577_, 4);
v_buildDir_2585_ = lean_ctor_get(v_cfg_2577_, 5);
v_leanLibDir_2586_ = lean_ctor_get(v_cfg_2577_, 6);
v_nativeLibDir_2587_ = lean_ctor_get(v_cfg_2577_, 7);
v_binDir_2588_ = lean_ctor_get(v_cfg_2577_, 8);
v_irDir_2589_ = lean_ctor_get(v_cfg_2577_, 9);
v_releaseRepo_2590_ = lean_ctor_get(v_cfg_2577_, 10);
v_buildArchive_2591_ = lean_ctor_get(v_cfg_2577_, 11);
v_preferReleaseBuild_2592_ = lean_ctor_get_uint8(v_cfg_2577_, sizeof(void*)*26 + 2);
v_testDriver_2593_ = lean_ctor_get(v_cfg_2577_, 12);
v_testDriverArgs_2594_ = lean_ctor_get(v_cfg_2577_, 13);
v_lintDriver_2595_ = lean_ctor_get(v_cfg_2577_, 14);
v_lintDriverArgs_2596_ = lean_ctor_get(v_cfg_2577_, 15);
v_version_2597_ = lean_ctor_get(v_cfg_2577_, 16);
v_versionTags_2598_ = lean_ctor_get(v_cfg_2577_, 17);
v_description_2599_ = lean_ctor_get(v_cfg_2577_, 18);
v_keywords_2600_ = lean_ctor_get(v_cfg_2577_, 19);
v_homepage_2601_ = lean_ctor_get(v_cfg_2577_, 20);
v_licenseFiles_2602_ = lean_ctor_get(v_cfg_2577_, 22);
v_readmeFile_2603_ = lean_ctor_get(v_cfg_2577_, 23);
v_reservoir_2604_ = lean_ctor_get_uint8(v_cfg_2577_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2605_ = lean_ctor_get(v_cfg_2577_, 24);
v_restoreAllArtifacts_x3f_2606_ = lean_ctor_get(v_cfg_2577_, 25);
v_libPrefixOnWindows_2607_ = lean_ctor_get_uint8(v_cfg_2577_, sizeof(void*)*26 + 4);
v_allowImportAll_2608_ = lean_ctor_get_uint8(v_cfg_2577_, sizeof(void*)*26 + 5);
v_fixedToolchain_2609_ = lean_ctor_get_uint8(v_cfg_2577_, sizeof(void*)*26 + 6);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_cfg_2577_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; 
v_unused_2617_ = lean_ctor_get(v_cfg_2577_, 21);
lean_dec(v_unused_2617_);
v___x_2611_ = v_cfg_2577_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2606_);
lean_inc(v_enableArtifactCache_x3f_2605_);
lean_inc(v_readmeFile_2603_);
lean_inc(v_licenseFiles_2602_);
lean_inc(v_homepage_2601_);
lean_inc(v_keywords_2600_);
lean_inc(v_description_2599_);
lean_inc(v_versionTags_2598_);
lean_inc(v_version_2597_);
lean_inc(v_lintDriverArgs_2596_);
lean_inc(v_lintDriver_2595_);
lean_inc(v_testDriverArgs_2594_);
lean_inc(v_testDriver_2593_);
lean_inc(v_buildArchive_2591_);
lean_inc(v_releaseRepo_2590_);
lean_inc(v_irDir_2589_);
lean_inc(v_binDir_2588_);
lean_inc(v_nativeLibDir_2587_);
lean_inc(v_leanLibDir_2586_);
lean_inc(v_buildDir_2585_);
lean_inc(v_srcDir_2584_);
lean_inc(v_moreGlobalServerArgs_2583_);
lean_inc(v_extraDepTargets_2581_);
lean_inc(v_toLeanConfig_2579_);
lean_inc(v_toWorkspaceConfig_2578_);
lean_dec(v_cfg_2577_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 21, v_val_2576_);
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_toWorkspaceConfig_2578_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_toLeanConfig_2579_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_extraDepTargets_2581_);
lean_ctor_set(v_reuseFailAlloc_2615_, 3, v_moreGlobalServerArgs_2583_);
lean_ctor_set(v_reuseFailAlloc_2615_, 4, v_srcDir_2584_);
lean_ctor_set(v_reuseFailAlloc_2615_, 5, v_buildDir_2585_);
lean_ctor_set(v_reuseFailAlloc_2615_, 6, v_leanLibDir_2586_);
lean_ctor_set(v_reuseFailAlloc_2615_, 7, v_nativeLibDir_2587_);
lean_ctor_set(v_reuseFailAlloc_2615_, 8, v_binDir_2588_);
lean_ctor_set(v_reuseFailAlloc_2615_, 9, v_irDir_2589_);
lean_ctor_set(v_reuseFailAlloc_2615_, 10, v_releaseRepo_2590_);
lean_ctor_set(v_reuseFailAlloc_2615_, 11, v_buildArchive_2591_);
lean_ctor_set(v_reuseFailAlloc_2615_, 12, v_testDriver_2593_);
lean_ctor_set(v_reuseFailAlloc_2615_, 13, v_testDriverArgs_2594_);
lean_ctor_set(v_reuseFailAlloc_2615_, 14, v_lintDriver_2595_);
lean_ctor_set(v_reuseFailAlloc_2615_, 15, v_lintDriverArgs_2596_);
lean_ctor_set(v_reuseFailAlloc_2615_, 16, v_version_2597_);
lean_ctor_set(v_reuseFailAlloc_2615_, 17, v_versionTags_2598_);
lean_ctor_set(v_reuseFailAlloc_2615_, 18, v_description_2599_);
lean_ctor_set(v_reuseFailAlloc_2615_, 19, v_keywords_2600_);
lean_ctor_set(v_reuseFailAlloc_2615_, 20, v_homepage_2601_);
lean_ctor_set(v_reuseFailAlloc_2615_, 21, v_val_2576_);
lean_ctor_set(v_reuseFailAlloc_2615_, 22, v_licenseFiles_2602_);
lean_ctor_set(v_reuseFailAlloc_2615_, 23, v_readmeFile_2603_);
lean_ctor_set(v_reuseFailAlloc_2615_, 24, v_enableArtifactCache_x3f_2605_);
lean_ctor_set(v_reuseFailAlloc_2615_, 25, v_restoreAllArtifacts_x3f_2606_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*26, v_bootstrap_2580_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*26 + 1, v_precompileModules_2582_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*26 + 3, v_reservoir_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2607_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*26 + 5, v_allowImportAll_2608_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*26 + 6, v_fixedToolchain_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__2(lean_object* v_f_2618_, lean_object* v_cfg_2619_){
_start:
{
lean_object* v_toWorkspaceConfig_2620_; lean_object* v_toLeanConfig_2621_; uint8_t v_bootstrap_2622_; lean_object* v_extraDepTargets_2623_; uint8_t v_precompileModules_2624_; lean_object* v_moreGlobalServerArgs_2625_; lean_object* v_srcDir_2626_; lean_object* v_buildDir_2627_; lean_object* v_leanLibDir_2628_; lean_object* v_nativeLibDir_2629_; lean_object* v_binDir_2630_; lean_object* v_irDir_2631_; lean_object* v_releaseRepo_2632_; lean_object* v_buildArchive_2633_; uint8_t v_preferReleaseBuild_2634_; lean_object* v_testDriver_2635_; lean_object* v_testDriverArgs_2636_; lean_object* v_lintDriver_2637_; lean_object* v_lintDriverArgs_2638_; lean_object* v_version_2639_; lean_object* v_versionTags_2640_; lean_object* v_description_2641_; lean_object* v_keywords_2642_; lean_object* v_homepage_2643_; lean_object* v_license_2644_; lean_object* v_licenseFiles_2645_; lean_object* v_readmeFile_2646_; uint8_t v_reservoir_2647_; lean_object* v_enableArtifactCache_x3f_2648_; lean_object* v_restoreAllArtifacts_x3f_2649_; uint8_t v_libPrefixOnWindows_2650_; uint8_t v_allowImportAll_2651_; uint8_t v_fixedToolchain_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2660_; 
v_toWorkspaceConfig_2620_ = lean_ctor_get(v_cfg_2619_, 0);
v_toLeanConfig_2621_ = lean_ctor_get(v_cfg_2619_, 1);
v_bootstrap_2622_ = lean_ctor_get_uint8(v_cfg_2619_, sizeof(void*)*26);
v_extraDepTargets_2623_ = lean_ctor_get(v_cfg_2619_, 2);
v_precompileModules_2624_ = lean_ctor_get_uint8(v_cfg_2619_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2625_ = lean_ctor_get(v_cfg_2619_, 3);
v_srcDir_2626_ = lean_ctor_get(v_cfg_2619_, 4);
v_buildDir_2627_ = lean_ctor_get(v_cfg_2619_, 5);
v_leanLibDir_2628_ = lean_ctor_get(v_cfg_2619_, 6);
v_nativeLibDir_2629_ = lean_ctor_get(v_cfg_2619_, 7);
v_binDir_2630_ = lean_ctor_get(v_cfg_2619_, 8);
v_irDir_2631_ = lean_ctor_get(v_cfg_2619_, 9);
v_releaseRepo_2632_ = lean_ctor_get(v_cfg_2619_, 10);
v_buildArchive_2633_ = lean_ctor_get(v_cfg_2619_, 11);
v_preferReleaseBuild_2634_ = lean_ctor_get_uint8(v_cfg_2619_, sizeof(void*)*26 + 2);
v_testDriver_2635_ = lean_ctor_get(v_cfg_2619_, 12);
v_testDriverArgs_2636_ = lean_ctor_get(v_cfg_2619_, 13);
v_lintDriver_2637_ = lean_ctor_get(v_cfg_2619_, 14);
v_lintDriverArgs_2638_ = lean_ctor_get(v_cfg_2619_, 15);
v_version_2639_ = lean_ctor_get(v_cfg_2619_, 16);
v_versionTags_2640_ = lean_ctor_get(v_cfg_2619_, 17);
v_description_2641_ = lean_ctor_get(v_cfg_2619_, 18);
v_keywords_2642_ = lean_ctor_get(v_cfg_2619_, 19);
v_homepage_2643_ = lean_ctor_get(v_cfg_2619_, 20);
v_license_2644_ = lean_ctor_get(v_cfg_2619_, 21);
v_licenseFiles_2645_ = lean_ctor_get(v_cfg_2619_, 22);
v_readmeFile_2646_ = lean_ctor_get(v_cfg_2619_, 23);
v_reservoir_2647_ = lean_ctor_get_uint8(v_cfg_2619_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2648_ = lean_ctor_get(v_cfg_2619_, 24);
v_restoreAllArtifacts_x3f_2649_ = lean_ctor_get(v_cfg_2619_, 25);
v_libPrefixOnWindows_2650_ = lean_ctor_get_uint8(v_cfg_2619_, sizeof(void*)*26 + 4);
v_allowImportAll_2651_ = lean_ctor_get_uint8(v_cfg_2619_, sizeof(void*)*26 + 5);
v_fixedToolchain_2652_ = lean_ctor_get_uint8(v_cfg_2619_, sizeof(void*)*26 + 6);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_cfg_2619_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2654_ = v_cfg_2619_;
v_isShared_2655_ = v_isSharedCheck_2660_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2649_);
lean_inc(v_enableArtifactCache_x3f_2648_);
lean_inc(v_readmeFile_2646_);
lean_inc(v_licenseFiles_2645_);
lean_inc(v_license_2644_);
lean_inc(v_homepage_2643_);
lean_inc(v_keywords_2642_);
lean_inc(v_description_2641_);
lean_inc(v_versionTags_2640_);
lean_inc(v_version_2639_);
lean_inc(v_lintDriverArgs_2638_);
lean_inc(v_lintDriver_2637_);
lean_inc(v_testDriverArgs_2636_);
lean_inc(v_testDriver_2635_);
lean_inc(v_buildArchive_2633_);
lean_inc(v_releaseRepo_2632_);
lean_inc(v_irDir_2631_);
lean_inc(v_binDir_2630_);
lean_inc(v_nativeLibDir_2629_);
lean_inc(v_leanLibDir_2628_);
lean_inc(v_buildDir_2627_);
lean_inc(v_srcDir_2626_);
lean_inc(v_moreGlobalServerArgs_2625_);
lean_inc(v_extraDepTargets_2623_);
lean_inc(v_toLeanConfig_2621_);
lean_inc(v_toWorkspaceConfig_2620_);
lean_dec(v_cfg_2619_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2660_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2656_ = lean_apply_1(v_f_2618_, v_license_2644_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 21, v___x_2656_);
v___x_2658_ = v___x_2654_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_toWorkspaceConfig_2620_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_toLeanConfig_2621_);
lean_ctor_set(v_reuseFailAlloc_2659_, 2, v_extraDepTargets_2623_);
lean_ctor_set(v_reuseFailAlloc_2659_, 3, v_moreGlobalServerArgs_2625_);
lean_ctor_set(v_reuseFailAlloc_2659_, 4, v_srcDir_2626_);
lean_ctor_set(v_reuseFailAlloc_2659_, 5, v_buildDir_2627_);
lean_ctor_set(v_reuseFailAlloc_2659_, 6, v_leanLibDir_2628_);
lean_ctor_set(v_reuseFailAlloc_2659_, 7, v_nativeLibDir_2629_);
lean_ctor_set(v_reuseFailAlloc_2659_, 8, v_binDir_2630_);
lean_ctor_set(v_reuseFailAlloc_2659_, 9, v_irDir_2631_);
lean_ctor_set(v_reuseFailAlloc_2659_, 10, v_releaseRepo_2632_);
lean_ctor_set(v_reuseFailAlloc_2659_, 11, v_buildArchive_2633_);
lean_ctor_set(v_reuseFailAlloc_2659_, 12, v_testDriver_2635_);
lean_ctor_set(v_reuseFailAlloc_2659_, 13, v_testDriverArgs_2636_);
lean_ctor_set(v_reuseFailAlloc_2659_, 14, v_lintDriver_2637_);
lean_ctor_set(v_reuseFailAlloc_2659_, 15, v_lintDriverArgs_2638_);
lean_ctor_set(v_reuseFailAlloc_2659_, 16, v_version_2639_);
lean_ctor_set(v_reuseFailAlloc_2659_, 17, v_versionTags_2640_);
lean_ctor_set(v_reuseFailAlloc_2659_, 18, v_description_2641_);
lean_ctor_set(v_reuseFailAlloc_2659_, 19, v_keywords_2642_);
lean_ctor_set(v_reuseFailAlloc_2659_, 20, v_homepage_2643_);
lean_ctor_set(v_reuseFailAlloc_2659_, 21, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2659_, 22, v_licenseFiles_2645_);
lean_ctor_set(v_reuseFailAlloc_2659_, 23, v_readmeFile_2646_);
lean_ctor_set(v_reuseFailAlloc_2659_, 24, v_enableArtifactCache_x3f_2648_);
lean_ctor_set(v_reuseFailAlloc_2659_, 25, v_restoreAllArtifacts_x3f_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2659_, sizeof(void*)*26, v_bootstrap_2622_);
lean_ctor_set_uint8(v_reuseFailAlloc_2659_, sizeof(void*)*26 + 1, v_precompileModules_2624_);
lean_ctor_set_uint8(v_reuseFailAlloc_2659_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2659_, sizeof(void*)*26 + 3, v_reservoir_2647_);
lean_ctor_set_uint8(v_reuseFailAlloc_2659_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2659_, sizeof(void*)*26 + 5, v_allowImportAll_2651_);
lean_ctor_set_uint8(v_reuseFailAlloc_2659_, sizeof(void*)*26 + 6, v_fixedToolchain_2652_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object* v_p_2669_, lean_object* v_n_2670_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = ((lean_object*)(l_Lake_PackageConfig_license___proj___closed__3));
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object* v_p_2672_, lean_object* v_n_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lake_PackageConfig_license___proj(v_p_2672_, v_n_2673_);
lean_dec(v_n_2673_);
lean_dec(v_p_2672_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object* v_p_2675_, lean_object* v_n_2676_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Lake_PackageConfig_license___proj(v_p_2675_, v_n_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object* v_p_2678_, lean_object* v_n_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lake_PackageConfig_license_instConfigField(v_p_2678_, v_n_2679_);
lean_dec(v_n_2679_);
lean_dec(v_p_2678_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0(lean_object* v_cfg_2681_){
_start:
{
lean_object* v_licenseFiles_2682_; 
v_licenseFiles_2682_ = lean_ctor_get(v_cfg_2681_, 22);
lean_inc_ref(v_licenseFiles_2682_);
return v_licenseFiles_2682_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0___boxed(lean_object* v_cfg_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Lake_PackageConfig_licenseFiles___proj___lam__0(v_cfg_2683_);
lean_dec_ref(v_cfg_2683_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__1(lean_object* v_val_2685_, lean_object* v_cfg_2686_){
_start:
{
lean_object* v_toWorkspaceConfig_2687_; lean_object* v_toLeanConfig_2688_; uint8_t v_bootstrap_2689_; lean_object* v_extraDepTargets_2690_; uint8_t v_precompileModules_2691_; lean_object* v_moreGlobalServerArgs_2692_; lean_object* v_srcDir_2693_; lean_object* v_buildDir_2694_; lean_object* v_leanLibDir_2695_; lean_object* v_nativeLibDir_2696_; lean_object* v_binDir_2697_; lean_object* v_irDir_2698_; lean_object* v_releaseRepo_2699_; lean_object* v_buildArchive_2700_; uint8_t v_preferReleaseBuild_2701_; lean_object* v_testDriver_2702_; lean_object* v_testDriverArgs_2703_; lean_object* v_lintDriver_2704_; lean_object* v_lintDriverArgs_2705_; lean_object* v_version_2706_; lean_object* v_versionTags_2707_; lean_object* v_description_2708_; lean_object* v_keywords_2709_; lean_object* v_homepage_2710_; lean_object* v_license_2711_; lean_object* v_readmeFile_2712_; uint8_t v_reservoir_2713_; lean_object* v_enableArtifactCache_x3f_2714_; lean_object* v_restoreAllArtifacts_x3f_2715_; uint8_t v_libPrefixOnWindows_2716_; uint8_t v_allowImportAll_2717_; uint8_t v_fixedToolchain_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
v_toWorkspaceConfig_2687_ = lean_ctor_get(v_cfg_2686_, 0);
v_toLeanConfig_2688_ = lean_ctor_get(v_cfg_2686_, 1);
v_bootstrap_2689_ = lean_ctor_get_uint8(v_cfg_2686_, sizeof(void*)*26);
v_extraDepTargets_2690_ = lean_ctor_get(v_cfg_2686_, 2);
v_precompileModules_2691_ = lean_ctor_get_uint8(v_cfg_2686_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2692_ = lean_ctor_get(v_cfg_2686_, 3);
v_srcDir_2693_ = lean_ctor_get(v_cfg_2686_, 4);
v_buildDir_2694_ = lean_ctor_get(v_cfg_2686_, 5);
v_leanLibDir_2695_ = lean_ctor_get(v_cfg_2686_, 6);
v_nativeLibDir_2696_ = lean_ctor_get(v_cfg_2686_, 7);
v_binDir_2697_ = lean_ctor_get(v_cfg_2686_, 8);
v_irDir_2698_ = lean_ctor_get(v_cfg_2686_, 9);
v_releaseRepo_2699_ = lean_ctor_get(v_cfg_2686_, 10);
v_buildArchive_2700_ = lean_ctor_get(v_cfg_2686_, 11);
v_preferReleaseBuild_2701_ = lean_ctor_get_uint8(v_cfg_2686_, sizeof(void*)*26 + 2);
v_testDriver_2702_ = lean_ctor_get(v_cfg_2686_, 12);
v_testDriverArgs_2703_ = lean_ctor_get(v_cfg_2686_, 13);
v_lintDriver_2704_ = lean_ctor_get(v_cfg_2686_, 14);
v_lintDriverArgs_2705_ = lean_ctor_get(v_cfg_2686_, 15);
v_version_2706_ = lean_ctor_get(v_cfg_2686_, 16);
v_versionTags_2707_ = lean_ctor_get(v_cfg_2686_, 17);
v_description_2708_ = lean_ctor_get(v_cfg_2686_, 18);
v_keywords_2709_ = lean_ctor_get(v_cfg_2686_, 19);
v_homepage_2710_ = lean_ctor_get(v_cfg_2686_, 20);
v_license_2711_ = lean_ctor_get(v_cfg_2686_, 21);
v_readmeFile_2712_ = lean_ctor_get(v_cfg_2686_, 23);
v_reservoir_2713_ = lean_ctor_get_uint8(v_cfg_2686_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2714_ = lean_ctor_get(v_cfg_2686_, 24);
v_restoreAllArtifacts_x3f_2715_ = lean_ctor_get(v_cfg_2686_, 25);
v_libPrefixOnWindows_2716_ = lean_ctor_get_uint8(v_cfg_2686_, sizeof(void*)*26 + 4);
v_allowImportAll_2717_ = lean_ctor_get_uint8(v_cfg_2686_, sizeof(void*)*26 + 5);
v_fixedToolchain_2718_ = lean_ctor_get_uint8(v_cfg_2686_, sizeof(void*)*26 + 6);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_cfg_2686_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v_cfg_2686_, 22);
lean_dec(v_unused_2726_);
v___x_2720_ = v_cfg_2686_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2715_);
lean_inc(v_enableArtifactCache_x3f_2714_);
lean_inc(v_readmeFile_2712_);
lean_inc(v_license_2711_);
lean_inc(v_homepage_2710_);
lean_inc(v_keywords_2709_);
lean_inc(v_description_2708_);
lean_inc(v_versionTags_2707_);
lean_inc(v_version_2706_);
lean_inc(v_lintDriverArgs_2705_);
lean_inc(v_lintDriver_2704_);
lean_inc(v_testDriverArgs_2703_);
lean_inc(v_testDriver_2702_);
lean_inc(v_buildArchive_2700_);
lean_inc(v_releaseRepo_2699_);
lean_inc(v_irDir_2698_);
lean_inc(v_binDir_2697_);
lean_inc(v_nativeLibDir_2696_);
lean_inc(v_leanLibDir_2695_);
lean_inc(v_buildDir_2694_);
lean_inc(v_srcDir_2693_);
lean_inc(v_moreGlobalServerArgs_2692_);
lean_inc(v_extraDepTargets_2690_);
lean_inc(v_toLeanConfig_2688_);
lean_inc(v_toWorkspaceConfig_2687_);
lean_dec(v_cfg_2686_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 22, v_val_2685_);
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_toWorkspaceConfig_2687_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_toLeanConfig_2688_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_extraDepTargets_2690_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v_moreGlobalServerArgs_2692_);
lean_ctor_set(v_reuseFailAlloc_2724_, 4, v_srcDir_2693_);
lean_ctor_set(v_reuseFailAlloc_2724_, 5, v_buildDir_2694_);
lean_ctor_set(v_reuseFailAlloc_2724_, 6, v_leanLibDir_2695_);
lean_ctor_set(v_reuseFailAlloc_2724_, 7, v_nativeLibDir_2696_);
lean_ctor_set(v_reuseFailAlloc_2724_, 8, v_binDir_2697_);
lean_ctor_set(v_reuseFailAlloc_2724_, 9, v_irDir_2698_);
lean_ctor_set(v_reuseFailAlloc_2724_, 10, v_releaseRepo_2699_);
lean_ctor_set(v_reuseFailAlloc_2724_, 11, v_buildArchive_2700_);
lean_ctor_set(v_reuseFailAlloc_2724_, 12, v_testDriver_2702_);
lean_ctor_set(v_reuseFailAlloc_2724_, 13, v_testDriverArgs_2703_);
lean_ctor_set(v_reuseFailAlloc_2724_, 14, v_lintDriver_2704_);
lean_ctor_set(v_reuseFailAlloc_2724_, 15, v_lintDriverArgs_2705_);
lean_ctor_set(v_reuseFailAlloc_2724_, 16, v_version_2706_);
lean_ctor_set(v_reuseFailAlloc_2724_, 17, v_versionTags_2707_);
lean_ctor_set(v_reuseFailAlloc_2724_, 18, v_description_2708_);
lean_ctor_set(v_reuseFailAlloc_2724_, 19, v_keywords_2709_);
lean_ctor_set(v_reuseFailAlloc_2724_, 20, v_homepage_2710_);
lean_ctor_set(v_reuseFailAlloc_2724_, 21, v_license_2711_);
lean_ctor_set(v_reuseFailAlloc_2724_, 22, v_val_2685_);
lean_ctor_set(v_reuseFailAlloc_2724_, 23, v_readmeFile_2712_);
lean_ctor_set(v_reuseFailAlloc_2724_, 24, v_enableArtifactCache_x3f_2714_);
lean_ctor_set(v_reuseFailAlloc_2724_, 25, v_restoreAllArtifacts_x3f_2715_);
lean_ctor_set_uint8(v_reuseFailAlloc_2724_, sizeof(void*)*26, v_bootstrap_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2724_, sizeof(void*)*26 + 1, v_precompileModules_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2724_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2724_, sizeof(void*)*26 + 3, v_reservoir_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2724_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2716_);
lean_ctor_set_uint8(v_reuseFailAlloc_2724_, sizeof(void*)*26 + 5, v_allowImportAll_2717_);
lean_ctor_set_uint8(v_reuseFailAlloc_2724_, sizeof(void*)*26 + 6, v_fixedToolchain_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__2(lean_object* v_f_2727_, lean_object* v_cfg_2728_){
_start:
{
lean_object* v_toWorkspaceConfig_2729_; lean_object* v_toLeanConfig_2730_; uint8_t v_bootstrap_2731_; lean_object* v_extraDepTargets_2732_; uint8_t v_precompileModules_2733_; lean_object* v_moreGlobalServerArgs_2734_; lean_object* v_srcDir_2735_; lean_object* v_buildDir_2736_; lean_object* v_leanLibDir_2737_; lean_object* v_nativeLibDir_2738_; lean_object* v_binDir_2739_; lean_object* v_irDir_2740_; lean_object* v_releaseRepo_2741_; lean_object* v_buildArchive_2742_; uint8_t v_preferReleaseBuild_2743_; lean_object* v_testDriver_2744_; lean_object* v_testDriverArgs_2745_; lean_object* v_lintDriver_2746_; lean_object* v_lintDriverArgs_2747_; lean_object* v_version_2748_; lean_object* v_versionTags_2749_; lean_object* v_description_2750_; lean_object* v_keywords_2751_; lean_object* v_homepage_2752_; lean_object* v_license_2753_; lean_object* v_licenseFiles_2754_; lean_object* v_readmeFile_2755_; uint8_t v_reservoir_2756_; lean_object* v_enableArtifactCache_x3f_2757_; lean_object* v_restoreAllArtifacts_x3f_2758_; uint8_t v_libPrefixOnWindows_2759_; uint8_t v_allowImportAll_2760_; uint8_t v_fixedToolchain_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2769_; 
v_toWorkspaceConfig_2729_ = lean_ctor_get(v_cfg_2728_, 0);
v_toLeanConfig_2730_ = lean_ctor_get(v_cfg_2728_, 1);
v_bootstrap_2731_ = lean_ctor_get_uint8(v_cfg_2728_, sizeof(void*)*26);
v_extraDepTargets_2732_ = lean_ctor_get(v_cfg_2728_, 2);
v_precompileModules_2733_ = lean_ctor_get_uint8(v_cfg_2728_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2734_ = lean_ctor_get(v_cfg_2728_, 3);
v_srcDir_2735_ = lean_ctor_get(v_cfg_2728_, 4);
v_buildDir_2736_ = lean_ctor_get(v_cfg_2728_, 5);
v_leanLibDir_2737_ = lean_ctor_get(v_cfg_2728_, 6);
v_nativeLibDir_2738_ = lean_ctor_get(v_cfg_2728_, 7);
v_binDir_2739_ = lean_ctor_get(v_cfg_2728_, 8);
v_irDir_2740_ = lean_ctor_get(v_cfg_2728_, 9);
v_releaseRepo_2741_ = lean_ctor_get(v_cfg_2728_, 10);
v_buildArchive_2742_ = lean_ctor_get(v_cfg_2728_, 11);
v_preferReleaseBuild_2743_ = lean_ctor_get_uint8(v_cfg_2728_, sizeof(void*)*26 + 2);
v_testDriver_2744_ = lean_ctor_get(v_cfg_2728_, 12);
v_testDriverArgs_2745_ = lean_ctor_get(v_cfg_2728_, 13);
v_lintDriver_2746_ = lean_ctor_get(v_cfg_2728_, 14);
v_lintDriverArgs_2747_ = lean_ctor_get(v_cfg_2728_, 15);
v_version_2748_ = lean_ctor_get(v_cfg_2728_, 16);
v_versionTags_2749_ = lean_ctor_get(v_cfg_2728_, 17);
v_description_2750_ = lean_ctor_get(v_cfg_2728_, 18);
v_keywords_2751_ = lean_ctor_get(v_cfg_2728_, 19);
v_homepage_2752_ = lean_ctor_get(v_cfg_2728_, 20);
v_license_2753_ = lean_ctor_get(v_cfg_2728_, 21);
v_licenseFiles_2754_ = lean_ctor_get(v_cfg_2728_, 22);
v_readmeFile_2755_ = lean_ctor_get(v_cfg_2728_, 23);
v_reservoir_2756_ = lean_ctor_get_uint8(v_cfg_2728_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2757_ = lean_ctor_get(v_cfg_2728_, 24);
v_restoreAllArtifacts_x3f_2758_ = lean_ctor_get(v_cfg_2728_, 25);
v_libPrefixOnWindows_2759_ = lean_ctor_get_uint8(v_cfg_2728_, sizeof(void*)*26 + 4);
v_allowImportAll_2760_ = lean_ctor_get_uint8(v_cfg_2728_, sizeof(void*)*26 + 5);
v_fixedToolchain_2761_ = lean_ctor_get_uint8(v_cfg_2728_, sizeof(void*)*26 + 6);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_cfg_2728_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2763_ = v_cfg_2728_;
v_isShared_2764_ = v_isSharedCheck_2769_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2758_);
lean_inc(v_enableArtifactCache_x3f_2757_);
lean_inc(v_readmeFile_2755_);
lean_inc(v_licenseFiles_2754_);
lean_inc(v_license_2753_);
lean_inc(v_homepage_2752_);
lean_inc(v_keywords_2751_);
lean_inc(v_description_2750_);
lean_inc(v_versionTags_2749_);
lean_inc(v_version_2748_);
lean_inc(v_lintDriverArgs_2747_);
lean_inc(v_lintDriver_2746_);
lean_inc(v_testDriverArgs_2745_);
lean_inc(v_testDriver_2744_);
lean_inc(v_buildArchive_2742_);
lean_inc(v_releaseRepo_2741_);
lean_inc(v_irDir_2740_);
lean_inc(v_binDir_2739_);
lean_inc(v_nativeLibDir_2738_);
lean_inc(v_leanLibDir_2737_);
lean_inc(v_buildDir_2736_);
lean_inc(v_srcDir_2735_);
lean_inc(v_moreGlobalServerArgs_2734_);
lean_inc(v_extraDepTargets_2732_);
lean_inc(v_toLeanConfig_2730_);
lean_inc(v_toWorkspaceConfig_2729_);
lean_dec(v_cfg_2728_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2769_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2765_ = lean_apply_1(v_f_2727_, v_licenseFiles_2754_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 22, v___x_2765_);
v___x_2767_ = v___x_2763_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_toWorkspaceConfig_2729_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_toLeanConfig_2730_);
lean_ctor_set(v_reuseFailAlloc_2768_, 2, v_extraDepTargets_2732_);
lean_ctor_set(v_reuseFailAlloc_2768_, 3, v_moreGlobalServerArgs_2734_);
lean_ctor_set(v_reuseFailAlloc_2768_, 4, v_srcDir_2735_);
lean_ctor_set(v_reuseFailAlloc_2768_, 5, v_buildDir_2736_);
lean_ctor_set(v_reuseFailAlloc_2768_, 6, v_leanLibDir_2737_);
lean_ctor_set(v_reuseFailAlloc_2768_, 7, v_nativeLibDir_2738_);
lean_ctor_set(v_reuseFailAlloc_2768_, 8, v_binDir_2739_);
lean_ctor_set(v_reuseFailAlloc_2768_, 9, v_irDir_2740_);
lean_ctor_set(v_reuseFailAlloc_2768_, 10, v_releaseRepo_2741_);
lean_ctor_set(v_reuseFailAlloc_2768_, 11, v_buildArchive_2742_);
lean_ctor_set(v_reuseFailAlloc_2768_, 12, v_testDriver_2744_);
lean_ctor_set(v_reuseFailAlloc_2768_, 13, v_testDriverArgs_2745_);
lean_ctor_set(v_reuseFailAlloc_2768_, 14, v_lintDriver_2746_);
lean_ctor_set(v_reuseFailAlloc_2768_, 15, v_lintDriverArgs_2747_);
lean_ctor_set(v_reuseFailAlloc_2768_, 16, v_version_2748_);
lean_ctor_set(v_reuseFailAlloc_2768_, 17, v_versionTags_2749_);
lean_ctor_set(v_reuseFailAlloc_2768_, 18, v_description_2750_);
lean_ctor_set(v_reuseFailAlloc_2768_, 19, v_keywords_2751_);
lean_ctor_set(v_reuseFailAlloc_2768_, 20, v_homepage_2752_);
lean_ctor_set(v_reuseFailAlloc_2768_, 21, v_license_2753_);
lean_ctor_set(v_reuseFailAlloc_2768_, 22, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2768_, 23, v_readmeFile_2755_);
lean_ctor_set(v_reuseFailAlloc_2768_, 24, v_enableArtifactCache_x3f_2757_);
lean_ctor_set(v_reuseFailAlloc_2768_, 25, v_restoreAllArtifacts_x3f_2758_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, sizeof(void*)*26, v_bootstrap_2731_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, sizeof(void*)*26 + 1, v_precompileModules_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2743_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, sizeof(void*)*26 + 3, v_reservoir_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2759_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, sizeof(void*)*26 + 5, v_allowImportAll_2760_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, sizeof(void*)*26 + 6, v_fixedToolchain_2761_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3(lean_object* v_x_2770_){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = lean_unsigned_to_nat(1u);
v___x_2772_ = lean_mk_empty_array_with_capacity(v___x_2771_);
lean_dec_ref(v___x_2772_);
v___x_2773_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__7));
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___boxed(lean_object* v_x_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lake_PackageConfig_licenseFiles___proj___lam__3(v_x_2774_);
lean_dec_ref(v_x_2774_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object* v_p_2785_, lean_object* v_n_2786_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___closed__4));
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object* v_p_2788_, lean_object* v_n_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2788_, v_n_2789_);
lean_dec(v_n_2789_);
lean_dec(v_p_2788_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object* v_p_2791_, lean_object* v_n_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2791_, v_n_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object* v_p_2794_, lean_object* v_n_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lake_PackageConfig_licenseFiles_instConfigField(v_p_2794_, v_n_2795_);
lean_dec(v_n_2795_);
lean_dec(v_p_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0(lean_object* v_cfg_2797_){
_start:
{
lean_object* v_readmeFile_2798_; 
v_readmeFile_2798_ = lean_ctor_get(v_cfg_2797_, 23);
lean_inc_ref(v_readmeFile_2798_);
return v_readmeFile_2798_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0___boxed(lean_object* v_cfg_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lake_PackageConfig_readmeFile___proj___lam__0(v_cfg_2799_);
lean_dec_ref(v_cfg_2799_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__1(lean_object* v_val_2801_, lean_object* v_cfg_2802_){
_start:
{
lean_object* v_toWorkspaceConfig_2803_; lean_object* v_toLeanConfig_2804_; uint8_t v_bootstrap_2805_; lean_object* v_extraDepTargets_2806_; uint8_t v_precompileModules_2807_; lean_object* v_moreGlobalServerArgs_2808_; lean_object* v_srcDir_2809_; lean_object* v_buildDir_2810_; lean_object* v_leanLibDir_2811_; lean_object* v_nativeLibDir_2812_; lean_object* v_binDir_2813_; lean_object* v_irDir_2814_; lean_object* v_releaseRepo_2815_; lean_object* v_buildArchive_2816_; uint8_t v_preferReleaseBuild_2817_; lean_object* v_testDriver_2818_; lean_object* v_testDriverArgs_2819_; lean_object* v_lintDriver_2820_; lean_object* v_lintDriverArgs_2821_; lean_object* v_version_2822_; lean_object* v_versionTags_2823_; lean_object* v_description_2824_; lean_object* v_keywords_2825_; lean_object* v_homepage_2826_; lean_object* v_license_2827_; lean_object* v_licenseFiles_2828_; uint8_t v_reservoir_2829_; lean_object* v_enableArtifactCache_x3f_2830_; lean_object* v_restoreAllArtifacts_x3f_2831_; uint8_t v_libPrefixOnWindows_2832_; uint8_t v_allowImportAll_2833_; uint8_t v_fixedToolchain_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
v_toWorkspaceConfig_2803_ = lean_ctor_get(v_cfg_2802_, 0);
v_toLeanConfig_2804_ = lean_ctor_get(v_cfg_2802_, 1);
v_bootstrap_2805_ = lean_ctor_get_uint8(v_cfg_2802_, sizeof(void*)*26);
v_extraDepTargets_2806_ = lean_ctor_get(v_cfg_2802_, 2);
v_precompileModules_2807_ = lean_ctor_get_uint8(v_cfg_2802_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2808_ = lean_ctor_get(v_cfg_2802_, 3);
v_srcDir_2809_ = lean_ctor_get(v_cfg_2802_, 4);
v_buildDir_2810_ = lean_ctor_get(v_cfg_2802_, 5);
v_leanLibDir_2811_ = lean_ctor_get(v_cfg_2802_, 6);
v_nativeLibDir_2812_ = lean_ctor_get(v_cfg_2802_, 7);
v_binDir_2813_ = lean_ctor_get(v_cfg_2802_, 8);
v_irDir_2814_ = lean_ctor_get(v_cfg_2802_, 9);
v_releaseRepo_2815_ = lean_ctor_get(v_cfg_2802_, 10);
v_buildArchive_2816_ = lean_ctor_get(v_cfg_2802_, 11);
v_preferReleaseBuild_2817_ = lean_ctor_get_uint8(v_cfg_2802_, sizeof(void*)*26 + 2);
v_testDriver_2818_ = lean_ctor_get(v_cfg_2802_, 12);
v_testDriverArgs_2819_ = lean_ctor_get(v_cfg_2802_, 13);
v_lintDriver_2820_ = lean_ctor_get(v_cfg_2802_, 14);
v_lintDriverArgs_2821_ = lean_ctor_get(v_cfg_2802_, 15);
v_version_2822_ = lean_ctor_get(v_cfg_2802_, 16);
v_versionTags_2823_ = lean_ctor_get(v_cfg_2802_, 17);
v_description_2824_ = lean_ctor_get(v_cfg_2802_, 18);
v_keywords_2825_ = lean_ctor_get(v_cfg_2802_, 19);
v_homepage_2826_ = lean_ctor_get(v_cfg_2802_, 20);
v_license_2827_ = lean_ctor_get(v_cfg_2802_, 21);
v_licenseFiles_2828_ = lean_ctor_get(v_cfg_2802_, 22);
v_reservoir_2829_ = lean_ctor_get_uint8(v_cfg_2802_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2830_ = lean_ctor_get(v_cfg_2802_, 24);
v_restoreAllArtifacts_x3f_2831_ = lean_ctor_get(v_cfg_2802_, 25);
v_libPrefixOnWindows_2832_ = lean_ctor_get_uint8(v_cfg_2802_, sizeof(void*)*26 + 4);
v_allowImportAll_2833_ = lean_ctor_get_uint8(v_cfg_2802_, sizeof(void*)*26 + 5);
v_fixedToolchain_2834_ = lean_ctor_get_uint8(v_cfg_2802_, sizeof(void*)*26 + 6);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_cfg_2802_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v_cfg_2802_, 23);
lean_dec(v_unused_2842_);
v___x_2836_ = v_cfg_2802_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2831_);
lean_inc(v_enableArtifactCache_x3f_2830_);
lean_inc(v_licenseFiles_2828_);
lean_inc(v_license_2827_);
lean_inc(v_homepage_2826_);
lean_inc(v_keywords_2825_);
lean_inc(v_description_2824_);
lean_inc(v_versionTags_2823_);
lean_inc(v_version_2822_);
lean_inc(v_lintDriverArgs_2821_);
lean_inc(v_lintDriver_2820_);
lean_inc(v_testDriverArgs_2819_);
lean_inc(v_testDriver_2818_);
lean_inc(v_buildArchive_2816_);
lean_inc(v_releaseRepo_2815_);
lean_inc(v_irDir_2814_);
lean_inc(v_binDir_2813_);
lean_inc(v_nativeLibDir_2812_);
lean_inc(v_leanLibDir_2811_);
lean_inc(v_buildDir_2810_);
lean_inc(v_srcDir_2809_);
lean_inc(v_moreGlobalServerArgs_2808_);
lean_inc(v_extraDepTargets_2806_);
lean_inc(v_toLeanConfig_2804_);
lean_inc(v_toWorkspaceConfig_2803_);
lean_dec(v_cfg_2802_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 23, v_val_2801_);
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_toWorkspaceConfig_2803_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_toLeanConfig_2804_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_extraDepTargets_2806_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_moreGlobalServerArgs_2808_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_srcDir_2809_);
lean_ctor_set(v_reuseFailAlloc_2840_, 5, v_buildDir_2810_);
lean_ctor_set(v_reuseFailAlloc_2840_, 6, v_leanLibDir_2811_);
lean_ctor_set(v_reuseFailAlloc_2840_, 7, v_nativeLibDir_2812_);
lean_ctor_set(v_reuseFailAlloc_2840_, 8, v_binDir_2813_);
lean_ctor_set(v_reuseFailAlloc_2840_, 9, v_irDir_2814_);
lean_ctor_set(v_reuseFailAlloc_2840_, 10, v_releaseRepo_2815_);
lean_ctor_set(v_reuseFailAlloc_2840_, 11, v_buildArchive_2816_);
lean_ctor_set(v_reuseFailAlloc_2840_, 12, v_testDriver_2818_);
lean_ctor_set(v_reuseFailAlloc_2840_, 13, v_testDriverArgs_2819_);
lean_ctor_set(v_reuseFailAlloc_2840_, 14, v_lintDriver_2820_);
lean_ctor_set(v_reuseFailAlloc_2840_, 15, v_lintDriverArgs_2821_);
lean_ctor_set(v_reuseFailAlloc_2840_, 16, v_version_2822_);
lean_ctor_set(v_reuseFailAlloc_2840_, 17, v_versionTags_2823_);
lean_ctor_set(v_reuseFailAlloc_2840_, 18, v_description_2824_);
lean_ctor_set(v_reuseFailAlloc_2840_, 19, v_keywords_2825_);
lean_ctor_set(v_reuseFailAlloc_2840_, 20, v_homepage_2826_);
lean_ctor_set(v_reuseFailAlloc_2840_, 21, v_license_2827_);
lean_ctor_set(v_reuseFailAlloc_2840_, 22, v_licenseFiles_2828_);
lean_ctor_set(v_reuseFailAlloc_2840_, 23, v_val_2801_);
lean_ctor_set(v_reuseFailAlloc_2840_, 24, v_enableArtifactCache_x3f_2830_);
lean_ctor_set(v_reuseFailAlloc_2840_, 25, v_restoreAllArtifacts_x3f_2831_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*26, v_bootstrap_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*26 + 1, v_precompileModules_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2817_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*26 + 3, v_reservoir_2829_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2832_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*26 + 5, v_allowImportAll_2833_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*26 + 6, v_fixedToolchain_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__2(lean_object* v_f_2843_, lean_object* v_cfg_2844_){
_start:
{
lean_object* v_toWorkspaceConfig_2845_; lean_object* v_toLeanConfig_2846_; uint8_t v_bootstrap_2847_; lean_object* v_extraDepTargets_2848_; uint8_t v_precompileModules_2849_; lean_object* v_moreGlobalServerArgs_2850_; lean_object* v_srcDir_2851_; lean_object* v_buildDir_2852_; lean_object* v_leanLibDir_2853_; lean_object* v_nativeLibDir_2854_; lean_object* v_binDir_2855_; lean_object* v_irDir_2856_; lean_object* v_releaseRepo_2857_; lean_object* v_buildArchive_2858_; uint8_t v_preferReleaseBuild_2859_; lean_object* v_testDriver_2860_; lean_object* v_testDriverArgs_2861_; lean_object* v_lintDriver_2862_; lean_object* v_lintDriverArgs_2863_; lean_object* v_version_2864_; lean_object* v_versionTags_2865_; lean_object* v_description_2866_; lean_object* v_keywords_2867_; lean_object* v_homepage_2868_; lean_object* v_license_2869_; lean_object* v_licenseFiles_2870_; lean_object* v_readmeFile_2871_; uint8_t v_reservoir_2872_; lean_object* v_enableArtifactCache_x3f_2873_; lean_object* v_restoreAllArtifacts_x3f_2874_; uint8_t v_libPrefixOnWindows_2875_; uint8_t v_allowImportAll_2876_; uint8_t v_fixedToolchain_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2885_; 
v_toWorkspaceConfig_2845_ = lean_ctor_get(v_cfg_2844_, 0);
v_toLeanConfig_2846_ = lean_ctor_get(v_cfg_2844_, 1);
v_bootstrap_2847_ = lean_ctor_get_uint8(v_cfg_2844_, sizeof(void*)*26);
v_extraDepTargets_2848_ = lean_ctor_get(v_cfg_2844_, 2);
v_precompileModules_2849_ = lean_ctor_get_uint8(v_cfg_2844_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2850_ = lean_ctor_get(v_cfg_2844_, 3);
v_srcDir_2851_ = lean_ctor_get(v_cfg_2844_, 4);
v_buildDir_2852_ = lean_ctor_get(v_cfg_2844_, 5);
v_leanLibDir_2853_ = lean_ctor_get(v_cfg_2844_, 6);
v_nativeLibDir_2854_ = lean_ctor_get(v_cfg_2844_, 7);
v_binDir_2855_ = lean_ctor_get(v_cfg_2844_, 8);
v_irDir_2856_ = lean_ctor_get(v_cfg_2844_, 9);
v_releaseRepo_2857_ = lean_ctor_get(v_cfg_2844_, 10);
v_buildArchive_2858_ = lean_ctor_get(v_cfg_2844_, 11);
v_preferReleaseBuild_2859_ = lean_ctor_get_uint8(v_cfg_2844_, sizeof(void*)*26 + 2);
v_testDriver_2860_ = lean_ctor_get(v_cfg_2844_, 12);
v_testDriverArgs_2861_ = lean_ctor_get(v_cfg_2844_, 13);
v_lintDriver_2862_ = lean_ctor_get(v_cfg_2844_, 14);
v_lintDriverArgs_2863_ = lean_ctor_get(v_cfg_2844_, 15);
v_version_2864_ = lean_ctor_get(v_cfg_2844_, 16);
v_versionTags_2865_ = lean_ctor_get(v_cfg_2844_, 17);
v_description_2866_ = lean_ctor_get(v_cfg_2844_, 18);
v_keywords_2867_ = lean_ctor_get(v_cfg_2844_, 19);
v_homepage_2868_ = lean_ctor_get(v_cfg_2844_, 20);
v_license_2869_ = lean_ctor_get(v_cfg_2844_, 21);
v_licenseFiles_2870_ = lean_ctor_get(v_cfg_2844_, 22);
v_readmeFile_2871_ = lean_ctor_get(v_cfg_2844_, 23);
v_reservoir_2872_ = lean_ctor_get_uint8(v_cfg_2844_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2873_ = lean_ctor_get(v_cfg_2844_, 24);
v_restoreAllArtifacts_x3f_2874_ = lean_ctor_get(v_cfg_2844_, 25);
v_libPrefixOnWindows_2875_ = lean_ctor_get_uint8(v_cfg_2844_, sizeof(void*)*26 + 4);
v_allowImportAll_2876_ = lean_ctor_get_uint8(v_cfg_2844_, sizeof(void*)*26 + 5);
v_fixedToolchain_2877_ = lean_ctor_get_uint8(v_cfg_2844_, sizeof(void*)*26 + 6);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_cfg_2844_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2879_ = v_cfg_2844_;
v_isShared_2880_ = v_isSharedCheck_2885_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2874_);
lean_inc(v_enableArtifactCache_x3f_2873_);
lean_inc(v_readmeFile_2871_);
lean_inc(v_licenseFiles_2870_);
lean_inc(v_license_2869_);
lean_inc(v_homepage_2868_);
lean_inc(v_keywords_2867_);
lean_inc(v_description_2866_);
lean_inc(v_versionTags_2865_);
lean_inc(v_version_2864_);
lean_inc(v_lintDriverArgs_2863_);
lean_inc(v_lintDriver_2862_);
lean_inc(v_testDriverArgs_2861_);
lean_inc(v_testDriver_2860_);
lean_inc(v_buildArchive_2858_);
lean_inc(v_releaseRepo_2857_);
lean_inc(v_irDir_2856_);
lean_inc(v_binDir_2855_);
lean_inc(v_nativeLibDir_2854_);
lean_inc(v_leanLibDir_2853_);
lean_inc(v_buildDir_2852_);
lean_inc(v_srcDir_2851_);
lean_inc(v_moreGlobalServerArgs_2850_);
lean_inc(v_extraDepTargets_2848_);
lean_inc(v_toLeanConfig_2846_);
lean_inc(v_toWorkspaceConfig_2845_);
lean_dec(v_cfg_2844_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2885_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = lean_apply_1(v_f_2843_, v_readmeFile_2871_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 23, v___x_2881_);
v___x_2883_ = v___x_2879_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_toWorkspaceConfig_2845_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_toLeanConfig_2846_);
lean_ctor_set(v_reuseFailAlloc_2884_, 2, v_extraDepTargets_2848_);
lean_ctor_set(v_reuseFailAlloc_2884_, 3, v_moreGlobalServerArgs_2850_);
lean_ctor_set(v_reuseFailAlloc_2884_, 4, v_srcDir_2851_);
lean_ctor_set(v_reuseFailAlloc_2884_, 5, v_buildDir_2852_);
lean_ctor_set(v_reuseFailAlloc_2884_, 6, v_leanLibDir_2853_);
lean_ctor_set(v_reuseFailAlloc_2884_, 7, v_nativeLibDir_2854_);
lean_ctor_set(v_reuseFailAlloc_2884_, 8, v_binDir_2855_);
lean_ctor_set(v_reuseFailAlloc_2884_, 9, v_irDir_2856_);
lean_ctor_set(v_reuseFailAlloc_2884_, 10, v_releaseRepo_2857_);
lean_ctor_set(v_reuseFailAlloc_2884_, 11, v_buildArchive_2858_);
lean_ctor_set(v_reuseFailAlloc_2884_, 12, v_testDriver_2860_);
lean_ctor_set(v_reuseFailAlloc_2884_, 13, v_testDriverArgs_2861_);
lean_ctor_set(v_reuseFailAlloc_2884_, 14, v_lintDriver_2862_);
lean_ctor_set(v_reuseFailAlloc_2884_, 15, v_lintDriverArgs_2863_);
lean_ctor_set(v_reuseFailAlloc_2884_, 16, v_version_2864_);
lean_ctor_set(v_reuseFailAlloc_2884_, 17, v_versionTags_2865_);
lean_ctor_set(v_reuseFailAlloc_2884_, 18, v_description_2866_);
lean_ctor_set(v_reuseFailAlloc_2884_, 19, v_keywords_2867_);
lean_ctor_set(v_reuseFailAlloc_2884_, 20, v_homepage_2868_);
lean_ctor_set(v_reuseFailAlloc_2884_, 21, v_license_2869_);
lean_ctor_set(v_reuseFailAlloc_2884_, 22, v_licenseFiles_2870_);
lean_ctor_set(v_reuseFailAlloc_2884_, 23, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2884_, 24, v_enableArtifactCache_x3f_2873_);
lean_ctor_set(v_reuseFailAlloc_2884_, 25, v_restoreAllArtifacts_x3f_2874_);
lean_ctor_set_uint8(v_reuseFailAlloc_2884_, sizeof(void*)*26, v_bootstrap_2847_);
lean_ctor_set_uint8(v_reuseFailAlloc_2884_, sizeof(void*)*26 + 1, v_precompileModules_2849_);
lean_ctor_set_uint8(v_reuseFailAlloc_2884_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2859_);
lean_ctor_set_uint8(v_reuseFailAlloc_2884_, sizeof(void*)*26 + 3, v_reservoir_2872_);
lean_ctor_set_uint8(v_reuseFailAlloc_2884_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2875_);
lean_ctor_set_uint8(v_reuseFailAlloc_2884_, sizeof(void*)*26 + 5, v_allowImportAll_2876_);
lean_ctor_set_uint8(v_reuseFailAlloc_2884_, sizeof(void*)*26 + 6, v_fixedToolchain_2877_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3(lean_object* v_x_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__8));
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3___boxed(lean_object* v_x_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lake_PackageConfig_readmeFile___proj___lam__3(v_x_2888_);
lean_dec_ref(v_x_2888_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object* v_p_2899_, lean_object* v_n_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___closed__4));
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object* v_p_2902_, lean_object* v_n_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lake_PackageConfig_readmeFile___proj(v_p_2902_, v_n_2903_);
lean_dec(v_n_2903_);
lean_dec(v_p_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object* v_p_2905_, lean_object* v_n_2906_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Lake_PackageConfig_readmeFile___proj(v_p_2905_, v_n_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object* v_p_2908_, lean_object* v_n_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lake_PackageConfig_readmeFile_instConfigField(v_p_2908_, v_n_2909_);
lean_dec(v_n_2909_);
lean_dec(v_p_2908_);
return v_res_2910_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__0(lean_object* v_cfg_2911_){
_start:
{
uint8_t v_reservoir_2912_; 
v_reservoir_2912_ = lean_ctor_get_uint8(v_cfg_2911_, sizeof(void*)*26 + 3);
return v_reservoir_2912_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__0___boxed(lean_object* v_cfg_2913_){
_start:
{
uint8_t v_res_2914_; lean_object* v_r_2915_; 
v_res_2914_ = l_Lake_PackageConfig_reservoir___proj___lam__0(v_cfg_2913_);
lean_dec_ref(v_cfg_2913_);
v_r_2915_ = lean_box(v_res_2914_);
return v_r_2915_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1(uint8_t v_val_2916_, lean_object* v_cfg_2917_){
_start:
{
lean_object* v_toWorkspaceConfig_2918_; lean_object* v_toLeanConfig_2919_; uint8_t v_bootstrap_2920_; lean_object* v_extraDepTargets_2921_; uint8_t v_precompileModules_2922_; lean_object* v_moreGlobalServerArgs_2923_; lean_object* v_srcDir_2924_; lean_object* v_buildDir_2925_; lean_object* v_leanLibDir_2926_; lean_object* v_nativeLibDir_2927_; lean_object* v_binDir_2928_; lean_object* v_irDir_2929_; lean_object* v_releaseRepo_2930_; lean_object* v_buildArchive_2931_; uint8_t v_preferReleaseBuild_2932_; lean_object* v_testDriver_2933_; lean_object* v_testDriverArgs_2934_; lean_object* v_lintDriver_2935_; lean_object* v_lintDriverArgs_2936_; lean_object* v_version_2937_; lean_object* v_versionTags_2938_; lean_object* v_description_2939_; lean_object* v_keywords_2940_; lean_object* v_homepage_2941_; lean_object* v_license_2942_; lean_object* v_licenseFiles_2943_; lean_object* v_readmeFile_2944_; lean_object* v_enableArtifactCache_x3f_2945_; lean_object* v_restoreAllArtifacts_x3f_2946_; uint8_t v_libPrefixOnWindows_2947_; uint8_t v_allowImportAll_2948_; uint8_t v_fixedToolchain_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_toWorkspaceConfig_2918_ = lean_ctor_get(v_cfg_2917_, 0);
v_toLeanConfig_2919_ = lean_ctor_get(v_cfg_2917_, 1);
v_bootstrap_2920_ = lean_ctor_get_uint8(v_cfg_2917_, sizeof(void*)*26);
v_extraDepTargets_2921_ = lean_ctor_get(v_cfg_2917_, 2);
v_precompileModules_2922_ = lean_ctor_get_uint8(v_cfg_2917_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2923_ = lean_ctor_get(v_cfg_2917_, 3);
v_srcDir_2924_ = lean_ctor_get(v_cfg_2917_, 4);
v_buildDir_2925_ = lean_ctor_get(v_cfg_2917_, 5);
v_leanLibDir_2926_ = lean_ctor_get(v_cfg_2917_, 6);
v_nativeLibDir_2927_ = lean_ctor_get(v_cfg_2917_, 7);
v_binDir_2928_ = lean_ctor_get(v_cfg_2917_, 8);
v_irDir_2929_ = lean_ctor_get(v_cfg_2917_, 9);
v_releaseRepo_2930_ = lean_ctor_get(v_cfg_2917_, 10);
v_buildArchive_2931_ = lean_ctor_get(v_cfg_2917_, 11);
v_preferReleaseBuild_2932_ = lean_ctor_get_uint8(v_cfg_2917_, sizeof(void*)*26 + 2);
v_testDriver_2933_ = lean_ctor_get(v_cfg_2917_, 12);
v_testDriverArgs_2934_ = lean_ctor_get(v_cfg_2917_, 13);
v_lintDriver_2935_ = lean_ctor_get(v_cfg_2917_, 14);
v_lintDriverArgs_2936_ = lean_ctor_get(v_cfg_2917_, 15);
v_version_2937_ = lean_ctor_get(v_cfg_2917_, 16);
v_versionTags_2938_ = lean_ctor_get(v_cfg_2917_, 17);
v_description_2939_ = lean_ctor_get(v_cfg_2917_, 18);
v_keywords_2940_ = lean_ctor_get(v_cfg_2917_, 19);
v_homepage_2941_ = lean_ctor_get(v_cfg_2917_, 20);
v_license_2942_ = lean_ctor_get(v_cfg_2917_, 21);
v_licenseFiles_2943_ = lean_ctor_get(v_cfg_2917_, 22);
v_readmeFile_2944_ = lean_ctor_get(v_cfg_2917_, 23);
v_enableArtifactCache_x3f_2945_ = lean_ctor_get(v_cfg_2917_, 24);
v_restoreAllArtifacts_x3f_2946_ = lean_ctor_get(v_cfg_2917_, 25);
v_libPrefixOnWindows_2947_ = lean_ctor_get_uint8(v_cfg_2917_, sizeof(void*)*26 + 4);
v_allowImportAll_2948_ = lean_ctor_get_uint8(v_cfg_2917_, sizeof(void*)*26 + 5);
v_fixedToolchain_2949_ = lean_ctor_get_uint8(v_cfg_2917_, sizeof(void*)*26 + 6);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_cfg_2917_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v_cfg_2917_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2946_);
lean_inc(v_enableArtifactCache_x3f_2945_);
lean_inc(v_readmeFile_2944_);
lean_inc(v_licenseFiles_2943_);
lean_inc(v_license_2942_);
lean_inc(v_homepage_2941_);
lean_inc(v_keywords_2940_);
lean_inc(v_description_2939_);
lean_inc(v_versionTags_2938_);
lean_inc(v_version_2937_);
lean_inc(v_lintDriverArgs_2936_);
lean_inc(v_lintDriver_2935_);
lean_inc(v_testDriverArgs_2934_);
lean_inc(v_testDriver_2933_);
lean_inc(v_buildArchive_2931_);
lean_inc(v_releaseRepo_2930_);
lean_inc(v_irDir_2929_);
lean_inc(v_binDir_2928_);
lean_inc(v_nativeLibDir_2927_);
lean_inc(v_leanLibDir_2926_);
lean_inc(v_buildDir_2925_);
lean_inc(v_srcDir_2924_);
lean_inc(v_moreGlobalServerArgs_2923_);
lean_inc(v_extraDepTargets_2921_);
lean_inc(v_toLeanConfig_2919_);
lean_inc(v_toWorkspaceConfig_2918_);
lean_dec(v_cfg_2917_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_toWorkspaceConfig_2918_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_toLeanConfig_2919_);
lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_extraDepTargets_2921_);
lean_ctor_set(v_reuseFailAlloc_2955_, 3, v_moreGlobalServerArgs_2923_);
lean_ctor_set(v_reuseFailAlloc_2955_, 4, v_srcDir_2924_);
lean_ctor_set(v_reuseFailAlloc_2955_, 5, v_buildDir_2925_);
lean_ctor_set(v_reuseFailAlloc_2955_, 6, v_leanLibDir_2926_);
lean_ctor_set(v_reuseFailAlloc_2955_, 7, v_nativeLibDir_2927_);
lean_ctor_set(v_reuseFailAlloc_2955_, 8, v_binDir_2928_);
lean_ctor_set(v_reuseFailAlloc_2955_, 9, v_irDir_2929_);
lean_ctor_set(v_reuseFailAlloc_2955_, 10, v_releaseRepo_2930_);
lean_ctor_set(v_reuseFailAlloc_2955_, 11, v_buildArchive_2931_);
lean_ctor_set(v_reuseFailAlloc_2955_, 12, v_testDriver_2933_);
lean_ctor_set(v_reuseFailAlloc_2955_, 13, v_testDriverArgs_2934_);
lean_ctor_set(v_reuseFailAlloc_2955_, 14, v_lintDriver_2935_);
lean_ctor_set(v_reuseFailAlloc_2955_, 15, v_lintDriverArgs_2936_);
lean_ctor_set(v_reuseFailAlloc_2955_, 16, v_version_2937_);
lean_ctor_set(v_reuseFailAlloc_2955_, 17, v_versionTags_2938_);
lean_ctor_set(v_reuseFailAlloc_2955_, 18, v_description_2939_);
lean_ctor_set(v_reuseFailAlloc_2955_, 19, v_keywords_2940_);
lean_ctor_set(v_reuseFailAlloc_2955_, 20, v_homepage_2941_);
lean_ctor_set(v_reuseFailAlloc_2955_, 21, v_license_2942_);
lean_ctor_set(v_reuseFailAlloc_2955_, 22, v_licenseFiles_2943_);
lean_ctor_set(v_reuseFailAlloc_2955_, 23, v_readmeFile_2944_);
lean_ctor_set(v_reuseFailAlloc_2955_, 24, v_enableArtifactCache_x3f_2945_);
lean_ctor_set(v_reuseFailAlloc_2955_, 25, v_restoreAllArtifacts_x3f_2946_);
lean_ctor_set_uint8(v_reuseFailAlloc_2955_, sizeof(void*)*26, v_bootstrap_2920_);
lean_ctor_set_uint8(v_reuseFailAlloc_2955_, sizeof(void*)*26 + 1, v_precompileModules_2922_);
lean_ctor_set_uint8(v_reuseFailAlloc_2955_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2955_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2947_);
lean_ctor_set_uint8(v_reuseFailAlloc_2955_, sizeof(void*)*26 + 5, v_allowImportAll_2948_);
lean_ctor_set_uint8(v_reuseFailAlloc_2955_, sizeof(void*)*26 + 6, v_fixedToolchain_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_ctor_set_uint8(v___x_2954_, sizeof(void*)*26 + 3, v_val_2916_);
return v___x_2954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1___boxed(lean_object* v_val_2957_, lean_object* v_cfg_2958_){
_start:
{
uint8_t v_val_134__boxed_2959_; lean_object* v_res_2960_; 
v_val_134__boxed_2959_ = lean_unbox(v_val_2957_);
v_res_2960_ = l_Lake_PackageConfig_reservoir___proj___lam__1(v_val_134__boxed_2959_, v_cfg_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__2(lean_object* v_f_2961_, lean_object* v_cfg_2962_){
_start:
{
lean_object* v_toWorkspaceConfig_2963_; lean_object* v_toLeanConfig_2964_; uint8_t v_bootstrap_2965_; lean_object* v_extraDepTargets_2966_; uint8_t v_precompileModules_2967_; lean_object* v_moreGlobalServerArgs_2968_; lean_object* v_srcDir_2969_; lean_object* v_buildDir_2970_; lean_object* v_leanLibDir_2971_; lean_object* v_nativeLibDir_2972_; lean_object* v_binDir_2973_; lean_object* v_irDir_2974_; lean_object* v_releaseRepo_2975_; lean_object* v_buildArchive_2976_; uint8_t v_preferReleaseBuild_2977_; lean_object* v_testDriver_2978_; lean_object* v_testDriverArgs_2979_; lean_object* v_lintDriver_2980_; lean_object* v_lintDriverArgs_2981_; lean_object* v_version_2982_; lean_object* v_versionTags_2983_; lean_object* v_description_2984_; lean_object* v_keywords_2985_; lean_object* v_homepage_2986_; lean_object* v_license_2987_; lean_object* v_licenseFiles_2988_; lean_object* v_readmeFile_2989_; uint8_t v_reservoir_2990_; lean_object* v_enableArtifactCache_x3f_2991_; lean_object* v_restoreAllArtifacts_x3f_2992_; uint8_t v_libPrefixOnWindows_2993_; uint8_t v_allowImportAll_2994_; uint8_t v_fixedToolchain_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3005_; 
v_toWorkspaceConfig_2963_ = lean_ctor_get(v_cfg_2962_, 0);
v_toLeanConfig_2964_ = lean_ctor_get(v_cfg_2962_, 1);
v_bootstrap_2965_ = lean_ctor_get_uint8(v_cfg_2962_, sizeof(void*)*26);
v_extraDepTargets_2966_ = lean_ctor_get(v_cfg_2962_, 2);
v_precompileModules_2967_ = lean_ctor_get_uint8(v_cfg_2962_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2968_ = lean_ctor_get(v_cfg_2962_, 3);
v_srcDir_2969_ = lean_ctor_get(v_cfg_2962_, 4);
v_buildDir_2970_ = lean_ctor_get(v_cfg_2962_, 5);
v_leanLibDir_2971_ = lean_ctor_get(v_cfg_2962_, 6);
v_nativeLibDir_2972_ = lean_ctor_get(v_cfg_2962_, 7);
v_binDir_2973_ = lean_ctor_get(v_cfg_2962_, 8);
v_irDir_2974_ = lean_ctor_get(v_cfg_2962_, 9);
v_releaseRepo_2975_ = lean_ctor_get(v_cfg_2962_, 10);
v_buildArchive_2976_ = lean_ctor_get(v_cfg_2962_, 11);
v_preferReleaseBuild_2977_ = lean_ctor_get_uint8(v_cfg_2962_, sizeof(void*)*26 + 2);
v_testDriver_2978_ = lean_ctor_get(v_cfg_2962_, 12);
v_testDriverArgs_2979_ = lean_ctor_get(v_cfg_2962_, 13);
v_lintDriver_2980_ = lean_ctor_get(v_cfg_2962_, 14);
v_lintDriverArgs_2981_ = lean_ctor_get(v_cfg_2962_, 15);
v_version_2982_ = lean_ctor_get(v_cfg_2962_, 16);
v_versionTags_2983_ = lean_ctor_get(v_cfg_2962_, 17);
v_description_2984_ = lean_ctor_get(v_cfg_2962_, 18);
v_keywords_2985_ = lean_ctor_get(v_cfg_2962_, 19);
v_homepage_2986_ = lean_ctor_get(v_cfg_2962_, 20);
v_license_2987_ = lean_ctor_get(v_cfg_2962_, 21);
v_licenseFiles_2988_ = lean_ctor_get(v_cfg_2962_, 22);
v_readmeFile_2989_ = lean_ctor_get(v_cfg_2962_, 23);
v_reservoir_2990_ = lean_ctor_get_uint8(v_cfg_2962_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2991_ = lean_ctor_get(v_cfg_2962_, 24);
v_restoreAllArtifacts_x3f_2992_ = lean_ctor_get(v_cfg_2962_, 25);
v_libPrefixOnWindows_2993_ = lean_ctor_get_uint8(v_cfg_2962_, sizeof(void*)*26 + 4);
v_allowImportAll_2994_ = lean_ctor_get_uint8(v_cfg_2962_, sizeof(void*)*26 + 5);
v_fixedToolchain_2995_ = lean_ctor_get_uint8(v_cfg_2962_, sizeof(void*)*26 + 6);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_cfg_2962_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2997_ = v_cfg_2962_;
v_isShared_2998_ = v_isSharedCheck_3005_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2992_);
lean_inc(v_enableArtifactCache_x3f_2991_);
lean_inc(v_readmeFile_2989_);
lean_inc(v_licenseFiles_2988_);
lean_inc(v_license_2987_);
lean_inc(v_homepage_2986_);
lean_inc(v_keywords_2985_);
lean_inc(v_description_2984_);
lean_inc(v_versionTags_2983_);
lean_inc(v_version_2982_);
lean_inc(v_lintDriverArgs_2981_);
lean_inc(v_lintDriver_2980_);
lean_inc(v_testDriverArgs_2979_);
lean_inc(v_testDriver_2978_);
lean_inc(v_buildArchive_2976_);
lean_inc(v_releaseRepo_2975_);
lean_inc(v_irDir_2974_);
lean_inc(v_binDir_2973_);
lean_inc(v_nativeLibDir_2972_);
lean_inc(v_leanLibDir_2971_);
lean_inc(v_buildDir_2970_);
lean_inc(v_srcDir_2969_);
lean_inc(v_moreGlobalServerArgs_2968_);
lean_inc(v_extraDepTargets_2966_);
lean_inc(v_toLeanConfig_2964_);
lean_inc(v_toWorkspaceConfig_2963_);
lean_dec(v_cfg_2962_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3005_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3002_; 
v___x_2999_ = lean_box(v_reservoir_2990_);
v___x_3000_ = lean_apply_1(v_f_2961_, v___x_2999_);
if (v_isShared_2998_ == 0)
{
v___x_3002_ = v___x_2997_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_toWorkspaceConfig_2963_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_toLeanConfig_2964_);
lean_ctor_set(v_reuseFailAlloc_3004_, 2, v_extraDepTargets_2966_);
lean_ctor_set(v_reuseFailAlloc_3004_, 3, v_moreGlobalServerArgs_2968_);
lean_ctor_set(v_reuseFailAlloc_3004_, 4, v_srcDir_2969_);
lean_ctor_set(v_reuseFailAlloc_3004_, 5, v_buildDir_2970_);
lean_ctor_set(v_reuseFailAlloc_3004_, 6, v_leanLibDir_2971_);
lean_ctor_set(v_reuseFailAlloc_3004_, 7, v_nativeLibDir_2972_);
lean_ctor_set(v_reuseFailAlloc_3004_, 8, v_binDir_2973_);
lean_ctor_set(v_reuseFailAlloc_3004_, 9, v_irDir_2974_);
lean_ctor_set(v_reuseFailAlloc_3004_, 10, v_releaseRepo_2975_);
lean_ctor_set(v_reuseFailAlloc_3004_, 11, v_buildArchive_2976_);
lean_ctor_set(v_reuseFailAlloc_3004_, 12, v_testDriver_2978_);
lean_ctor_set(v_reuseFailAlloc_3004_, 13, v_testDriverArgs_2979_);
lean_ctor_set(v_reuseFailAlloc_3004_, 14, v_lintDriver_2980_);
lean_ctor_set(v_reuseFailAlloc_3004_, 15, v_lintDriverArgs_2981_);
lean_ctor_set(v_reuseFailAlloc_3004_, 16, v_version_2982_);
lean_ctor_set(v_reuseFailAlloc_3004_, 17, v_versionTags_2983_);
lean_ctor_set(v_reuseFailAlloc_3004_, 18, v_description_2984_);
lean_ctor_set(v_reuseFailAlloc_3004_, 19, v_keywords_2985_);
lean_ctor_set(v_reuseFailAlloc_3004_, 20, v_homepage_2986_);
lean_ctor_set(v_reuseFailAlloc_3004_, 21, v_license_2987_);
lean_ctor_set(v_reuseFailAlloc_3004_, 22, v_licenseFiles_2988_);
lean_ctor_set(v_reuseFailAlloc_3004_, 23, v_readmeFile_2989_);
lean_ctor_set(v_reuseFailAlloc_3004_, 24, v_enableArtifactCache_x3f_2991_);
lean_ctor_set(v_reuseFailAlloc_3004_, 25, v_restoreAllArtifacts_x3f_2992_);
lean_ctor_set_uint8(v_reuseFailAlloc_3004_, sizeof(void*)*26, v_bootstrap_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_3004_, sizeof(void*)*26 + 1, v_precompileModules_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_3004_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2977_);
v___x_3002_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
uint8_t v___x_3003_; 
v___x_3003_ = lean_unbox(v___x_3000_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*26 + 3, v___x_3003_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2993_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*26 + 5, v_allowImportAll_2994_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*26 + 6, v_fixedToolchain_2995_);
return v___x_3002_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__3(lean_object* v_x_3006_){
_start:
{
uint8_t v___x_3007_; 
v___x_3007_ = 1;
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__3___boxed(lean_object* v_x_3008_){
_start:
{
uint8_t v_res_3009_; lean_object* v_r_3010_; 
v_res_3009_ = l_Lake_PackageConfig_reservoir___proj___lam__3(v_x_3008_);
lean_dec_ref(v_x_3008_);
v_r_3010_ = lean_box(v_res_3009_);
return v_r_3010_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object* v_p_3020_, lean_object* v_n_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = ((lean_object*)(l_Lake_PackageConfig_reservoir___proj___closed__4));
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object* v_p_3023_, lean_object* v_n_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lake_PackageConfig_reservoir___proj(v_p_3023_, v_n_3024_);
lean_dec(v_n_3024_);
lean_dec(v_p_3023_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object* v_p_3026_, lean_object* v_n_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Lake_PackageConfig_reservoir___proj(v_p_3026_, v_n_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object* v_p_3029_, lean_object* v_n_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lake_PackageConfig_reservoir_instConfigField(v_p_3029_, v_n_3030_);
lean_dec(v_n_3030_);
lean_dec(v_p_3029_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(lean_object* v_cfg_3032_){
_start:
{
lean_object* v_enableArtifactCache_x3f_3033_; 
v_enableArtifactCache_x3f_3033_ = lean_ctor_get(v_cfg_3032_, 24);
lean_inc(v_enableArtifactCache_x3f_3033_);
return v_enableArtifactCache_x3f_3033_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0___boxed(lean_object* v_cfg_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(v_cfg_3034_);
lean_dec_ref(v_cfg_3034_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__1(lean_object* v_val_3036_, lean_object* v_cfg_3037_){
_start:
{
lean_object* v_toWorkspaceConfig_3038_; lean_object* v_toLeanConfig_3039_; uint8_t v_bootstrap_3040_; lean_object* v_extraDepTargets_3041_; uint8_t v_precompileModules_3042_; lean_object* v_moreGlobalServerArgs_3043_; lean_object* v_srcDir_3044_; lean_object* v_buildDir_3045_; lean_object* v_leanLibDir_3046_; lean_object* v_nativeLibDir_3047_; lean_object* v_binDir_3048_; lean_object* v_irDir_3049_; lean_object* v_releaseRepo_3050_; lean_object* v_buildArchive_3051_; uint8_t v_preferReleaseBuild_3052_; lean_object* v_testDriver_3053_; lean_object* v_testDriverArgs_3054_; lean_object* v_lintDriver_3055_; lean_object* v_lintDriverArgs_3056_; lean_object* v_version_3057_; lean_object* v_versionTags_3058_; lean_object* v_description_3059_; lean_object* v_keywords_3060_; lean_object* v_homepage_3061_; lean_object* v_license_3062_; lean_object* v_licenseFiles_3063_; lean_object* v_readmeFile_3064_; uint8_t v_reservoir_3065_; lean_object* v_restoreAllArtifacts_x3f_3066_; uint8_t v_libPrefixOnWindows_3067_; uint8_t v_allowImportAll_3068_; uint8_t v_fixedToolchain_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
v_toWorkspaceConfig_3038_ = lean_ctor_get(v_cfg_3037_, 0);
v_toLeanConfig_3039_ = lean_ctor_get(v_cfg_3037_, 1);
v_bootstrap_3040_ = lean_ctor_get_uint8(v_cfg_3037_, sizeof(void*)*26);
v_extraDepTargets_3041_ = lean_ctor_get(v_cfg_3037_, 2);
v_precompileModules_3042_ = lean_ctor_get_uint8(v_cfg_3037_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3043_ = lean_ctor_get(v_cfg_3037_, 3);
v_srcDir_3044_ = lean_ctor_get(v_cfg_3037_, 4);
v_buildDir_3045_ = lean_ctor_get(v_cfg_3037_, 5);
v_leanLibDir_3046_ = lean_ctor_get(v_cfg_3037_, 6);
v_nativeLibDir_3047_ = lean_ctor_get(v_cfg_3037_, 7);
v_binDir_3048_ = lean_ctor_get(v_cfg_3037_, 8);
v_irDir_3049_ = lean_ctor_get(v_cfg_3037_, 9);
v_releaseRepo_3050_ = lean_ctor_get(v_cfg_3037_, 10);
v_buildArchive_3051_ = lean_ctor_get(v_cfg_3037_, 11);
v_preferReleaseBuild_3052_ = lean_ctor_get_uint8(v_cfg_3037_, sizeof(void*)*26 + 2);
v_testDriver_3053_ = lean_ctor_get(v_cfg_3037_, 12);
v_testDriverArgs_3054_ = lean_ctor_get(v_cfg_3037_, 13);
v_lintDriver_3055_ = lean_ctor_get(v_cfg_3037_, 14);
v_lintDriverArgs_3056_ = lean_ctor_get(v_cfg_3037_, 15);
v_version_3057_ = lean_ctor_get(v_cfg_3037_, 16);
v_versionTags_3058_ = lean_ctor_get(v_cfg_3037_, 17);
v_description_3059_ = lean_ctor_get(v_cfg_3037_, 18);
v_keywords_3060_ = lean_ctor_get(v_cfg_3037_, 19);
v_homepage_3061_ = lean_ctor_get(v_cfg_3037_, 20);
v_license_3062_ = lean_ctor_get(v_cfg_3037_, 21);
v_licenseFiles_3063_ = lean_ctor_get(v_cfg_3037_, 22);
v_readmeFile_3064_ = lean_ctor_get(v_cfg_3037_, 23);
v_reservoir_3065_ = lean_ctor_get_uint8(v_cfg_3037_, sizeof(void*)*26 + 3);
v_restoreAllArtifacts_x3f_3066_ = lean_ctor_get(v_cfg_3037_, 25);
v_libPrefixOnWindows_3067_ = lean_ctor_get_uint8(v_cfg_3037_, sizeof(void*)*26 + 4);
v_allowImportAll_3068_ = lean_ctor_get_uint8(v_cfg_3037_, sizeof(void*)*26 + 5);
v_fixedToolchain_3069_ = lean_ctor_get_uint8(v_cfg_3037_, sizeof(void*)*26 + 6);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_cfg_3037_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v_cfg_3037_, 24);
lean_dec(v_unused_3077_);
v___x_3071_ = v_cfg_3037_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3066_);
lean_inc(v_readmeFile_3064_);
lean_inc(v_licenseFiles_3063_);
lean_inc(v_license_3062_);
lean_inc(v_homepage_3061_);
lean_inc(v_keywords_3060_);
lean_inc(v_description_3059_);
lean_inc(v_versionTags_3058_);
lean_inc(v_version_3057_);
lean_inc(v_lintDriverArgs_3056_);
lean_inc(v_lintDriver_3055_);
lean_inc(v_testDriverArgs_3054_);
lean_inc(v_testDriver_3053_);
lean_inc(v_buildArchive_3051_);
lean_inc(v_releaseRepo_3050_);
lean_inc(v_irDir_3049_);
lean_inc(v_binDir_3048_);
lean_inc(v_nativeLibDir_3047_);
lean_inc(v_leanLibDir_3046_);
lean_inc(v_buildDir_3045_);
lean_inc(v_srcDir_3044_);
lean_inc(v_moreGlobalServerArgs_3043_);
lean_inc(v_extraDepTargets_3041_);
lean_inc(v_toLeanConfig_3039_);
lean_inc(v_toWorkspaceConfig_3038_);
lean_dec(v_cfg_3037_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 24, v_val_3036_);
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_toWorkspaceConfig_3038_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_toLeanConfig_3039_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_extraDepTargets_3041_);
lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_moreGlobalServerArgs_3043_);
lean_ctor_set(v_reuseFailAlloc_3075_, 4, v_srcDir_3044_);
lean_ctor_set(v_reuseFailAlloc_3075_, 5, v_buildDir_3045_);
lean_ctor_set(v_reuseFailAlloc_3075_, 6, v_leanLibDir_3046_);
lean_ctor_set(v_reuseFailAlloc_3075_, 7, v_nativeLibDir_3047_);
lean_ctor_set(v_reuseFailAlloc_3075_, 8, v_binDir_3048_);
lean_ctor_set(v_reuseFailAlloc_3075_, 9, v_irDir_3049_);
lean_ctor_set(v_reuseFailAlloc_3075_, 10, v_releaseRepo_3050_);
lean_ctor_set(v_reuseFailAlloc_3075_, 11, v_buildArchive_3051_);
lean_ctor_set(v_reuseFailAlloc_3075_, 12, v_testDriver_3053_);
lean_ctor_set(v_reuseFailAlloc_3075_, 13, v_testDriverArgs_3054_);
lean_ctor_set(v_reuseFailAlloc_3075_, 14, v_lintDriver_3055_);
lean_ctor_set(v_reuseFailAlloc_3075_, 15, v_lintDriverArgs_3056_);
lean_ctor_set(v_reuseFailAlloc_3075_, 16, v_version_3057_);
lean_ctor_set(v_reuseFailAlloc_3075_, 17, v_versionTags_3058_);
lean_ctor_set(v_reuseFailAlloc_3075_, 18, v_description_3059_);
lean_ctor_set(v_reuseFailAlloc_3075_, 19, v_keywords_3060_);
lean_ctor_set(v_reuseFailAlloc_3075_, 20, v_homepage_3061_);
lean_ctor_set(v_reuseFailAlloc_3075_, 21, v_license_3062_);
lean_ctor_set(v_reuseFailAlloc_3075_, 22, v_licenseFiles_3063_);
lean_ctor_set(v_reuseFailAlloc_3075_, 23, v_readmeFile_3064_);
lean_ctor_set(v_reuseFailAlloc_3075_, 24, v_val_3036_);
lean_ctor_set(v_reuseFailAlloc_3075_, 25, v_restoreAllArtifacts_x3f_3066_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*26, v_bootstrap_3040_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*26 + 1, v_precompileModules_3042_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3052_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*26 + 3, v_reservoir_3065_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3067_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*26 + 5, v_allowImportAll_3068_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*26 + 6, v_fixedToolchain_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__2(lean_object* v_f_3078_, lean_object* v_cfg_3079_){
_start:
{
lean_object* v_toWorkspaceConfig_3080_; lean_object* v_toLeanConfig_3081_; uint8_t v_bootstrap_3082_; lean_object* v_extraDepTargets_3083_; uint8_t v_precompileModules_3084_; lean_object* v_moreGlobalServerArgs_3085_; lean_object* v_srcDir_3086_; lean_object* v_buildDir_3087_; lean_object* v_leanLibDir_3088_; lean_object* v_nativeLibDir_3089_; lean_object* v_binDir_3090_; lean_object* v_irDir_3091_; lean_object* v_releaseRepo_3092_; lean_object* v_buildArchive_3093_; uint8_t v_preferReleaseBuild_3094_; lean_object* v_testDriver_3095_; lean_object* v_testDriverArgs_3096_; lean_object* v_lintDriver_3097_; lean_object* v_lintDriverArgs_3098_; lean_object* v_version_3099_; lean_object* v_versionTags_3100_; lean_object* v_description_3101_; lean_object* v_keywords_3102_; lean_object* v_homepage_3103_; lean_object* v_license_3104_; lean_object* v_licenseFiles_3105_; lean_object* v_readmeFile_3106_; uint8_t v_reservoir_3107_; lean_object* v_enableArtifactCache_x3f_3108_; lean_object* v_restoreAllArtifacts_x3f_3109_; uint8_t v_libPrefixOnWindows_3110_; uint8_t v_allowImportAll_3111_; uint8_t v_fixedToolchain_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3120_; 
v_toWorkspaceConfig_3080_ = lean_ctor_get(v_cfg_3079_, 0);
v_toLeanConfig_3081_ = lean_ctor_get(v_cfg_3079_, 1);
v_bootstrap_3082_ = lean_ctor_get_uint8(v_cfg_3079_, sizeof(void*)*26);
v_extraDepTargets_3083_ = lean_ctor_get(v_cfg_3079_, 2);
v_precompileModules_3084_ = lean_ctor_get_uint8(v_cfg_3079_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3085_ = lean_ctor_get(v_cfg_3079_, 3);
v_srcDir_3086_ = lean_ctor_get(v_cfg_3079_, 4);
v_buildDir_3087_ = lean_ctor_get(v_cfg_3079_, 5);
v_leanLibDir_3088_ = lean_ctor_get(v_cfg_3079_, 6);
v_nativeLibDir_3089_ = lean_ctor_get(v_cfg_3079_, 7);
v_binDir_3090_ = lean_ctor_get(v_cfg_3079_, 8);
v_irDir_3091_ = lean_ctor_get(v_cfg_3079_, 9);
v_releaseRepo_3092_ = lean_ctor_get(v_cfg_3079_, 10);
v_buildArchive_3093_ = lean_ctor_get(v_cfg_3079_, 11);
v_preferReleaseBuild_3094_ = lean_ctor_get_uint8(v_cfg_3079_, sizeof(void*)*26 + 2);
v_testDriver_3095_ = lean_ctor_get(v_cfg_3079_, 12);
v_testDriverArgs_3096_ = lean_ctor_get(v_cfg_3079_, 13);
v_lintDriver_3097_ = lean_ctor_get(v_cfg_3079_, 14);
v_lintDriverArgs_3098_ = lean_ctor_get(v_cfg_3079_, 15);
v_version_3099_ = lean_ctor_get(v_cfg_3079_, 16);
v_versionTags_3100_ = lean_ctor_get(v_cfg_3079_, 17);
v_description_3101_ = lean_ctor_get(v_cfg_3079_, 18);
v_keywords_3102_ = lean_ctor_get(v_cfg_3079_, 19);
v_homepage_3103_ = lean_ctor_get(v_cfg_3079_, 20);
v_license_3104_ = lean_ctor_get(v_cfg_3079_, 21);
v_licenseFiles_3105_ = lean_ctor_get(v_cfg_3079_, 22);
v_readmeFile_3106_ = lean_ctor_get(v_cfg_3079_, 23);
v_reservoir_3107_ = lean_ctor_get_uint8(v_cfg_3079_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3108_ = lean_ctor_get(v_cfg_3079_, 24);
v_restoreAllArtifacts_x3f_3109_ = lean_ctor_get(v_cfg_3079_, 25);
v_libPrefixOnWindows_3110_ = lean_ctor_get_uint8(v_cfg_3079_, sizeof(void*)*26 + 4);
v_allowImportAll_3111_ = lean_ctor_get_uint8(v_cfg_3079_, sizeof(void*)*26 + 5);
v_fixedToolchain_3112_ = lean_ctor_get_uint8(v_cfg_3079_, sizeof(void*)*26 + 6);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_cfg_3079_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3114_ = v_cfg_3079_;
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3109_);
lean_inc(v_enableArtifactCache_x3f_3108_);
lean_inc(v_readmeFile_3106_);
lean_inc(v_licenseFiles_3105_);
lean_inc(v_license_3104_);
lean_inc(v_homepage_3103_);
lean_inc(v_keywords_3102_);
lean_inc(v_description_3101_);
lean_inc(v_versionTags_3100_);
lean_inc(v_version_3099_);
lean_inc(v_lintDriverArgs_3098_);
lean_inc(v_lintDriver_3097_);
lean_inc(v_testDriverArgs_3096_);
lean_inc(v_testDriver_3095_);
lean_inc(v_buildArchive_3093_);
lean_inc(v_releaseRepo_3092_);
lean_inc(v_irDir_3091_);
lean_inc(v_binDir_3090_);
lean_inc(v_nativeLibDir_3089_);
lean_inc(v_leanLibDir_3088_);
lean_inc(v_buildDir_3087_);
lean_inc(v_srcDir_3086_);
lean_inc(v_moreGlobalServerArgs_3085_);
lean_inc(v_extraDepTargets_3083_);
lean_inc(v_toLeanConfig_3081_);
lean_inc(v_toWorkspaceConfig_3080_);
lean_dec(v_cfg_3079_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_apply_1(v_f_3078_, v_enableArtifactCache_x3f_3108_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 24, v___x_3116_);
v___x_3118_ = v___x_3114_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_toWorkspaceConfig_3080_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_toLeanConfig_3081_);
lean_ctor_set(v_reuseFailAlloc_3119_, 2, v_extraDepTargets_3083_);
lean_ctor_set(v_reuseFailAlloc_3119_, 3, v_moreGlobalServerArgs_3085_);
lean_ctor_set(v_reuseFailAlloc_3119_, 4, v_srcDir_3086_);
lean_ctor_set(v_reuseFailAlloc_3119_, 5, v_buildDir_3087_);
lean_ctor_set(v_reuseFailAlloc_3119_, 6, v_leanLibDir_3088_);
lean_ctor_set(v_reuseFailAlloc_3119_, 7, v_nativeLibDir_3089_);
lean_ctor_set(v_reuseFailAlloc_3119_, 8, v_binDir_3090_);
lean_ctor_set(v_reuseFailAlloc_3119_, 9, v_irDir_3091_);
lean_ctor_set(v_reuseFailAlloc_3119_, 10, v_releaseRepo_3092_);
lean_ctor_set(v_reuseFailAlloc_3119_, 11, v_buildArchive_3093_);
lean_ctor_set(v_reuseFailAlloc_3119_, 12, v_testDriver_3095_);
lean_ctor_set(v_reuseFailAlloc_3119_, 13, v_testDriverArgs_3096_);
lean_ctor_set(v_reuseFailAlloc_3119_, 14, v_lintDriver_3097_);
lean_ctor_set(v_reuseFailAlloc_3119_, 15, v_lintDriverArgs_3098_);
lean_ctor_set(v_reuseFailAlloc_3119_, 16, v_version_3099_);
lean_ctor_set(v_reuseFailAlloc_3119_, 17, v_versionTags_3100_);
lean_ctor_set(v_reuseFailAlloc_3119_, 18, v_description_3101_);
lean_ctor_set(v_reuseFailAlloc_3119_, 19, v_keywords_3102_);
lean_ctor_set(v_reuseFailAlloc_3119_, 20, v_homepage_3103_);
lean_ctor_set(v_reuseFailAlloc_3119_, 21, v_license_3104_);
lean_ctor_set(v_reuseFailAlloc_3119_, 22, v_licenseFiles_3105_);
lean_ctor_set(v_reuseFailAlloc_3119_, 23, v_readmeFile_3106_);
lean_ctor_set(v_reuseFailAlloc_3119_, 24, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3119_, 25, v_restoreAllArtifacts_x3f_3109_);
lean_ctor_set_uint8(v_reuseFailAlloc_3119_, sizeof(void*)*26, v_bootstrap_3082_);
lean_ctor_set_uint8(v_reuseFailAlloc_3119_, sizeof(void*)*26 + 1, v_precompileModules_3084_);
lean_ctor_set_uint8(v_reuseFailAlloc_3119_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3094_);
lean_ctor_set_uint8(v_reuseFailAlloc_3119_, sizeof(void*)*26 + 3, v_reservoir_3107_);
lean_ctor_set_uint8(v_reuseFailAlloc_3119_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3110_);
lean_ctor_set_uint8(v_reuseFailAlloc_3119_, sizeof(void*)*26 + 5, v_allowImportAll_3111_);
lean_ctor_set_uint8(v_reuseFailAlloc_3119_, sizeof(void*)*26 + 6, v_fixedToolchain_3112_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(lean_object* v_x_3121_){
_start:
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_box(0);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3___boxed(lean_object* v_x_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(v_x_3123_);
lean_dec_ref(v_x_3123_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object* v_p_3134_, lean_object* v_n_3135_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = ((lean_object*)(l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__4));
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object* v_p_3137_, lean_object* v_n_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3137_, v_n_3138_);
lean_dec(v_n_3138_);
lean_dec(v_p_3137_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object* v_p_3140_, lean_object* v_n_3141_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3140_, v_n_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object* v_p_3143_, lean_object* v_n_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(v_p_3143_, v_n_3144_);
lean_dec(v_n_3144_);
lean_dec(v_p_3143_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object* v_p_3146_, lean_object* v_n_3147_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3146_, v_n_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object* v_p_3149_, lean_object* v_n_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField(v_p_3149_, v_n_3150_);
lean_dec(v_n_3150_);
lean_dec(v_p_3149_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(lean_object* v_cfg_3152_){
_start:
{
lean_object* v_restoreAllArtifacts_x3f_3153_; 
v_restoreAllArtifacts_x3f_3153_ = lean_ctor_get(v_cfg_3152_, 25);
lean_inc(v_restoreAllArtifacts_x3f_3153_);
return v_restoreAllArtifacts_x3f_3153_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0___boxed(lean_object* v_cfg_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(v_cfg_3154_);
lean_dec_ref(v_cfg_3154_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__1(lean_object* v_val_3156_, lean_object* v_cfg_3157_){
_start:
{
lean_object* v_toWorkspaceConfig_3158_; lean_object* v_toLeanConfig_3159_; uint8_t v_bootstrap_3160_; lean_object* v_extraDepTargets_3161_; uint8_t v_precompileModules_3162_; lean_object* v_moreGlobalServerArgs_3163_; lean_object* v_srcDir_3164_; lean_object* v_buildDir_3165_; lean_object* v_leanLibDir_3166_; lean_object* v_nativeLibDir_3167_; lean_object* v_binDir_3168_; lean_object* v_irDir_3169_; lean_object* v_releaseRepo_3170_; lean_object* v_buildArchive_3171_; uint8_t v_preferReleaseBuild_3172_; lean_object* v_testDriver_3173_; lean_object* v_testDriverArgs_3174_; lean_object* v_lintDriver_3175_; lean_object* v_lintDriverArgs_3176_; lean_object* v_version_3177_; lean_object* v_versionTags_3178_; lean_object* v_description_3179_; lean_object* v_keywords_3180_; lean_object* v_homepage_3181_; lean_object* v_license_3182_; lean_object* v_licenseFiles_3183_; lean_object* v_readmeFile_3184_; uint8_t v_reservoir_3185_; lean_object* v_enableArtifactCache_x3f_3186_; uint8_t v_libPrefixOnWindows_3187_; uint8_t v_allowImportAll_3188_; uint8_t v_fixedToolchain_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
v_toWorkspaceConfig_3158_ = lean_ctor_get(v_cfg_3157_, 0);
v_toLeanConfig_3159_ = lean_ctor_get(v_cfg_3157_, 1);
v_bootstrap_3160_ = lean_ctor_get_uint8(v_cfg_3157_, sizeof(void*)*26);
v_extraDepTargets_3161_ = lean_ctor_get(v_cfg_3157_, 2);
v_precompileModules_3162_ = lean_ctor_get_uint8(v_cfg_3157_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3163_ = lean_ctor_get(v_cfg_3157_, 3);
v_srcDir_3164_ = lean_ctor_get(v_cfg_3157_, 4);
v_buildDir_3165_ = lean_ctor_get(v_cfg_3157_, 5);
v_leanLibDir_3166_ = lean_ctor_get(v_cfg_3157_, 6);
v_nativeLibDir_3167_ = lean_ctor_get(v_cfg_3157_, 7);
v_binDir_3168_ = lean_ctor_get(v_cfg_3157_, 8);
v_irDir_3169_ = lean_ctor_get(v_cfg_3157_, 9);
v_releaseRepo_3170_ = lean_ctor_get(v_cfg_3157_, 10);
v_buildArchive_3171_ = lean_ctor_get(v_cfg_3157_, 11);
v_preferReleaseBuild_3172_ = lean_ctor_get_uint8(v_cfg_3157_, sizeof(void*)*26 + 2);
v_testDriver_3173_ = lean_ctor_get(v_cfg_3157_, 12);
v_testDriverArgs_3174_ = lean_ctor_get(v_cfg_3157_, 13);
v_lintDriver_3175_ = lean_ctor_get(v_cfg_3157_, 14);
v_lintDriverArgs_3176_ = lean_ctor_get(v_cfg_3157_, 15);
v_version_3177_ = lean_ctor_get(v_cfg_3157_, 16);
v_versionTags_3178_ = lean_ctor_get(v_cfg_3157_, 17);
v_description_3179_ = lean_ctor_get(v_cfg_3157_, 18);
v_keywords_3180_ = lean_ctor_get(v_cfg_3157_, 19);
v_homepage_3181_ = lean_ctor_get(v_cfg_3157_, 20);
v_license_3182_ = lean_ctor_get(v_cfg_3157_, 21);
v_licenseFiles_3183_ = lean_ctor_get(v_cfg_3157_, 22);
v_readmeFile_3184_ = lean_ctor_get(v_cfg_3157_, 23);
v_reservoir_3185_ = lean_ctor_get_uint8(v_cfg_3157_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3186_ = lean_ctor_get(v_cfg_3157_, 24);
v_libPrefixOnWindows_3187_ = lean_ctor_get_uint8(v_cfg_3157_, sizeof(void*)*26 + 4);
v_allowImportAll_3188_ = lean_ctor_get_uint8(v_cfg_3157_, sizeof(void*)*26 + 5);
v_fixedToolchain_3189_ = lean_ctor_get_uint8(v_cfg_3157_, sizeof(void*)*26 + 6);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_cfg_3157_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; 
v_unused_3197_ = lean_ctor_get(v_cfg_3157_, 25);
lean_dec(v_unused_3197_);
v___x_3191_ = v_cfg_3157_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_enableArtifactCache_x3f_3186_);
lean_inc(v_readmeFile_3184_);
lean_inc(v_licenseFiles_3183_);
lean_inc(v_license_3182_);
lean_inc(v_homepage_3181_);
lean_inc(v_keywords_3180_);
lean_inc(v_description_3179_);
lean_inc(v_versionTags_3178_);
lean_inc(v_version_3177_);
lean_inc(v_lintDriverArgs_3176_);
lean_inc(v_lintDriver_3175_);
lean_inc(v_testDriverArgs_3174_);
lean_inc(v_testDriver_3173_);
lean_inc(v_buildArchive_3171_);
lean_inc(v_releaseRepo_3170_);
lean_inc(v_irDir_3169_);
lean_inc(v_binDir_3168_);
lean_inc(v_nativeLibDir_3167_);
lean_inc(v_leanLibDir_3166_);
lean_inc(v_buildDir_3165_);
lean_inc(v_srcDir_3164_);
lean_inc(v_moreGlobalServerArgs_3163_);
lean_inc(v_extraDepTargets_3161_);
lean_inc(v_toLeanConfig_3159_);
lean_inc(v_toWorkspaceConfig_3158_);
lean_dec(v_cfg_3157_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 25, v_val_3156_);
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_toWorkspaceConfig_3158_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_toLeanConfig_3159_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_extraDepTargets_3161_);
lean_ctor_set(v_reuseFailAlloc_3195_, 3, v_moreGlobalServerArgs_3163_);
lean_ctor_set(v_reuseFailAlloc_3195_, 4, v_srcDir_3164_);
lean_ctor_set(v_reuseFailAlloc_3195_, 5, v_buildDir_3165_);
lean_ctor_set(v_reuseFailAlloc_3195_, 6, v_leanLibDir_3166_);
lean_ctor_set(v_reuseFailAlloc_3195_, 7, v_nativeLibDir_3167_);
lean_ctor_set(v_reuseFailAlloc_3195_, 8, v_binDir_3168_);
lean_ctor_set(v_reuseFailAlloc_3195_, 9, v_irDir_3169_);
lean_ctor_set(v_reuseFailAlloc_3195_, 10, v_releaseRepo_3170_);
lean_ctor_set(v_reuseFailAlloc_3195_, 11, v_buildArchive_3171_);
lean_ctor_set(v_reuseFailAlloc_3195_, 12, v_testDriver_3173_);
lean_ctor_set(v_reuseFailAlloc_3195_, 13, v_testDriverArgs_3174_);
lean_ctor_set(v_reuseFailAlloc_3195_, 14, v_lintDriver_3175_);
lean_ctor_set(v_reuseFailAlloc_3195_, 15, v_lintDriverArgs_3176_);
lean_ctor_set(v_reuseFailAlloc_3195_, 16, v_version_3177_);
lean_ctor_set(v_reuseFailAlloc_3195_, 17, v_versionTags_3178_);
lean_ctor_set(v_reuseFailAlloc_3195_, 18, v_description_3179_);
lean_ctor_set(v_reuseFailAlloc_3195_, 19, v_keywords_3180_);
lean_ctor_set(v_reuseFailAlloc_3195_, 20, v_homepage_3181_);
lean_ctor_set(v_reuseFailAlloc_3195_, 21, v_license_3182_);
lean_ctor_set(v_reuseFailAlloc_3195_, 22, v_licenseFiles_3183_);
lean_ctor_set(v_reuseFailAlloc_3195_, 23, v_readmeFile_3184_);
lean_ctor_set(v_reuseFailAlloc_3195_, 24, v_enableArtifactCache_x3f_3186_);
lean_ctor_set(v_reuseFailAlloc_3195_, 25, v_val_3156_);
lean_ctor_set_uint8(v_reuseFailAlloc_3195_, sizeof(void*)*26, v_bootstrap_3160_);
lean_ctor_set_uint8(v_reuseFailAlloc_3195_, sizeof(void*)*26 + 1, v_precompileModules_3162_);
lean_ctor_set_uint8(v_reuseFailAlloc_3195_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3172_);
lean_ctor_set_uint8(v_reuseFailAlloc_3195_, sizeof(void*)*26 + 3, v_reservoir_3185_);
lean_ctor_set_uint8(v_reuseFailAlloc_3195_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3187_);
lean_ctor_set_uint8(v_reuseFailAlloc_3195_, sizeof(void*)*26 + 5, v_allowImportAll_3188_);
lean_ctor_set_uint8(v_reuseFailAlloc_3195_, sizeof(void*)*26 + 6, v_fixedToolchain_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__2(lean_object* v_f_3198_, lean_object* v_cfg_3199_){
_start:
{
lean_object* v_toWorkspaceConfig_3200_; lean_object* v_toLeanConfig_3201_; uint8_t v_bootstrap_3202_; lean_object* v_extraDepTargets_3203_; uint8_t v_precompileModules_3204_; lean_object* v_moreGlobalServerArgs_3205_; lean_object* v_srcDir_3206_; lean_object* v_buildDir_3207_; lean_object* v_leanLibDir_3208_; lean_object* v_nativeLibDir_3209_; lean_object* v_binDir_3210_; lean_object* v_irDir_3211_; lean_object* v_releaseRepo_3212_; lean_object* v_buildArchive_3213_; uint8_t v_preferReleaseBuild_3214_; lean_object* v_testDriver_3215_; lean_object* v_testDriverArgs_3216_; lean_object* v_lintDriver_3217_; lean_object* v_lintDriverArgs_3218_; lean_object* v_version_3219_; lean_object* v_versionTags_3220_; lean_object* v_description_3221_; lean_object* v_keywords_3222_; lean_object* v_homepage_3223_; lean_object* v_license_3224_; lean_object* v_licenseFiles_3225_; lean_object* v_readmeFile_3226_; uint8_t v_reservoir_3227_; lean_object* v_enableArtifactCache_x3f_3228_; lean_object* v_restoreAllArtifacts_x3f_3229_; uint8_t v_libPrefixOnWindows_3230_; uint8_t v_allowImportAll_3231_; uint8_t v_fixedToolchain_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3240_; 
v_toWorkspaceConfig_3200_ = lean_ctor_get(v_cfg_3199_, 0);
v_toLeanConfig_3201_ = lean_ctor_get(v_cfg_3199_, 1);
v_bootstrap_3202_ = lean_ctor_get_uint8(v_cfg_3199_, sizeof(void*)*26);
v_extraDepTargets_3203_ = lean_ctor_get(v_cfg_3199_, 2);
v_precompileModules_3204_ = lean_ctor_get_uint8(v_cfg_3199_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3205_ = lean_ctor_get(v_cfg_3199_, 3);
v_srcDir_3206_ = lean_ctor_get(v_cfg_3199_, 4);
v_buildDir_3207_ = lean_ctor_get(v_cfg_3199_, 5);
v_leanLibDir_3208_ = lean_ctor_get(v_cfg_3199_, 6);
v_nativeLibDir_3209_ = lean_ctor_get(v_cfg_3199_, 7);
v_binDir_3210_ = lean_ctor_get(v_cfg_3199_, 8);
v_irDir_3211_ = lean_ctor_get(v_cfg_3199_, 9);
v_releaseRepo_3212_ = lean_ctor_get(v_cfg_3199_, 10);
v_buildArchive_3213_ = lean_ctor_get(v_cfg_3199_, 11);
v_preferReleaseBuild_3214_ = lean_ctor_get_uint8(v_cfg_3199_, sizeof(void*)*26 + 2);
v_testDriver_3215_ = lean_ctor_get(v_cfg_3199_, 12);
v_testDriverArgs_3216_ = lean_ctor_get(v_cfg_3199_, 13);
v_lintDriver_3217_ = lean_ctor_get(v_cfg_3199_, 14);
v_lintDriverArgs_3218_ = lean_ctor_get(v_cfg_3199_, 15);
v_version_3219_ = lean_ctor_get(v_cfg_3199_, 16);
v_versionTags_3220_ = lean_ctor_get(v_cfg_3199_, 17);
v_description_3221_ = lean_ctor_get(v_cfg_3199_, 18);
v_keywords_3222_ = lean_ctor_get(v_cfg_3199_, 19);
v_homepage_3223_ = lean_ctor_get(v_cfg_3199_, 20);
v_license_3224_ = lean_ctor_get(v_cfg_3199_, 21);
v_licenseFiles_3225_ = lean_ctor_get(v_cfg_3199_, 22);
v_readmeFile_3226_ = lean_ctor_get(v_cfg_3199_, 23);
v_reservoir_3227_ = lean_ctor_get_uint8(v_cfg_3199_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3228_ = lean_ctor_get(v_cfg_3199_, 24);
v_restoreAllArtifacts_x3f_3229_ = lean_ctor_get(v_cfg_3199_, 25);
v_libPrefixOnWindows_3230_ = lean_ctor_get_uint8(v_cfg_3199_, sizeof(void*)*26 + 4);
v_allowImportAll_3231_ = lean_ctor_get_uint8(v_cfg_3199_, sizeof(void*)*26 + 5);
v_fixedToolchain_3232_ = lean_ctor_get_uint8(v_cfg_3199_, sizeof(void*)*26 + 6);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_cfg_3199_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3234_ = v_cfg_3199_;
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3229_);
lean_inc(v_enableArtifactCache_x3f_3228_);
lean_inc(v_readmeFile_3226_);
lean_inc(v_licenseFiles_3225_);
lean_inc(v_license_3224_);
lean_inc(v_homepage_3223_);
lean_inc(v_keywords_3222_);
lean_inc(v_description_3221_);
lean_inc(v_versionTags_3220_);
lean_inc(v_version_3219_);
lean_inc(v_lintDriverArgs_3218_);
lean_inc(v_lintDriver_3217_);
lean_inc(v_testDriverArgs_3216_);
lean_inc(v_testDriver_3215_);
lean_inc(v_buildArchive_3213_);
lean_inc(v_releaseRepo_3212_);
lean_inc(v_irDir_3211_);
lean_inc(v_binDir_3210_);
lean_inc(v_nativeLibDir_3209_);
lean_inc(v_leanLibDir_3208_);
lean_inc(v_buildDir_3207_);
lean_inc(v_srcDir_3206_);
lean_inc(v_moreGlobalServerArgs_3205_);
lean_inc(v_extraDepTargets_3203_);
lean_inc(v_toLeanConfig_3201_);
lean_inc(v_toWorkspaceConfig_3200_);
lean_dec(v_cfg_3199_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3236_ = lean_apply_1(v_f_3198_, v_restoreAllArtifacts_x3f_3229_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 25, v___x_3236_);
v___x_3238_ = v___x_3234_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_toWorkspaceConfig_3200_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_toLeanConfig_3201_);
lean_ctor_set(v_reuseFailAlloc_3239_, 2, v_extraDepTargets_3203_);
lean_ctor_set(v_reuseFailAlloc_3239_, 3, v_moreGlobalServerArgs_3205_);
lean_ctor_set(v_reuseFailAlloc_3239_, 4, v_srcDir_3206_);
lean_ctor_set(v_reuseFailAlloc_3239_, 5, v_buildDir_3207_);
lean_ctor_set(v_reuseFailAlloc_3239_, 6, v_leanLibDir_3208_);
lean_ctor_set(v_reuseFailAlloc_3239_, 7, v_nativeLibDir_3209_);
lean_ctor_set(v_reuseFailAlloc_3239_, 8, v_binDir_3210_);
lean_ctor_set(v_reuseFailAlloc_3239_, 9, v_irDir_3211_);
lean_ctor_set(v_reuseFailAlloc_3239_, 10, v_releaseRepo_3212_);
lean_ctor_set(v_reuseFailAlloc_3239_, 11, v_buildArchive_3213_);
lean_ctor_set(v_reuseFailAlloc_3239_, 12, v_testDriver_3215_);
lean_ctor_set(v_reuseFailAlloc_3239_, 13, v_testDriverArgs_3216_);
lean_ctor_set(v_reuseFailAlloc_3239_, 14, v_lintDriver_3217_);
lean_ctor_set(v_reuseFailAlloc_3239_, 15, v_lintDriverArgs_3218_);
lean_ctor_set(v_reuseFailAlloc_3239_, 16, v_version_3219_);
lean_ctor_set(v_reuseFailAlloc_3239_, 17, v_versionTags_3220_);
lean_ctor_set(v_reuseFailAlloc_3239_, 18, v_description_3221_);
lean_ctor_set(v_reuseFailAlloc_3239_, 19, v_keywords_3222_);
lean_ctor_set(v_reuseFailAlloc_3239_, 20, v_homepage_3223_);
lean_ctor_set(v_reuseFailAlloc_3239_, 21, v_license_3224_);
lean_ctor_set(v_reuseFailAlloc_3239_, 22, v_licenseFiles_3225_);
lean_ctor_set(v_reuseFailAlloc_3239_, 23, v_readmeFile_3226_);
lean_ctor_set(v_reuseFailAlloc_3239_, 24, v_enableArtifactCache_x3f_3228_);
lean_ctor_set(v_reuseFailAlloc_3239_, 25, v___x_3236_);
lean_ctor_set_uint8(v_reuseFailAlloc_3239_, sizeof(void*)*26, v_bootstrap_3202_);
lean_ctor_set_uint8(v_reuseFailAlloc_3239_, sizeof(void*)*26 + 1, v_precompileModules_3204_);
lean_ctor_set_uint8(v_reuseFailAlloc_3239_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3214_);
lean_ctor_set_uint8(v_reuseFailAlloc_3239_, sizeof(void*)*26 + 3, v_reservoir_3227_);
lean_ctor_set_uint8(v_reuseFailAlloc_3239_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3230_);
lean_ctor_set_uint8(v_reuseFailAlloc_3239_, sizeof(void*)*26 + 5, v_allowImportAll_3231_);
lean_ctor_set_uint8(v_reuseFailAlloc_3239_, sizeof(void*)*26 + 6, v_fixedToolchain_3232_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object* v_p_3249_, lean_object* v_n_3250_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = ((lean_object*)(l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__3));
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___boxed(lean_object* v_p_3252_, lean_object* v_n_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3252_, v_n_3253_);
lean_dec(v_n_3253_);
lean_dec(v_p_3252_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object* v_p_3255_, lean_object* v_n_3256_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3255_, v_n_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object* v_p_3258_, lean_object* v_n_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(v_p_3258_, v_n_3259_);
lean_dec(v_n_3259_);
lean_dec(v_p_3258_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object* v_p_3261_, lean_object* v_n_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3261_, v_n_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object* v_p_3264_, lean_object* v_n_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(v_p_3264_, v_n_3265_);
lean_dec(v_n_3265_);
lean_dec(v_p_3264_);
return v_res_3266_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(lean_object* v_cfg_3267_){
_start:
{
uint8_t v_libPrefixOnWindows_3268_; 
v_libPrefixOnWindows_3268_ = lean_ctor_get_uint8(v_cfg_3267_, sizeof(void*)*26 + 4);
return v_libPrefixOnWindows_3268_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object* v_cfg_3269_){
_start:
{
uint8_t v_res_3270_; lean_object* v_r_3271_; 
v_res_3270_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(v_cfg_3269_);
lean_dec_ref(v_cfg_3269_);
v_r_3271_ = lean_box(v_res_3270_);
return v_r_3271_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(uint8_t v_val_3272_, lean_object* v_cfg_3273_){
_start:
{
lean_object* v_toWorkspaceConfig_3274_; lean_object* v_toLeanConfig_3275_; uint8_t v_bootstrap_3276_; lean_object* v_extraDepTargets_3277_; uint8_t v_precompileModules_3278_; lean_object* v_moreGlobalServerArgs_3279_; lean_object* v_srcDir_3280_; lean_object* v_buildDir_3281_; lean_object* v_leanLibDir_3282_; lean_object* v_nativeLibDir_3283_; lean_object* v_binDir_3284_; lean_object* v_irDir_3285_; lean_object* v_releaseRepo_3286_; lean_object* v_buildArchive_3287_; uint8_t v_preferReleaseBuild_3288_; lean_object* v_testDriver_3289_; lean_object* v_testDriverArgs_3290_; lean_object* v_lintDriver_3291_; lean_object* v_lintDriverArgs_3292_; lean_object* v_version_3293_; lean_object* v_versionTags_3294_; lean_object* v_description_3295_; lean_object* v_keywords_3296_; lean_object* v_homepage_3297_; lean_object* v_license_3298_; lean_object* v_licenseFiles_3299_; lean_object* v_readmeFile_3300_; uint8_t v_reservoir_3301_; lean_object* v_enableArtifactCache_x3f_3302_; lean_object* v_restoreAllArtifacts_x3f_3303_; uint8_t v_allowImportAll_3304_; uint8_t v_fixedToolchain_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
v_toWorkspaceConfig_3274_ = lean_ctor_get(v_cfg_3273_, 0);
v_toLeanConfig_3275_ = lean_ctor_get(v_cfg_3273_, 1);
v_bootstrap_3276_ = lean_ctor_get_uint8(v_cfg_3273_, sizeof(void*)*26);
v_extraDepTargets_3277_ = lean_ctor_get(v_cfg_3273_, 2);
v_precompileModules_3278_ = lean_ctor_get_uint8(v_cfg_3273_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3279_ = lean_ctor_get(v_cfg_3273_, 3);
v_srcDir_3280_ = lean_ctor_get(v_cfg_3273_, 4);
v_buildDir_3281_ = lean_ctor_get(v_cfg_3273_, 5);
v_leanLibDir_3282_ = lean_ctor_get(v_cfg_3273_, 6);
v_nativeLibDir_3283_ = lean_ctor_get(v_cfg_3273_, 7);
v_binDir_3284_ = lean_ctor_get(v_cfg_3273_, 8);
v_irDir_3285_ = lean_ctor_get(v_cfg_3273_, 9);
v_releaseRepo_3286_ = lean_ctor_get(v_cfg_3273_, 10);
v_buildArchive_3287_ = lean_ctor_get(v_cfg_3273_, 11);
v_preferReleaseBuild_3288_ = lean_ctor_get_uint8(v_cfg_3273_, sizeof(void*)*26 + 2);
v_testDriver_3289_ = lean_ctor_get(v_cfg_3273_, 12);
v_testDriverArgs_3290_ = lean_ctor_get(v_cfg_3273_, 13);
v_lintDriver_3291_ = lean_ctor_get(v_cfg_3273_, 14);
v_lintDriverArgs_3292_ = lean_ctor_get(v_cfg_3273_, 15);
v_version_3293_ = lean_ctor_get(v_cfg_3273_, 16);
v_versionTags_3294_ = lean_ctor_get(v_cfg_3273_, 17);
v_description_3295_ = lean_ctor_get(v_cfg_3273_, 18);
v_keywords_3296_ = lean_ctor_get(v_cfg_3273_, 19);
v_homepage_3297_ = lean_ctor_get(v_cfg_3273_, 20);
v_license_3298_ = lean_ctor_get(v_cfg_3273_, 21);
v_licenseFiles_3299_ = lean_ctor_get(v_cfg_3273_, 22);
v_readmeFile_3300_ = lean_ctor_get(v_cfg_3273_, 23);
v_reservoir_3301_ = lean_ctor_get_uint8(v_cfg_3273_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3302_ = lean_ctor_get(v_cfg_3273_, 24);
v_restoreAllArtifacts_x3f_3303_ = lean_ctor_get(v_cfg_3273_, 25);
v_allowImportAll_3304_ = lean_ctor_get_uint8(v_cfg_3273_, sizeof(void*)*26 + 5);
v_fixedToolchain_3305_ = lean_ctor_get_uint8(v_cfg_3273_, sizeof(void*)*26 + 6);
v_isSharedCheck_3312_ = !lean_is_exclusive(v_cfg_3273_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v_cfg_3273_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3303_);
lean_inc(v_enableArtifactCache_x3f_3302_);
lean_inc(v_readmeFile_3300_);
lean_inc(v_licenseFiles_3299_);
lean_inc(v_license_3298_);
lean_inc(v_homepage_3297_);
lean_inc(v_keywords_3296_);
lean_inc(v_description_3295_);
lean_inc(v_versionTags_3294_);
lean_inc(v_version_3293_);
lean_inc(v_lintDriverArgs_3292_);
lean_inc(v_lintDriver_3291_);
lean_inc(v_testDriverArgs_3290_);
lean_inc(v_testDriver_3289_);
lean_inc(v_buildArchive_3287_);
lean_inc(v_releaseRepo_3286_);
lean_inc(v_irDir_3285_);
lean_inc(v_binDir_3284_);
lean_inc(v_nativeLibDir_3283_);
lean_inc(v_leanLibDir_3282_);
lean_inc(v_buildDir_3281_);
lean_inc(v_srcDir_3280_);
lean_inc(v_moreGlobalServerArgs_3279_);
lean_inc(v_extraDepTargets_3277_);
lean_inc(v_toLeanConfig_3275_);
lean_inc(v_toWorkspaceConfig_3274_);
lean_dec(v_cfg_3273_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_toWorkspaceConfig_3274_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v_toLeanConfig_3275_);
lean_ctor_set(v_reuseFailAlloc_3311_, 2, v_extraDepTargets_3277_);
lean_ctor_set(v_reuseFailAlloc_3311_, 3, v_moreGlobalServerArgs_3279_);
lean_ctor_set(v_reuseFailAlloc_3311_, 4, v_srcDir_3280_);
lean_ctor_set(v_reuseFailAlloc_3311_, 5, v_buildDir_3281_);
lean_ctor_set(v_reuseFailAlloc_3311_, 6, v_leanLibDir_3282_);
lean_ctor_set(v_reuseFailAlloc_3311_, 7, v_nativeLibDir_3283_);
lean_ctor_set(v_reuseFailAlloc_3311_, 8, v_binDir_3284_);
lean_ctor_set(v_reuseFailAlloc_3311_, 9, v_irDir_3285_);
lean_ctor_set(v_reuseFailAlloc_3311_, 10, v_releaseRepo_3286_);
lean_ctor_set(v_reuseFailAlloc_3311_, 11, v_buildArchive_3287_);
lean_ctor_set(v_reuseFailAlloc_3311_, 12, v_testDriver_3289_);
lean_ctor_set(v_reuseFailAlloc_3311_, 13, v_testDriverArgs_3290_);
lean_ctor_set(v_reuseFailAlloc_3311_, 14, v_lintDriver_3291_);
lean_ctor_set(v_reuseFailAlloc_3311_, 15, v_lintDriverArgs_3292_);
lean_ctor_set(v_reuseFailAlloc_3311_, 16, v_version_3293_);
lean_ctor_set(v_reuseFailAlloc_3311_, 17, v_versionTags_3294_);
lean_ctor_set(v_reuseFailAlloc_3311_, 18, v_description_3295_);
lean_ctor_set(v_reuseFailAlloc_3311_, 19, v_keywords_3296_);
lean_ctor_set(v_reuseFailAlloc_3311_, 20, v_homepage_3297_);
lean_ctor_set(v_reuseFailAlloc_3311_, 21, v_license_3298_);
lean_ctor_set(v_reuseFailAlloc_3311_, 22, v_licenseFiles_3299_);
lean_ctor_set(v_reuseFailAlloc_3311_, 23, v_readmeFile_3300_);
lean_ctor_set(v_reuseFailAlloc_3311_, 24, v_enableArtifactCache_x3f_3302_);
lean_ctor_set(v_reuseFailAlloc_3311_, 25, v_restoreAllArtifacts_x3f_3303_);
lean_ctor_set_uint8(v_reuseFailAlloc_3311_, sizeof(void*)*26, v_bootstrap_3276_);
lean_ctor_set_uint8(v_reuseFailAlloc_3311_, sizeof(void*)*26 + 1, v_precompileModules_3278_);
lean_ctor_set_uint8(v_reuseFailAlloc_3311_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3288_);
lean_ctor_set_uint8(v_reuseFailAlloc_3311_, sizeof(void*)*26 + 3, v_reservoir_3301_);
lean_ctor_set_uint8(v_reuseFailAlloc_3311_, sizeof(void*)*26 + 5, v_allowImportAll_3304_);
lean_ctor_set_uint8(v_reuseFailAlloc_3311_, sizeof(void*)*26 + 6, v_fixedToolchain_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*26 + 4, v_val_3272_);
return v___x_3310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object* v_val_3313_, lean_object* v_cfg_3314_){
_start:
{
uint8_t v_val_134__boxed_3315_; lean_object* v_res_3316_; 
v_val_134__boxed_3315_ = lean_unbox(v_val_3313_);
v_res_3316_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(v_val_134__boxed_3315_, v_cfg_3314_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__2(lean_object* v_f_3317_, lean_object* v_cfg_3318_){
_start:
{
lean_object* v_toWorkspaceConfig_3319_; lean_object* v_toLeanConfig_3320_; uint8_t v_bootstrap_3321_; lean_object* v_extraDepTargets_3322_; uint8_t v_precompileModules_3323_; lean_object* v_moreGlobalServerArgs_3324_; lean_object* v_srcDir_3325_; lean_object* v_buildDir_3326_; lean_object* v_leanLibDir_3327_; lean_object* v_nativeLibDir_3328_; lean_object* v_binDir_3329_; lean_object* v_irDir_3330_; lean_object* v_releaseRepo_3331_; lean_object* v_buildArchive_3332_; uint8_t v_preferReleaseBuild_3333_; lean_object* v_testDriver_3334_; lean_object* v_testDriverArgs_3335_; lean_object* v_lintDriver_3336_; lean_object* v_lintDriverArgs_3337_; lean_object* v_version_3338_; lean_object* v_versionTags_3339_; lean_object* v_description_3340_; lean_object* v_keywords_3341_; lean_object* v_homepage_3342_; lean_object* v_license_3343_; lean_object* v_licenseFiles_3344_; lean_object* v_readmeFile_3345_; uint8_t v_reservoir_3346_; lean_object* v_enableArtifactCache_x3f_3347_; lean_object* v_restoreAllArtifacts_x3f_3348_; uint8_t v_libPrefixOnWindows_3349_; uint8_t v_allowImportAll_3350_; uint8_t v_fixedToolchain_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3361_; 
v_toWorkspaceConfig_3319_ = lean_ctor_get(v_cfg_3318_, 0);
v_toLeanConfig_3320_ = lean_ctor_get(v_cfg_3318_, 1);
v_bootstrap_3321_ = lean_ctor_get_uint8(v_cfg_3318_, sizeof(void*)*26);
v_extraDepTargets_3322_ = lean_ctor_get(v_cfg_3318_, 2);
v_precompileModules_3323_ = lean_ctor_get_uint8(v_cfg_3318_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3324_ = lean_ctor_get(v_cfg_3318_, 3);
v_srcDir_3325_ = lean_ctor_get(v_cfg_3318_, 4);
v_buildDir_3326_ = lean_ctor_get(v_cfg_3318_, 5);
v_leanLibDir_3327_ = lean_ctor_get(v_cfg_3318_, 6);
v_nativeLibDir_3328_ = lean_ctor_get(v_cfg_3318_, 7);
v_binDir_3329_ = lean_ctor_get(v_cfg_3318_, 8);
v_irDir_3330_ = lean_ctor_get(v_cfg_3318_, 9);
v_releaseRepo_3331_ = lean_ctor_get(v_cfg_3318_, 10);
v_buildArchive_3332_ = lean_ctor_get(v_cfg_3318_, 11);
v_preferReleaseBuild_3333_ = lean_ctor_get_uint8(v_cfg_3318_, sizeof(void*)*26 + 2);
v_testDriver_3334_ = lean_ctor_get(v_cfg_3318_, 12);
v_testDriverArgs_3335_ = lean_ctor_get(v_cfg_3318_, 13);
v_lintDriver_3336_ = lean_ctor_get(v_cfg_3318_, 14);
v_lintDriverArgs_3337_ = lean_ctor_get(v_cfg_3318_, 15);
v_version_3338_ = lean_ctor_get(v_cfg_3318_, 16);
v_versionTags_3339_ = lean_ctor_get(v_cfg_3318_, 17);
v_description_3340_ = lean_ctor_get(v_cfg_3318_, 18);
v_keywords_3341_ = lean_ctor_get(v_cfg_3318_, 19);
v_homepage_3342_ = lean_ctor_get(v_cfg_3318_, 20);
v_license_3343_ = lean_ctor_get(v_cfg_3318_, 21);
v_licenseFiles_3344_ = lean_ctor_get(v_cfg_3318_, 22);
v_readmeFile_3345_ = lean_ctor_get(v_cfg_3318_, 23);
v_reservoir_3346_ = lean_ctor_get_uint8(v_cfg_3318_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3347_ = lean_ctor_get(v_cfg_3318_, 24);
v_restoreAllArtifacts_x3f_3348_ = lean_ctor_get(v_cfg_3318_, 25);
v_libPrefixOnWindows_3349_ = lean_ctor_get_uint8(v_cfg_3318_, sizeof(void*)*26 + 4);
v_allowImportAll_3350_ = lean_ctor_get_uint8(v_cfg_3318_, sizeof(void*)*26 + 5);
v_fixedToolchain_3351_ = lean_ctor_get_uint8(v_cfg_3318_, sizeof(void*)*26 + 6);
v_isSharedCheck_3361_ = !lean_is_exclusive(v_cfg_3318_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3353_ = v_cfg_3318_;
v_isShared_3354_ = v_isSharedCheck_3361_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3348_);
lean_inc(v_enableArtifactCache_x3f_3347_);
lean_inc(v_readmeFile_3345_);
lean_inc(v_licenseFiles_3344_);
lean_inc(v_license_3343_);
lean_inc(v_homepage_3342_);
lean_inc(v_keywords_3341_);
lean_inc(v_description_3340_);
lean_inc(v_versionTags_3339_);
lean_inc(v_version_3338_);
lean_inc(v_lintDriverArgs_3337_);
lean_inc(v_lintDriver_3336_);
lean_inc(v_testDriverArgs_3335_);
lean_inc(v_testDriver_3334_);
lean_inc(v_buildArchive_3332_);
lean_inc(v_releaseRepo_3331_);
lean_inc(v_irDir_3330_);
lean_inc(v_binDir_3329_);
lean_inc(v_nativeLibDir_3328_);
lean_inc(v_leanLibDir_3327_);
lean_inc(v_buildDir_3326_);
lean_inc(v_srcDir_3325_);
lean_inc(v_moreGlobalServerArgs_3324_);
lean_inc(v_extraDepTargets_3322_);
lean_inc(v_toLeanConfig_3320_);
lean_inc(v_toWorkspaceConfig_3319_);
lean_dec(v_cfg_3318_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3361_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3355_ = lean_box(v_libPrefixOnWindows_3349_);
v___x_3356_ = lean_apply_1(v_f_3317_, v___x_3355_);
if (v_isShared_3354_ == 0)
{
v___x_3358_ = v___x_3353_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_toWorkspaceConfig_3319_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_toLeanConfig_3320_);
lean_ctor_set(v_reuseFailAlloc_3360_, 2, v_extraDepTargets_3322_);
lean_ctor_set(v_reuseFailAlloc_3360_, 3, v_moreGlobalServerArgs_3324_);
lean_ctor_set(v_reuseFailAlloc_3360_, 4, v_srcDir_3325_);
lean_ctor_set(v_reuseFailAlloc_3360_, 5, v_buildDir_3326_);
lean_ctor_set(v_reuseFailAlloc_3360_, 6, v_leanLibDir_3327_);
lean_ctor_set(v_reuseFailAlloc_3360_, 7, v_nativeLibDir_3328_);
lean_ctor_set(v_reuseFailAlloc_3360_, 8, v_binDir_3329_);
lean_ctor_set(v_reuseFailAlloc_3360_, 9, v_irDir_3330_);
lean_ctor_set(v_reuseFailAlloc_3360_, 10, v_releaseRepo_3331_);
lean_ctor_set(v_reuseFailAlloc_3360_, 11, v_buildArchive_3332_);
lean_ctor_set(v_reuseFailAlloc_3360_, 12, v_testDriver_3334_);
lean_ctor_set(v_reuseFailAlloc_3360_, 13, v_testDriverArgs_3335_);
lean_ctor_set(v_reuseFailAlloc_3360_, 14, v_lintDriver_3336_);
lean_ctor_set(v_reuseFailAlloc_3360_, 15, v_lintDriverArgs_3337_);
lean_ctor_set(v_reuseFailAlloc_3360_, 16, v_version_3338_);
lean_ctor_set(v_reuseFailAlloc_3360_, 17, v_versionTags_3339_);
lean_ctor_set(v_reuseFailAlloc_3360_, 18, v_description_3340_);
lean_ctor_set(v_reuseFailAlloc_3360_, 19, v_keywords_3341_);
lean_ctor_set(v_reuseFailAlloc_3360_, 20, v_homepage_3342_);
lean_ctor_set(v_reuseFailAlloc_3360_, 21, v_license_3343_);
lean_ctor_set(v_reuseFailAlloc_3360_, 22, v_licenseFiles_3344_);
lean_ctor_set(v_reuseFailAlloc_3360_, 23, v_readmeFile_3345_);
lean_ctor_set(v_reuseFailAlloc_3360_, 24, v_enableArtifactCache_x3f_3347_);
lean_ctor_set(v_reuseFailAlloc_3360_, 25, v_restoreAllArtifacts_x3f_3348_);
lean_ctor_set_uint8(v_reuseFailAlloc_3360_, sizeof(void*)*26, v_bootstrap_3321_);
lean_ctor_set_uint8(v_reuseFailAlloc_3360_, sizeof(void*)*26 + 1, v_precompileModules_3323_);
lean_ctor_set_uint8(v_reuseFailAlloc_3360_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3333_);
lean_ctor_set_uint8(v_reuseFailAlloc_3360_, sizeof(void*)*26 + 3, v_reservoir_3346_);
v___x_3358_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
uint8_t v___x_3359_; 
v___x_3359_ = lean_unbox(v___x_3356_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*26 + 4, v___x_3359_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*26 + 5, v_allowImportAll_3350_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*26 + 6, v_fixedToolchain_3351_);
return v___x_3358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object* v_p_3370_, lean_object* v_n_3371_){
_start:
{
lean_object* v___x_3372_; 
v___x_3372_ = ((lean_object*)(l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__3));
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object* v_p_3373_, lean_object* v_n_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3373_, v_n_3374_);
lean_dec(v_n_3374_);
lean_dec(v_p_3373_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object* v_p_3376_, lean_object* v_n_3377_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3376_, v_n_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_p_3379_, lean_object* v_n_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(v_p_3379_, v_n_3380_);
lean_dec(v_n_3380_);
lean_dec(v_p_3379_);
return v_res_3381_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_allowImportAll___proj___lam__0(lean_object* v_cfg_3382_){
_start:
{
uint8_t v_allowImportAll_3383_; 
v_allowImportAll_3383_ = lean_ctor_get_uint8(v_cfg_3382_, sizeof(void*)*26 + 5);
return v_allowImportAll_3383_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__0___boxed(lean_object* v_cfg_3384_){
_start:
{
uint8_t v_res_3385_; lean_object* v_r_3386_; 
v_res_3385_ = l_Lake_PackageConfig_allowImportAll___proj___lam__0(v_cfg_3384_);
lean_dec_ref(v_cfg_3384_);
v_r_3386_ = lean_box(v_res_3385_);
return v_r_3386_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1(uint8_t v_val_3387_, lean_object* v_cfg_3388_){
_start:
{
lean_object* v_toWorkspaceConfig_3389_; lean_object* v_toLeanConfig_3390_; uint8_t v_bootstrap_3391_; lean_object* v_extraDepTargets_3392_; uint8_t v_precompileModules_3393_; lean_object* v_moreGlobalServerArgs_3394_; lean_object* v_srcDir_3395_; lean_object* v_buildDir_3396_; lean_object* v_leanLibDir_3397_; lean_object* v_nativeLibDir_3398_; lean_object* v_binDir_3399_; lean_object* v_irDir_3400_; lean_object* v_releaseRepo_3401_; lean_object* v_buildArchive_3402_; uint8_t v_preferReleaseBuild_3403_; lean_object* v_testDriver_3404_; lean_object* v_testDriverArgs_3405_; lean_object* v_lintDriver_3406_; lean_object* v_lintDriverArgs_3407_; lean_object* v_version_3408_; lean_object* v_versionTags_3409_; lean_object* v_description_3410_; lean_object* v_keywords_3411_; lean_object* v_homepage_3412_; lean_object* v_license_3413_; lean_object* v_licenseFiles_3414_; lean_object* v_readmeFile_3415_; uint8_t v_reservoir_3416_; lean_object* v_enableArtifactCache_x3f_3417_; lean_object* v_restoreAllArtifacts_x3f_3418_; uint8_t v_libPrefixOnWindows_3419_; uint8_t v_fixedToolchain_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
v_toWorkspaceConfig_3389_ = lean_ctor_get(v_cfg_3388_, 0);
v_toLeanConfig_3390_ = lean_ctor_get(v_cfg_3388_, 1);
v_bootstrap_3391_ = lean_ctor_get_uint8(v_cfg_3388_, sizeof(void*)*26);
v_extraDepTargets_3392_ = lean_ctor_get(v_cfg_3388_, 2);
v_precompileModules_3393_ = lean_ctor_get_uint8(v_cfg_3388_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3394_ = lean_ctor_get(v_cfg_3388_, 3);
v_srcDir_3395_ = lean_ctor_get(v_cfg_3388_, 4);
v_buildDir_3396_ = lean_ctor_get(v_cfg_3388_, 5);
v_leanLibDir_3397_ = lean_ctor_get(v_cfg_3388_, 6);
v_nativeLibDir_3398_ = lean_ctor_get(v_cfg_3388_, 7);
v_binDir_3399_ = lean_ctor_get(v_cfg_3388_, 8);
v_irDir_3400_ = lean_ctor_get(v_cfg_3388_, 9);
v_releaseRepo_3401_ = lean_ctor_get(v_cfg_3388_, 10);
v_buildArchive_3402_ = lean_ctor_get(v_cfg_3388_, 11);
v_preferReleaseBuild_3403_ = lean_ctor_get_uint8(v_cfg_3388_, sizeof(void*)*26 + 2);
v_testDriver_3404_ = lean_ctor_get(v_cfg_3388_, 12);
v_testDriverArgs_3405_ = lean_ctor_get(v_cfg_3388_, 13);
v_lintDriver_3406_ = lean_ctor_get(v_cfg_3388_, 14);
v_lintDriverArgs_3407_ = lean_ctor_get(v_cfg_3388_, 15);
v_version_3408_ = lean_ctor_get(v_cfg_3388_, 16);
v_versionTags_3409_ = lean_ctor_get(v_cfg_3388_, 17);
v_description_3410_ = lean_ctor_get(v_cfg_3388_, 18);
v_keywords_3411_ = lean_ctor_get(v_cfg_3388_, 19);
v_homepage_3412_ = lean_ctor_get(v_cfg_3388_, 20);
v_license_3413_ = lean_ctor_get(v_cfg_3388_, 21);
v_licenseFiles_3414_ = lean_ctor_get(v_cfg_3388_, 22);
v_readmeFile_3415_ = lean_ctor_get(v_cfg_3388_, 23);
v_reservoir_3416_ = lean_ctor_get_uint8(v_cfg_3388_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3417_ = lean_ctor_get(v_cfg_3388_, 24);
v_restoreAllArtifacts_x3f_3418_ = lean_ctor_get(v_cfg_3388_, 25);
v_libPrefixOnWindows_3419_ = lean_ctor_get_uint8(v_cfg_3388_, sizeof(void*)*26 + 4);
v_fixedToolchain_3420_ = lean_ctor_get_uint8(v_cfg_3388_, sizeof(void*)*26 + 6);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_cfg_3388_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v_cfg_3388_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3418_);
lean_inc(v_enableArtifactCache_x3f_3417_);
lean_inc(v_readmeFile_3415_);
lean_inc(v_licenseFiles_3414_);
lean_inc(v_license_3413_);
lean_inc(v_homepage_3412_);
lean_inc(v_keywords_3411_);
lean_inc(v_description_3410_);
lean_inc(v_versionTags_3409_);
lean_inc(v_version_3408_);
lean_inc(v_lintDriverArgs_3407_);
lean_inc(v_lintDriver_3406_);
lean_inc(v_testDriverArgs_3405_);
lean_inc(v_testDriver_3404_);
lean_inc(v_buildArchive_3402_);
lean_inc(v_releaseRepo_3401_);
lean_inc(v_irDir_3400_);
lean_inc(v_binDir_3399_);
lean_inc(v_nativeLibDir_3398_);
lean_inc(v_leanLibDir_3397_);
lean_inc(v_buildDir_3396_);
lean_inc(v_srcDir_3395_);
lean_inc(v_moreGlobalServerArgs_3394_);
lean_inc(v_extraDepTargets_3392_);
lean_inc(v_toLeanConfig_3390_);
lean_inc(v_toWorkspaceConfig_3389_);
lean_dec(v_cfg_3388_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_toWorkspaceConfig_3389_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_toLeanConfig_3390_);
lean_ctor_set(v_reuseFailAlloc_3426_, 2, v_extraDepTargets_3392_);
lean_ctor_set(v_reuseFailAlloc_3426_, 3, v_moreGlobalServerArgs_3394_);
lean_ctor_set(v_reuseFailAlloc_3426_, 4, v_srcDir_3395_);
lean_ctor_set(v_reuseFailAlloc_3426_, 5, v_buildDir_3396_);
lean_ctor_set(v_reuseFailAlloc_3426_, 6, v_leanLibDir_3397_);
lean_ctor_set(v_reuseFailAlloc_3426_, 7, v_nativeLibDir_3398_);
lean_ctor_set(v_reuseFailAlloc_3426_, 8, v_binDir_3399_);
lean_ctor_set(v_reuseFailAlloc_3426_, 9, v_irDir_3400_);
lean_ctor_set(v_reuseFailAlloc_3426_, 10, v_releaseRepo_3401_);
lean_ctor_set(v_reuseFailAlloc_3426_, 11, v_buildArchive_3402_);
lean_ctor_set(v_reuseFailAlloc_3426_, 12, v_testDriver_3404_);
lean_ctor_set(v_reuseFailAlloc_3426_, 13, v_testDriverArgs_3405_);
lean_ctor_set(v_reuseFailAlloc_3426_, 14, v_lintDriver_3406_);
lean_ctor_set(v_reuseFailAlloc_3426_, 15, v_lintDriverArgs_3407_);
lean_ctor_set(v_reuseFailAlloc_3426_, 16, v_version_3408_);
lean_ctor_set(v_reuseFailAlloc_3426_, 17, v_versionTags_3409_);
lean_ctor_set(v_reuseFailAlloc_3426_, 18, v_description_3410_);
lean_ctor_set(v_reuseFailAlloc_3426_, 19, v_keywords_3411_);
lean_ctor_set(v_reuseFailAlloc_3426_, 20, v_homepage_3412_);
lean_ctor_set(v_reuseFailAlloc_3426_, 21, v_license_3413_);
lean_ctor_set(v_reuseFailAlloc_3426_, 22, v_licenseFiles_3414_);
lean_ctor_set(v_reuseFailAlloc_3426_, 23, v_readmeFile_3415_);
lean_ctor_set(v_reuseFailAlloc_3426_, 24, v_enableArtifactCache_x3f_3417_);
lean_ctor_set(v_reuseFailAlloc_3426_, 25, v_restoreAllArtifacts_x3f_3418_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, sizeof(void*)*26, v_bootstrap_3391_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, sizeof(void*)*26 + 1, v_precompileModules_3393_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3403_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, sizeof(void*)*26 + 3, v_reservoir_3416_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3419_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, sizeof(void*)*26 + 6, v_fixedToolchain_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*26 + 5, v_val_3387_);
return v___x_3425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1___boxed(lean_object* v_val_3428_, lean_object* v_cfg_3429_){
_start:
{
uint8_t v_val_134__boxed_3430_; lean_object* v_res_3431_; 
v_val_134__boxed_3430_ = lean_unbox(v_val_3428_);
v_res_3431_ = l_Lake_PackageConfig_allowImportAll___proj___lam__1(v_val_134__boxed_3430_, v_cfg_3429_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__2(lean_object* v_f_3432_, lean_object* v_cfg_3433_){
_start:
{
lean_object* v_toWorkspaceConfig_3434_; lean_object* v_toLeanConfig_3435_; uint8_t v_bootstrap_3436_; lean_object* v_extraDepTargets_3437_; uint8_t v_precompileModules_3438_; lean_object* v_moreGlobalServerArgs_3439_; lean_object* v_srcDir_3440_; lean_object* v_buildDir_3441_; lean_object* v_leanLibDir_3442_; lean_object* v_nativeLibDir_3443_; lean_object* v_binDir_3444_; lean_object* v_irDir_3445_; lean_object* v_releaseRepo_3446_; lean_object* v_buildArchive_3447_; uint8_t v_preferReleaseBuild_3448_; lean_object* v_testDriver_3449_; lean_object* v_testDriverArgs_3450_; lean_object* v_lintDriver_3451_; lean_object* v_lintDriverArgs_3452_; lean_object* v_version_3453_; lean_object* v_versionTags_3454_; lean_object* v_description_3455_; lean_object* v_keywords_3456_; lean_object* v_homepage_3457_; lean_object* v_license_3458_; lean_object* v_licenseFiles_3459_; lean_object* v_readmeFile_3460_; uint8_t v_reservoir_3461_; lean_object* v_enableArtifactCache_x3f_3462_; lean_object* v_restoreAllArtifacts_x3f_3463_; uint8_t v_libPrefixOnWindows_3464_; uint8_t v_allowImportAll_3465_; uint8_t v_fixedToolchain_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3476_; 
v_toWorkspaceConfig_3434_ = lean_ctor_get(v_cfg_3433_, 0);
v_toLeanConfig_3435_ = lean_ctor_get(v_cfg_3433_, 1);
v_bootstrap_3436_ = lean_ctor_get_uint8(v_cfg_3433_, sizeof(void*)*26);
v_extraDepTargets_3437_ = lean_ctor_get(v_cfg_3433_, 2);
v_precompileModules_3438_ = lean_ctor_get_uint8(v_cfg_3433_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3439_ = lean_ctor_get(v_cfg_3433_, 3);
v_srcDir_3440_ = lean_ctor_get(v_cfg_3433_, 4);
v_buildDir_3441_ = lean_ctor_get(v_cfg_3433_, 5);
v_leanLibDir_3442_ = lean_ctor_get(v_cfg_3433_, 6);
v_nativeLibDir_3443_ = lean_ctor_get(v_cfg_3433_, 7);
v_binDir_3444_ = lean_ctor_get(v_cfg_3433_, 8);
v_irDir_3445_ = lean_ctor_get(v_cfg_3433_, 9);
v_releaseRepo_3446_ = lean_ctor_get(v_cfg_3433_, 10);
v_buildArchive_3447_ = lean_ctor_get(v_cfg_3433_, 11);
v_preferReleaseBuild_3448_ = lean_ctor_get_uint8(v_cfg_3433_, sizeof(void*)*26 + 2);
v_testDriver_3449_ = lean_ctor_get(v_cfg_3433_, 12);
v_testDriverArgs_3450_ = lean_ctor_get(v_cfg_3433_, 13);
v_lintDriver_3451_ = lean_ctor_get(v_cfg_3433_, 14);
v_lintDriverArgs_3452_ = lean_ctor_get(v_cfg_3433_, 15);
v_version_3453_ = lean_ctor_get(v_cfg_3433_, 16);
v_versionTags_3454_ = lean_ctor_get(v_cfg_3433_, 17);
v_description_3455_ = lean_ctor_get(v_cfg_3433_, 18);
v_keywords_3456_ = lean_ctor_get(v_cfg_3433_, 19);
v_homepage_3457_ = lean_ctor_get(v_cfg_3433_, 20);
v_license_3458_ = lean_ctor_get(v_cfg_3433_, 21);
v_licenseFiles_3459_ = lean_ctor_get(v_cfg_3433_, 22);
v_readmeFile_3460_ = lean_ctor_get(v_cfg_3433_, 23);
v_reservoir_3461_ = lean_ctor_get_uint8(v_cfg_3433_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3462_ = lean_ctor_get(v_cfg_3433_, 24);
v_restoreAllArtifacts_x3f_3463_ = lean_ctor_get(v_cfg_3433_, 25);
v_libPrefixOnWindows_3464_ = lean_ctor_get_uint8(v_cfg_3433_, sizeof(void*)*26 + 4);
v_allowImportAll_3465_ = lean_ctor_get_uint8(v_cfg_3433_, sizeof(void*)*26 + 5);
v_fixedToolchain_3466_ = lean_ctor_get_uint8(v_cfg_3433_, sizeof(void*)*26 + 6);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_cfg_3433_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3468_ = v_cfg_3433_;
v_isShared_3469_ = v_isSharedCheck_3476_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3463_);
lean_inc(v_enableArtifactCache_x3f_3462_);
lean_inc(v_readmeFile_3460_);
lean_inc(v_licenseFiles_3459_);
lean_inc(v_license_3458_);
lean_inc(v_homepage_3457_);
lean_inc(v_keywords_3456_);
lean_inc(v_description_3455_);
lean_inc(v_versionTags_3454_);
lean_inc(v_version_3453_);
lean_inc(v_lintDriverArgs_3452_);
lean_inc(v_lintDriver_3451_);
lean_inc(v_testDriverArgs_3450_);
lean_inc(v_testDriver_3449_);
lean_inc(v_buildArchive_3447_);
lean_inc(v_releaseRepo_3446_);
lean_inc(v_irDir_3445_);
lean_inc(v_binDir_3444_);
lean_inc(v_nativeLibDir_3443_);
lean_inc(v_leanLibDir_3442_);
lean_inc(v_buildDir_3441_);
lean_inc(v_srcDir_3440_);
lean_inc(v_moreGlobalServerArgs_3439_);
lean_inc(v_extraDepTargets_3437_);
lean_inc(v_toLeanConfig_3435_);
lean_inc(v_toWorkspaceConfig_3434_);
lean_dec(v_cfg_3433_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3476_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3470_ = lean_box(v_allowImportAll_3465_);
v___x_3471_ = lean_apply_1(v_f_3432_, v___x_3470_);
if (v_isShared_3469_ == 0)
{
v___x_3473_ = v___x_3468_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_toWorkspaceConfig_3434_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_toLeanConfig_3435_);
lean_ctor_set(v_reuseFailAlloc_3475_, 2, v_extraDepTargets_3437_);
lean_ctor_set(v_reuseFailAlloc_3475_, 3, v_moreGlobalServerArgs_3439_);
lean_ctor_set(v_reuseFailAlloc_3475_, 4, v_srcDir_3440_);
lean_ctor_set(v_reuseFailAlloc_3475_, 5, v_buildDir_3441_);
lean_ctor_set(v_reuseFailAlloc_3475_, 6, v_leanLibDir_3442_);
lean_ctor_set(v_reuseFailAlloc_3475_, 7, v_nativeLibDir_3443_);
lean_ctor_set(v_reuseFailAlloc_3475_, 8, v_binDir_3444_);
lean_ctor_set(v_reuseFailAlloc_3475_, 9, v_irDir_3445_);
lean_ctor_set(v_reuseFailAlloc_3475_, 10, v_releaseRepo_3446_);
lean_ctor_set(v_reuseFailAlloc_3475_, 11, v_buildArchive_3447_);
lean_ctor_set(v_reuseFailAlloc_3475_, 12, v_testDriver_3449_);
lean_ctor_set(v_reuseFailAlloc_3475_, 13, v_testDriverArgs_3450_);
lean_ctor_set(v_reuseFailAlloc_3475_, 14, v_lintDriver_3451_);
lean_ctor_set(v_reuseFailAlloc_3475_, 15, v_lintDriverArgs_3452_);
lean_ctor_set(v_reuseFailAlloc_3475_, 16, v_version_3453_);
lean_ctor_set(v_reuseFailAlloc_3475_, 17, v_versionTags_3454_);
lean_ctor_set(v_reuseFailAlloc_3475_, 18, v_description_3455_);
lean_ctor_set(v_reuseFailAlloc_3475_, 19, v_keywords_3456_);
lean_ctor_set(v_reuseFailAlloc_3475_, 20, v_homepage_3457_);
lean_ctor_set(v_reuseFailAlloc_3475_, 21, v_license_3458_);
lean_ctor_set(v_reuseFailAlloc_3475_, 22, v_licenseFiles_3459_);
lean_ctor_set(v_reuseFailAlloc_3475_, 23, v_readmeFile_3460_);
lean_ctor_set(v_reuseFailAlloc_3475_, 24, v_enableArtifactCache_x3f_3462_);
lean_ctor_set(v_reuseFailAlloc_3475_, 25, v_restoreAllArtifacts_x3f_3463_);
lean_ctor_set_uint8(v_reuseFailAlloc_3475_, sizeof(void*)*26, v_bootstrap_3436_);
lean_ctor_set_uint8(v_reuseFailAlloc_3475_, sizeof(void*)*26 + 1, v_precompileModules_3438_);
lean_ctor_set_uint8(v_reuseFailAlloc_3475_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3448_);
lean_ctor_set_uint8(v_reuseFailAlloc_3475_, sizeof(void*)*26 + 3, v_reservoir_3461_);
lean_ctor_set_uint8(v_reuseFailAlloc_3475_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3464_);
v___x_3473_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
uint8_t v___x_3474_; 
v___x_3474_ = lean_unbox(v___x_3471_);
lean_ctor_set_uint8(v___x_3473_, sizeof(void*)*26 + 5, v___x_3474_);
lean_ctor_set_uint8(v___x_3473_, sizeof(void*)*26 + 6, v_fixedToolchain_3466_);
return v___x_3473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object* v_p_3485_, lean_object* v_n_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = ((lean_object*)(l_Lake_PackageConfig_allowImportAll___proj___closed__3));
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object* v_p_3488_, lean_object* v_n_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3488_, v_n_3489_);
lean_dec(v_n_3489_);
lean_dec(v_p_3488_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object* v_p_3491_, lean_object* v_n_3492_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3491_, v_n_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object* v_p_3494_, lean_object* v_n_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lake_PackageConfig_allowImportAll_instConfigField(v_p_3494_, v_n_3495_);
lean_dec(v_n_3495_);
lean_dec(v_p_3494_);
return v_res_3496_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_fixedToolchain___proj___lam__0(lean_object* v_cfg_3497_){
_start:
{
uint8_t v_fixedToolchain_3498_; 
v_fixedToolchain_3498_ = lean_ctor_get_uint8(v_cfg_3497_, sizeof(void*)*26 + 6);
return v_fixedToolchain_3498_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__0___boxed(lean_object* v_cfg_3499_){
_start:
{
uint8_t v_res_3500_; lean_object* v_r_3501_; 
v_res_3500_ = l_Lake_PackageConfig_fixedToolchain___proj___lam__0(v_cfg_3499_);
lean_dec_ref(v_cfg_3499_);
v_r_3501_ = lean_box(v_res_3500_);
return v_r_3501_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1(uint8_t v_val_3502_, lean_object* v_cfg_3503_){
_start:
{
lean_object* v_toWorkspaceConfig_3504_; lean_object* v_toLeanConfig_3505_; uint8_t v_bootstrap_3506_; lean_object* v_extraDepTargets_3507_; uint8_t v_precompileModules_3508_; lean_object* v_moreGlobalServerArgs_3509_; lean_object* v_srcDir_3510_; lean_object* v_buildDir_3511_; lean_object* v_leanLibDir_3512_; lean_object* v_nativeLibDir_3513_; lean_object* v_binDir_3514_; lean_object* v_irDir_3515_; lean_object* v_releaseRepo_3516_; lean_object* v_buildArchive_3517_; uint8_t v_preferReleaseBuild_3518_; lean_object* v_testDriver_3519_; lean_object* v_testDriverArgs_3520_; lean_object* v_lintDriver_3521_; lean_object* v_lintDriverArgs_3522_; lean_object* v_version_3523_; lean_object* v_versionTags_3524_; lean_object* v_description_3525_; lean_object* v_keywords_3526_; lean_object* v_homepage_3527_; lean_object* v_license_3528_; lean_object* v_licenseFiles_3529_; lean_object* v_readmeFile_3530_; uint8_t v_reservoir_3531_; lean_object* v_enableArtifactCache_x3f_3532_; lean_object* v_restoreAllArtifacts_x3f_3533_; uint8_t v_libPrefixOnWindows_3534_; uint8_t v_allowImportAll_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
v_toWorkspaceConfig_3504_ = lean_ctor_get(v_cfg_3503_, 0);
v_toLeanConfig_3505_ = lean_ctor_get(v_cfg_3503_, 1);
v_bootstrap_3506_ = lean_ctor_get_uint8(v_cfg_3503_, sizeof(void*)*26);
v_extraDepTargets_3507_ = lean_ctor_get(v_cfg_3503_, 2);
v_precompileModules_3508_ = lean_ctor_get_uint8(v_cfg_3503_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3509_ = lean_ctor_get(v_cfg_3503_, 3);
v_srcDir_3510_ = lean_ctor_get(v_cfg_3503_, 4);
v_buildDir_3511_ = lean_ctor_get(v_cfg_3503_, 5);
v_leanLibDir_3512_ = lean_ctor_get(v_cfg_3503_, 6);
v_nativeLibDir_3513_ = lean_ctor_get(v_cfg_3503_, 7);
v_binDir_3514_ = lean_ctor_get(v_cfg_3503_, 8);
v_irDir_3515_ = lean_ctor_get(v_cfg_3503_, 9);
v_releaseRepo_3516_ = lean_ctor_get(v_cfg_3503_, 10);
v_buildArchive_3517_ = lean_ctor_get(v_cfg_3503_, 11);
v_preferReleaseBuild_3518_ = lean_ctor_get_uint8(v_cfg_3503_, sizeof(void*)*26 + 2);
v_testDriver_3519_ = lean_ctor_get(v_cfg_3503_, 12);
v_testDriverArgs_3520_ = lean_ctor_get(v_cfg_3503_, 13);
v_lintDriver_3521_ = lean_ctor_get(v_cfg_3503_, 14);
v_lintDriverArgs_3522_ = lean_ctor_get(v_cfg_3503_, 15);
v_version_3523_ = lean_ctor_get(v_cfg_3503_, 16);
v_versionTags_3524_ = lean_ctor_get(v_cfg_3503_, 17);
v_description_3525_ = lean_ctor_get(v_cfg_3503_, 18);
v_keywords_3526_ = lean_ctor_get(v_cfg_3503_, 19);
v_homepage_3527_ = lean_ctor_get(v_cfg_3503_, 20);
v_license_3528_ = lean_ctor_get(v_cfg_3503_, 21);
v_licenseFiles_3529_ = lean_ctor_get(v_cfg_3503_, 22);
v_readmeFile_3530_ = lean_ctor_get(v_cfg_3503_, 23);
v_reservoir_3531_ = lean_ctor_get_uint8(v_cfg_3503_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3532_ = lean_ctor_get(v_cfg_3503_, 24);
v_restoreAllArtifacts_x3f_3533_ = lean_ctor_get(v_cfg_3503_, 25);
v_libPrefixOnWindows_3534_ = lean_ctor_get_uint8(v_cfg_3503_, sizeof(void*)*26 + 4);
v_allowImportAll_3535_ = lean_ctor_get_uint8(v_cfg_3503_, sizeof(void*)*26 + 5);
v_isSharedCheck_3542_ = !lean_is_exclusive(v_cfg_3503_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v_cfg_3503_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3533_);
lean_inc(v_enableArtifactCache_x3f_3532_);
lean_inc(v_readmeFile_3530_);
lean_inc(v_licenseFiles_3529_);
lean_inc(v_license_3528_);
lean_inc(v_homepage_3527_);
lean_inc(v_keywords_3526_);
lean_inc(v_description_3525_);
lean_inc(v_versionTags_3524_);
lean_inc(v_version_3523_);
lean_inc(v_lintDriverArgs_3522_);
lean_inc(v_lintDriver_3521_);
lean_inc(v_testDriverArgs_3520_);
lean_inc(v_testDriver_3519_);
lean_inc(v_buildArchive_3517_);
lean_inc(v_releaseRepo_3516_);
lean_inc(v_irDir_3515_);
lean_inc(v_binDir_3514_);
lean_inc(v_nativeLibDir_3513_);
lean_inc(v_leanLibDir_3512_);
lean_inc(v_buildDir_3511_);
lean_inc(v_srcDir_3510_);
lean_inc(v_moreGlobalServerArgs_3509_);
lean_inc(v_extraDepTargets_3507_);
lean_inc(v_toLeanConfig_3505_);
lean_inc(v_toWorkspaceConfig_3504_);
lean_dec(v_cfg_3503_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_toWorkspaceConfig_3504_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_toLeanConfig_3505_);
lean_ctor_set(v_reuseFailAlloc_3541_, 2, v_extraDepTargets_3507_);
lean_ctor_set(v_reuseFailAlloc_3541_, 3, v_moreGlobalServerArgs_3509_);
lean_ctor_set(v_reuseFailAlloc_3541_, 4, v_srcDir_3510_);
lean_ctor_set(v_reuseFailAlloc_3541_, 5, v_buildDir_3511_);
lean_ctor_set(v_reuseFailAlloc_3541_, 6, v_leanLibDir_3512_);
lean_ctor_set(v_reuseFailAlloc_3541_, 7, v_nativeLibDir_3513_);
lean_ctor_set(v_reuseFailAlloc_3541_, 8, v_binDir_3514_);
lean_ctor_set(v_reuseFailAlloc_3541_, 9, v_irDir_3515_);
lean_ctor_set(v_reuseFailAlloc_3541_, 10, v_releaseRepo_3516_);
lean_ctor_set(v_reuseFailAlloc_3541_, 11, v_buildArchive_3517_);
lean_ctor_set(v_reuseFailAlloc_3541_, 12, v_testDriver_3519_);
lean_ctor_set(v_reuseFailAlloc_3541_, 13, v_testDriverArgs_3520_);
lean_ctor_set(v_reuseFailAlloc_3541_, 14, v_lintDriver_3521_);
lean_ctor_set(v_reuseFailAlloc_3541_, 15, v_lintDriverArgs_3522_);
lean_ctor_set(v_reuseFailAlloc_3541_, 16, v_version_3523_);
lean_ctor_set(v_reuseFailAlloc_3541_, 17, v_versionTags_3524_);
lean_ctor_set(v_reuseFailAlloc_3541_, 18, v_description_3525_);
lean_ctor_set(v_reuseFailAlloc_3541_, 19, v_keywords_3526_);
lean_ctor_set(v_reuseFailAlloc_3541_, 20, v_homepage_3527_);
lean_ctor_set(v_reuseFailAlloc_3541_, 21, v_license_3528_);
lean_ctor_set(v_reuseFailAlloc_3541_, 22, v_licenseFiles_3529_);
lean_ctor_set(v_reuseFailAlloc_3541_, 23, v_readmeFile_3530_);
lean_ctor_set(v_reuseFailAlloc_3541_, 24, v_enableArtifactCache_x3f_3532_);
lean_ctor_set(v_reuseFailAlloc_3541_, 25, v_restoreAllArtifacts_x3f_3533_);
lean_ctor_set_uint8(v_reuseFailAlloc_3541_, sizeof(void*)*26, v_bootstrap_3506_);
lean_ctor_set_uint8(v_reuseFailAlloc_3541_, sizeof(void*)*26 + 1, v_precompileModules_3508_);
lean_ctor_set_uint8(v_reuseFailAlloc_3541_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3518_);
lean_ctor_set_uint8(v_reuseFailAlloc_3541_, sizeof(void*)*26 + 3, v_reservoir_3531_);
lean_ctor_set_uint8(v_reuseFailAlloc_3541_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3534_);
lean_ctor_set_uint8(v_reuseFailAlloc_3541_, sizeof(void*)*26 + 5, v_allowImportAll_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_ctor_set_uint8(v___x_3540_, sizeof(void*)*26 + 6, v_val_3502_);
return v___x_3540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1___boxed(lean_object* v_val_3543_, lean_object* v_cfg_3544_){
_start:
{
uint8_t v_val_134__boxed_3545_; lean_object* v_res_3546_; 
v_val_134__boxed_3545_ = lean_unbox(v_val_3543_);
v_res_3546_ = l_Lake_PackageConfig_fixedToolchain___proj___lam__1(v_val_134__boxed_3545_, v_cfg_3544_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__2(lean_object* v_f_3547_, lean_object* v_cfg_3548_){
_start:
{
lean_object* v_toWorkspaceConfig_3549_; lean_object* v_toLeanConfig_3550_; uint8_t v_bootstrap_3551_; lean_object* v_extraDepTargets_3552_; uint8_t v_precompileModules_3553_; lean_object* v_moreGlobalServerArgs_3554_; lean_object* v_srcDir_3555_; lean_object* v_buildDir_3556_; lean_object* v_leanLibDir_3557_; lean_object* v_nativeLibDir_3558_; lean_object* v_binDir_3559_; lean_object* v_irDir_3560_; lean_object* v_releaseRepo_3561_; lean_object* v_buildArchive_3562_; uint8_t v_preferReleaseBuild_3563_; lean_object* v_testDriver_3564_; lean_object* v_testDriverArgs_3565_; lean_object* v_lintDriver_3566_; lean_object* v_lintDriverArgs_3567_; lean_object* v_version_3568_; lean_object* v_versionTags_3569_; lean_object* v_description_3570_; lean_object* v_keywords_3571_; lean_object* v_homepage_3572_; lean_object* v_license_3573_; lean_object* v_licenseFiles_3574_; lean_object* v_readmeFile_3575_; uint8_t v_reservoir_3576_; lean_object* v_enableArtifactCache_x3f_3577_; lean_object* v_restoreAllArtifacts_x3f_3578_; uint8_t v_libPrefixOnWindows_3579_; uint8_t v_allowImportAll_3580_; uint8_t v_fixedToolchain_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3591_; 
v_toWorkspaceConfig_3549_ = lean_ctor_get(v_cfg_3548_, 0);
v_toLeanConfig_3550_ = lean_ctor_get(v_cfg_3548_, 1);
v_bootstrap_3551_ = lean_ctor_get_uint8(v_cfg_3548_, sizeof(void*)*26);
v_extraDepTargets_3552_ = lean_ctor_get(v_cfg_3548_, 2);
v_precompileModules_3553_ = lean_ctor_get_uint8(v_cfg_3548_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3554_ = lean_ctor_get(v_cfg_3548_, 3);
v_srcDir_3555_ = lean_ctor_get(v_cfg_3548_, 4);
v_buildDir_3556_ = lean_ctor_get(v_cfg_3548_, 5);
v_leanLibDir_3557_ = lean_ctor_get(v_cfg_3548_, 6);
v_nativeLibDir_3558_ = lean_ctor_get(v_cfg_3548_, 7);
v_binDir_3559_ = lean_ctor_get(v_cfg_3548_, 8);
v_irDir_3560_ = lean_ctor_get(v_cfg_3548_, 9);
v_releaseRepo_3561_ = lean_ctor_get(v_cfg_3548_, 10);
v_buildArchive_3562_ = lean_ctor_get(v_cfg_3548_, 11);
v_preferReleaseBuild_3563_ = lean_ctor_get_uint8(v_cfg_3548_, sizeof(void*)*26 + 2);
v_testDriver_3564_ = lean_ctor_get(v_cfg_3548_, 12);
v_testDriverArgs_3565_ = lean_ctor_get(v_cfg_3548_, 13);
v_lintDriver_3566_ = lean_ctor_get(v_cfg_3548_, 14);
v_lintDriverArgs_3567_ = lean_ctor_get(v_cfg_3548_, 15);
v_version_3568_ = lean_ctor_get(v_cfg_3548_, 16);
v_versionTags_3569_ = lean_ctor_get(v_cfg_3548_, 17);
v_description_3570_ = lean_ctor_get(v_cfg_3548_, 18);
v_keywords_3571_ = lean_ctor_get(v_cfg_3548_, 19);
v_homepage_3572_ = lean_ctor_get(v_cfg_3548_, 20);
v_license_3573_ = lean_ctor_get(v_cfg_3548_, 21);
v_licenseFiles_3574_ = lean_ctor_get(v_cfg_3548_, 22);
v_readmeFile_3575_ = lean_ctor_get(v_cfg_3548_, 23);
v_reservoir_3576_ = lean_ctor_get_uint8(v_cfg_3548_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3577_ = lean_ctor_get(v_cfg_3548_, 24);
v_restoreAllArtifacts_x3f_3578_ = lean_ctor_get(v_cfg_3548_, 25);
v_libPrefixOnWindows_3579_ = lean_ctor_get_uint8(v_cfg_3548_, sizeof(void*)*26 + 4);
v_allowImportAll_3580_ = lean_ctor_get_uint8(v_cfg_3548_, sizeof(void*)*26 + 5);
v_fixedToolchain_3581_ = lean_ctor_get_uint8(v_cfg_3548_, sizeof(void*)*26 + 6);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_cfg_3548_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3583_ = v_cfg_3548_;
v_isShared_3584_ = v_isSharedCheck_3591_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3578_);
lean_inc(v_enableArtifactCache_x3f_3577_);
lean_inc(v_readmeFile_3575_);
lean_inc(v_licenseFiles_3574_);
lean_inc(v_license_3573_);
lean_inc(v_homepage_3572_);
lean_inc(v_keywords_3571_);
lean_inc(v_description_3570_);
lean_inc(v_versionTags_3569_);
lean_inc(v_version_3568_);
lean_inc(v_lintDriverArgs_3567_);
lean_inc(v_lintDriver_3566_);
lean_inc(v_testDriverArgs_3565_);
lean_inc(v_testDriver_3564_);
lean_inc(v_buildArchive_3562_);
lean_inc(v_releaseRepo_3561_);
lean_inc(v_irDir_3560_);
lean_inc(v_binDir_3559_);
lean_inc(v_nativeLibDir_3558_);
lean_inc(v_leanLibDir_3557_);
lean_inc(v_buildDir_3556_);
lean_inc(v_srcDir_3555_);
lean_inc(v_moreGlobalServerArgs_3554_);
lean_inc(v_extraDepTargets_3552_);
lean_inc(v_toLeanConfig_3550_);
lean_inc(v_toWorkspaceConfig_3549_);
lean_dec(v_cfg_3548_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3591_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3585_ = lean_box(v_fixedToolchain_3581_);
v___x_3586_ = lean_apply_1(v_f_3547_, v___x_3585_);
if (v_isShared_3584_ == 0)
{
v___x_3588_ = v___x_3583_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_toWorkspaceConfig_3549_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_toLeanConfig_3550_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_extraDepTargets_3552_);
lean_ctor_set(v_reuseFailAlloc_3590_, 3, v_moreGlobalServerArgs_3554_);
lean_ctor_set(v_reuseFailAlloc_3590_, 4, v_srcDir_3555_);
lean_ctor_set(v_reuseFailAlloc_3590_, 5, v_buildDir_3556_);
lean_ctor_set(v_reuseFailAlloc_3590_, 6, v_leanLibDir_3557_);
lean_ctor_set(v_reuseFailAlloc_3590_, 7, v_nativeLibDir_3558_);
lean_ctor_set(v_reuseFailAlloc_3590_, 8, v_binDir_3559_);
lean_ctor_set(v_reuseFailAlloc_3590_, 9, v_irDir_3560_);
lean_ctor_set(v_reuseFailAlloc_3590_, 10, v_releaseRepo_3561_);
lean_ctor_set(v_reuseFailAlloc_3590_, 11, v_buildArchive_3562_);
lean_ctor_set(v_reuseFailAlloc_3590_, 12, v_testDriver_3564_);
lean_ctor_set(v_reuseFailAlloc_3590_, 13, v_testDriverArgs_3565_);
lean_ctor_set(v_reuseFailAlloc_3590_, 14, v_lintDriver_3566_);
lean_ctor_set(v_reuseFailAlloc_3590_, 15, v_lintDriverArgs_3567_);
lean_ctor_set(v_reuseFailAlloc_3590_, 16, v_version_3568_);
lean_ctor_set(v_reuseFailAlloc_3590_, 17, v_versionTags_3569_);
lean_ctor_set(v_reuseFailAlloc_3590_, 18, v_description_3570_);
lean_ctor_set(v_reuseFailAlloc_3590_, 19, v_keywords_3571_);
lean_ctor_set(v_reuseFailAlloc_3590_, 20, v_homepage_3572_);
lean_ctor_set(v_reuseFailAlloc_3590_, 21, v_license_3573_);
lean_ctor_set(v_reuseFailAlloc_3590_, 22, v_licenseFiles_3574_);
lean_ctor_set(v_reuseFailAlloc_3590_, 23, v_readmeFile_3575_);
lean_ctor_set(v_reuseFailAlloc_3590_, 24, v_enableArtifactCache_x3f_3577_);
lean_ctor_set(v_reuseFailAlloc_3590_, 25, v_restoreAllArtifacts_x3f_3578_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*26, v_bootstrap_3551_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*26 + 1, v_precompileModules_3553_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3563_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*26 + 3, v_reservoir_3576_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3579_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*26 + 5, v_allowImportAll_3580_);
v___x_3588_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
uint8_t v___x_3589_; 
v___x_3589_ = lean_unbox(v___x_3586_);
lean_ctor_set_uint8(v___x_3588_, sizeof(void*)*26 + 6, v___x_3589_);
return v___x_3588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj(lean_object* v_p_3600_, lean_object* v_n_3601_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = ((lean_object*)(l_Lake_PackageConfig_fixedToolchain___proj___closed__3));
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___boxed(lean_object* v_p_3603_, lean_object* v_n_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_3603_, v_n_3604_);
lean_dec(v_n_3604_);
lean_dec(v_p_3603_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField(lean_object* v_p_3606_, lean_object* v_n_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_3606_, v_n_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___boxed(lean_object* v_p_3609_, lean_object* v_n_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lake_PackageConfig_fixedToolchain_instConfigField(v_p_3609_, v_n_3610_);
lean_dec(v_n_3610_);
lean_dec(v_p_3609_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(lean_object* v_cfg_3612_){
_start:
{
lean_object* v_toWorkspaceConfig_3613_; 
v_toWorkspaceConfig_3613_ = lean_ctor_get(v_cfg_3612_, 0);
lean_inc_ref(v_toWorkspaceConfig_3613_);
return v_toWorkspaceConfig_3613_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0___boxed(lean_object* v_cfg_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(v_cfg_3614_);
lean_dec_ref(v_cfg_3614_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__1(lean_object* v_val_3616_, lean_object* v_cfg_3617_){
_start:
{
lean_object* v_toLeanConfig_3618_; uint8_t v_bootstrap_3619_; lean_object* v_extraDepTargets_3620_; uint8_t v_precompileModules_3621_; lean_object* v_moreGlobalServerArgs_3622_; lean_object* v_srcDir_3623_; lean_object* v_buildDir_3624_; lean_object* v_leanLibDir_3625_; lean_object* v_nativeLibDir_3626_; lean_object* v_binDir_3627_; lean_object* v_irDir_3628_; lean_object* v_releaseRepo_3629_; lean_object* v_buildArchive_3630_; uint8_t v_preferReleaseBuild_3631_; lean_object* v_testDriver_3632_; lean_object* v_testDriverArgs_3633_; lean_object* v_lintDriver_3634_; lean_object* v_lintDriverArgs_3635_; lean_object* v_version_3636_; lean_object* v_versionTags_3637_; lean_object* v_description_3638_; lean_object* v_keywords_3639_; lean_object* v_homepage_3640_; lean_object* v_license_3641_; lean_object* v_licenseFiles_3642_; lean_object* v_readmeFile_3643_; uint8_t v_reservoir_3644_; lean_object* v_enableArtifactCache_x3f_3645_; lean_object* v_restoreAllArtifacts_x3f_3646_; uint8_t v_libPrefixOnWindows_3647_; uint8_t v_allowImportAll_3648_; uint8_t v_fixedToolchain_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
v_toLeanConfig_3618_ = lean_ctor_get(v_cfg_3617_, 1);
v_bootstrap_3619_ = lean_ctor_get_uint8(v_cfg_3617_, sizeof(void*)*26);
v_extraDepTargets_3620_ = lean_ctor_get(v_cfg_3617_, 2);
v_precompileModules_3621_ = lean_ctor_get_uint8(v_cfg_3617_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3622_ = lean_ctor_get(v_cfg_3617_, 3);
v_srcDir_3623_ = lean_ctor_get(v_cfg_3617_, 4);
v_buildDir_3624_ = lean_ctor_get(v_cfg_3617_, 5);
v_leanLibDir_3625_ = lean_ctor_get(v_cfg_3617_, 6);
v_nativeLibDir_3626_ = lean_ctor_get(v_cfg_3617_, 7);
v_binDir_3627_ = lean_ctor_get(v_cfg_3617_, 8);
v_irDir_3628_ = lean_ctor_get(v_cfg_3617_, 9);
v_releaseRepo_3629_ = lean_ctor_get(v_cfg_3617_, 10);
v_buildArchive_3630_ = lean_ctor_get(v_cfg_3617_, 11);
v_preferReleaseBuild_3631_ = lean_ctor_get_uint8(v_cfg_3617_, sizeof(void*)*26 + 2);
v_testDriver_3632_ = lean_ctor_get(v_cfg_3617_, 12);
v_testDriverArgs_3633_ = lean_ctor_get(v_cfg_3617_, 13);
v_lintDriver_3634_ = lean_ctor_get(v_cfg_3617_, 14);
v_lintDriverArgs_3635_ = lean_ctor_get(v_cfg_3617_, 15);
v_version_3636_ = lean_ctor_get(v_cfg_3617_, 16);
v_versionTags_3637_ = lean_ctor_get(v_cfg_3617_, 17);
v_description_3638_ = lean_ctor_get(v_cfg_3617_, 18);
v_keywords_3639_ = lean_ctor_get(v_cfg_3617_, 19);
v_homepage_3640_ = lean_ctor_get(v_cfg_3617_, 20);
v_license_3641_ = lean_ctor_get(v_cfg_3617_, 21);
v_licenseFiles_3642_ = lean_ctor_get(v_cfg_3617_, 22);
v_readmeFile_3643_ = lean_ctor_get(v_cfg_3617_, 23);
v_reservoir_3644_ = lean_ctor_get_uint8(v_cfg_3617_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3645_ = lean_ctor_get(v_cfg_3617_, 24);
v_restoreAllArtifacts_x3f_3646_ = lean_ctor_get(v_cfg_3617_, 25);
v_libPrefixOnWindows_3647_ = lean_ctor_get_uint8(v_cfg_3617_, sizeof(void*)*26 + 4);
v_allowImportAll_3648_ = lean_ctor_get_uint8(v_cfg_3617_, sizeof(void*)*26 + 5);
v_fixedToolchain_3649_ = lean_ctor_get_uint8(v_cfg_3617_, sizeof(void*)*26 + 6);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_cfg_3617_);
if (v_isSharedCheck_3656_ == 0)
{
lean_object* v_unused_3657_; 
v_unused_3657_ = lean_ctor_get(v_cfg_3617_, 0);
lean_dec(v_unused_3657_);
v___x_3651_ = v_cfg_3617_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3646_);
lean_inc(v_enableArtifactCache_x3f_3645_);
lean_inc(v_readmeFile_3643_);
lean_inc(v_licenseFiles_3642_);
lean_inc(v_license_3641_);
lean_inc(v_homepage_3640_);
lean_inc(v_keywords_3639_);
lean_inc(v_description_3638_);
lean_inc(v_versionTags_3637_);
lean_inc(v_version_3636_);
lean_inc(v_lintDriverArgs_3635_);
lean_inc(v_lintDriver_3634_);
lean_inc(v_testDriverArgs_3633_);
lean_inc(v_testDriver_3632_);
lean_inc(v_buildArchive_3630_);
lean_inc(v_releaseRepo_3629_);
lean_inc(v_irDir_3628_);
lean_inc(v_binDir_3627_);
lean_inc(v_nativeLibDir_3626_);
lean_inc(v_leanLibDir_3625_);
lean_inc(v_buildDir_3624_);
lean_inc(v_srcDir_3623_);
lean_inc(v_moreGlobalServerArgs_3622_);
lean_inc(v_extraDepTargets_3620_);
lean_inc(v_toLeanConfig_3618_);
lean_dec(v_cfg_3617_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v_val_3616_);
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_val_3616_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v_toLeanConfig_3618_);
lean_ctor_set(v_reuseFailAlloc_3655_, 2, v_extraDepTargets_3620_);
lean_ctor_set(v_reuseFailAlloc_3655_, 3, v_moreGlobalServerArgs_3622_);
lean_ctor_set(v_reuseFailAlloc_3655_, 4, v_srcDir_3623_);
lean_ctor_set(v_reuseFailAlloc_3655_, 5, v_buildDir_3624_);
lean_ctor_set(v_reuseFailAlloc_3655_, 6, v_leanLibDir_3625_);
lean_ctor_set(v_reuseFailAlloc_3655_, 7, v_nativeLibDir_3626_);
lean_ctor_set(v_reuseFailAlloc_3655_, 8, v_binDir_3627_);
lean_ctor_set(v_reuseFailAlloc_3655_, 9, v_irDir_3628_);
lean_ctor_set(v_reuseFailAlloc_3655_, 10, v_releaseRepo_3629_);
lean_ctor_set(v_reuseFailAlloc_3655_, 11, v_buildArchive_3630_);
lean_ctor_set(v_reuseFailAlloc_3655_, 12, v_testDriver_3632_);
lean_ctor_set(v_reuseFailAlloc_3655_, 13, v_testDriverArgs_3633_);
lean_ctor_set(v_reuseFailAlloc_3655_, 14, v_lintDriver_3634_);
lean_ctor_set(v_reuseFailAlloc_3655_, 15, v_lintDriverArgs_3635_);
lean_ctor_set(v_reuseFailAlloc_3655_, 16, v_version_3636_);
lean_ctor_set(v_reuseFailAlloc_3655_, 17, v_versionTags_3637_);
lean_ctor_set(v_reuseFailAlloc_3655_, 18, v_description_3638_);
lean_ctor_set(v_reuseFailAlloc_3655_, 19, v_keywords_3639_);
lean_ctor_set(v_reuseFailAlloc_3655_, 20, v_homepage_3640_);
lean_ctor_set(v_reuseFailAlloc_3655_, 21, v_license_3641_);
lean_ctor_set(v_reuseFailAlloc_3655_, 22, v_licenseFiles_3642_);
lean_ctor_set(v_reuseFailAlloc_3655_, 23, v_readmeFile_3643_);
lean_ctor_set(v_reuseFailAlloc_3655_, 24, v_enableArtifactCache_x3f_3645_);
lean_ctor_set(v_reuseFailAlloc_3655_, 25, v_restoreAllArtifacts_x3f_3646_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*26, v_bootstrap_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*26 + 1, v_precompileModules_3621_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3631_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*26 + 3, v_reservoir_3644_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3647_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*26 + 5, v_allowImportAll_3648_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*26 + 6, v_fixedToolchain_3649_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__2(lean_object* v_f_3658_, lean_object* v_cfg_3659_){
_start:
{
lean_object* v_toWorkspaceConfig_3660_; lean_object* v_toLeanConfig_3661_; uint8_t v_bootstrap_3662_; lean_object* v_extraDepTargets_3663_; uint8_t v_precompileModules_3664_; lean_object* v_moreGlobalServerArgs_3665_; lean_object* v_srcDir_3666_; lean_object* v_buildDir_3667_; lean_object* v_leanLibDir_3668_; lean_object* v_nativeLibDir_3669_; lean_object* v_binDir_3670_; lean_object* v_irDir_3671_; lean_object* v_releaseRepo_3672_; lean_object* v_buildArchive_3673_; uint8_t v_preferReleaseBuild_3674_; lean_object* v_testDriver_3675_; lean_object* v_testDriverArgs_3676_; lean_object* v_lintDriver_3677_; lean_object* v_lintDriverArgs_3678_; lean_object* v_version_3679_; lean_object* v_versionTags_3680_; lean_object* v_description_3681_; lean_object* v_keywords_3682_; lean_object* v_homepage_3683_; lean_object* v_license_3684_; lean_object* v_licenseFiles_3685_; lean_object* v_readmeFile_3686_; uint8_t v_reservoir_3687_; lean_object* v_enableArtifactCache_x3f_3688_; lean_object* v_restoreAllArtifacts_x3f_3689_; uint8_t v_libPrefixOnWindows_3690_; uint8_t v_allowImportAll_3691_; uint8_t v_fixedToolchain_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3700_; 
v_toWorkspaceConfig_3660_ = lean_ctor_get(v_cfg_3659_, 0);
v_toLeanConfig_3661_ = lean_ctor_get(v_cfg_3659_, 1);
v_bootstrap_3662_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*26);
v_extraDepTargets_3663_ = lean_ctor_get(v_cfg_3659_, 2);
v_precompileModules_3664_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3665_ = lean_ctor_get(v_cfg_3659_, 3);
v_srcDir_3666_ = lean_ctor_get(v_cfg_3659_, 4);
v_buildDir_3667_ = lean_ctor_get(v_cfg_3659_, 5);
v_leanLibDir_3668_ = lean_ctor_get(v_cfg_3659_, 6);
v_nativeLibDir_3669_ = lean_ctor_get(v_cfg_3659_, 7);
v_binDir_3670_ = lean_ctor_get(v_cfg_3659_, 8);
v_irDir_3671_ = lean_ctor_get(v_cfg_3659_, 9);
v_releaseRepo_3672_ = lean_ctor_get(v_cfg_3659_, 10);
v_buildArchive_3673_ = lean_ctor_get(v_cfg_3659_, 11);
v_preferReleaseBuild_3674_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*26 + 2);
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
v_reservoir_3687_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3688_ = lean_ctor_get(v_cfg_3659_, 24);
v_restoreAllArtifacts_x3f_3689_ = lean_ctor_get(v_cfg_3659_, 25);
v_libPrefixOnWindows_3690_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*26 + 4);
v_allowImportAll_3691_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*26 + 5);
v_fixedToolchain_3692_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*26 + 6);
v_isSharedCheck_3700_ = !lean_is_exclusive(v_cfg_3659_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3694_ = v_cfg_3659_;
v_isShared_3695_ = v_isSharedCheck_3700_;
goto v_resetjp_3693_;
}
else
{
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
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3700_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3696_ = lean_apply_1(v_f_3658_, v_toWorkspaceConfig_3660_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3696_);
v___x_3698_ = v___x_3694_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_toLeanConfig_3661_);
lean_ctor_set(v_reuseFailAlloc_3699_, 2, v_extraDepTargets_3663_);
lean_ctor_set(v_reuseFailAlloc_3699_, 3, v_moreGlobalServerArgs_3665_);
lean_ctor_set(v_reuseFailAlloc_3699_, 4, v_srcDir_3666_);
lean_ctor_set(v_reuseFailAlloc_3699_, 5, v_buildDir_3667_);
lean_ctor_set(v_reuseFailAlloc_3699_, 6, v_leanLibDir_3668_);
lean_ctor_set(v_reuseFailAlloc_3699_, 7, v_nativeLibDir_3669_);
lean_ctor_set(v_reuseFailAlloc_3699_, 8, v_binDir_3670_);
lean_ctor_set(v_reuseFailAlloc_3699_, 9, v_irDir_3671_);
lean_ctor_set(v_reuseFailAlloc_3699_, 10, v_releaseRepo_3672_);
lean_ctor_set(v_reuseFailAlloc_3699_, 11, v_buildArchive_3673_);
lean_ctor_set(v_reuseFailAlloc_3699_, 12, v_testDriver_3675_);
lean_ctor_set(v_reuseFailAlloc_3699_, 13, v_testDriverArgs_3676_);
lean_ctor_set(v_reuseFailAlloc_3699_, 14, v_lintDriver_3677_);
lean_ctor_set(v_reuseFailAlloc_3699_, 15, v_lintDriverArgs_3678_);
lean_ctor_set(v_reuseFailAlloc_3699_, 16, v_version_3679_);
lean_ctor_set(v_reuseFailAlloc_3699_, 17, v_versionTags_3680_);
lean_ctor_set(v_reuseFailAlloc_3699_, 18, v_description_3681_);
lean_ctor_set(v_reuseFailAlloc_3699_, 19, v_keywords_3682_);
lean_ctor_set(v_reuseFailAlloc_3699_, 20, v_homepage_3683_);
lean_ctor_set(v_reuseFailAlloc_3699_, 21, v_license_3684_);
lean_ctor_set(v_reuseFailAlloc_3699_, 22, v_licenseFiles_3685_);
lean_ctor_set(v_reuseFailAlloc_3699_, 23, v_readmeFile_3686_);
lean_ctor_set(v_reuseFailAlloc_3699_, 24, v_enableArtifactCache_x3f_3688_);
lean_ctor_set(v_reuseFailAlloc_3699_, 25, v_restoreAllArtifacts_x3f_3689_);
lean_ctor_set_uint8(v_reuseFailAlloc_3699_, sizeof(void*)*26, v_bootstrap_3662_);
lean_ctor_set_uint8(v_reuseFailAlloc_3699_, sizeof(void*)*26 + 1, v_precompileModules_3664_);
lean_ctor_set_uint8(v_reuseFailAlloc_3699_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3674_);
lean_ctor_set_uint8(v_reuseFailAlloc_3699_, sizeof(void*)*26 + 3, v_reservoir_3687_);
lean_ctor_set_uint8(v_reuseFailAlloc_3699_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3690_);
lean_ctor_set_uint8(v_reuseFailAlloc_3699_, sizeof(void*)*26 + 5, v_allowImportAll_3691_);
lean_ctor_set_uint8(v_reuseFailAlloc_3699_, sizeof(void*)*26 + 6, v_fixedToolchain_3692_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(lean_object* v_x_3701_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Lake_defaultPackagesDir;
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3___boxed(lean_object* v_x_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(v_x_3703_);
lean_dec_ref(v_x_3703_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object* v_p_3714_, lean_object* v_n_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = ((lean_object*)(l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__4));
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object* v_p_3717_, lean_object* v_n_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_3717_, v_n_3718_);
lean_dec(v_n_3718_);
lean_dec(v_p_3717_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object* v_p_3720_, lean_object* v_n_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_3720_, v_n_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object* v_p_3723_, lean_object* v_n_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(v_p_3723_, v_n_3724_);
lean_dec(v_n_3724_);
lean_dec(v_p_3723_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0(lean_object* v_cfg_3726_){
_start:
{
lean_object* v_toLeanConfig_3727_; 
v_toLeanConfig_3727_ = lean_ctor_get(v_cfg_3726_, 1);
lean_inc_ref(v_toLeanConfig_3727_);
return v_toLeanConfig_3727_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0___boxed(lean_object* v_cfg_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Lake_PackageConfig_toLeanConfig___proj___lam__0(v_cfg_3728_);
lean_dec_ref(v_cfg_3728_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__1(lean_object* v_val_3730_, lean_object* v_cfg_3731_){
_start:
{
lean_object* v_toWorkspaceConfig_3732_; uint8_t v_bootstrap_3733_; lean_object* v_extraDepTargets_3734_; uint8_t v_precompileModules_3735_; lean_object* v_moreGlobalServerArgs_3736_; lean_object* v_srcDir_3737_; lean_object* v_buildDir_3738_; lean_object* v_leanLibDir_3739_; lean_object* v_nativeLibDir_3740_; lean_object* v_binDir_3741_; lean_object* v_irDir_3742_; lean_object* v_releaseRepo_3743_; lean_object* v_buildArchive_3744_; uint8_t v_preferReleaseBuild_3745_; lean_object* v_testDriver_3746_; lean_object* v_testDriverArgs_3747_; lean_object* v_lintDriver_3748_; lean_object* v_lintDriverArgs_3749_; lean_object* v_version_3750_; lean_object* v_versionTags_3751_; lean_object* v_description_3752_; lean_object* v_keywords_3753_; lean_object* v_homepage_3754_; lean_object* v_license_3755_; lean_object* v_licenseFiles_3756_; lean_object* v_readmeFile_3757_; uint8_t v_reservoir_3758_; lean_object* v_enableArtifactCache_x3f_3759_; lean_object* v_restoreAllArtifacts_x3f_3760_; uint8_t v_libPrefixOnWindows_3761_; uint8_t v_allowImportAll_3762_; uint8_t v_fixedToolchain_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
v_toWorkspaceConfig_3732_ = lean_ctor_get(v_cfg_3731_, 0);
v_bootstrap_3733_ = lean_ctor_get_uint8(v_cfg_3731_, sizeof(void*)*26);
v_extraDepTargets_3734_ = lean_ctor_get(v_cfg_3731_, 2);
v_precompileModules_3735_ = lean_ctor_get_uint8(v_cfg_3731_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3736_ = lean_ctor_get(v_cfg_3731_, 3);
v_srcDir_3737_ = lean_ctor_get(v_cfg_3731_, 4);
v_buildDir_3738_ = lean_ctor_get(v_cfg_3731_, 5);
v_leanLibDir_3739_ = lean_ctor_get(v_cfg_3731_, 6);
v_nativeLibDir_3740_ = lean_ctor_get(v_cfg_3731_, 7);
v_binDir_3741_ = lean_ctor_get(v_cfg_3731_, 8);
v_irDir_3742_ = lean_ctor_get(v_cfg_3731_, 9);
v_releaseRepo_3743_ = lean_ctor_get(v_cfg_3731_, 10);
v_buildArchive_3744_ = lean_ctor_get(v_cfg_3731_, 11);
v_preferReleaseBuild_3745_ = lean_ctor_get_uint8(v_cfg_3731_, sizeof(void*)*26 + 2);
v_testDriver_3746_ = lean_ctor_get(v_cfg_3731_, 12);
v_testDriverArgs_3747_ = lean_ctor_get(v_cfg_3731_, 13);
v_lintDriver_3748_ = lean_ctor_get(v_cfg_3731_, 14);
v_lintDriverArgs_3749_ = lean_ctor_get(v_cfg_3731_, 15);
v_version_3750_ = lean_ctor_get(v_cfg_3731_, 16);
v_versionTags_3751_ = lean_ctor_get(v_cfg_3731_, 17);
v_description_3752_ = lean_ctor_get(v_cfg_3731_, 18);
v_keywords_3753_ = lean_ctor_get(v_cfg_3731_, 19);
v_homepage_3754_ = lean_ctor_get(v_cfg_3731_, 20);
v_license_3755_ = lean_ctor_get(v_cfg_3731_, 21);
v_licenseFiles_3756_ = lean_ctor_get(v_cfg_3731_, 22);
v_readmeFile_3757_ = lean_ctor_get(v_cfg_3731_, 23);
v_reservoir_3758_ = lean_ctor_get_uint8(v_cfg_3731_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3759_ = lean_ctor_get(v_cfg_3731_, 24);
v_restoreAllArtifacts_x3f_3760_ = lean_ctor_get(v_cfg_3731_, 25);
v_libPrefixOnWindows_3761_ = lean_ctor_get_uint8(v_cfg_3731_, sizeof(void*)*26 + 4);
v_allowImportAll_3762_ = lean_ctor_get_uint8(v_cfg_3731_, sizeof(void*)*26 + 5);
v_fixedToolchain_3763_ = lean_ctor_get_uint8(v_cfg_3731_, sizeof(void*)*26 + 6);
v_isSharedCheck_3770_ = !lean_is_exclusive(v_cfg_3731_);
if (v_isSharedCheck_3770_ == 0)
{
lean_object* v_unused_3771_; 
v_unused_3771_ = lean_ctor_get(v_cfg_3731_, 1);
lean_dec(v_unused_3771_);
v___x_3765_ = v_cfg_3731_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3760_);
lean_inc(v_enableArtifactCache_x3f_3759_);
lean_inc(v_readmeFile_3757_);
lean_inc(v_licenseFiles_3756_);
lean_inc(v_license_3755_);
lean_inc(v_homepage_3754_);
lean_inc(v_keywords_3753_);
lean_inc(v_description_3752_);
lean_inc(v_versionTags_3751_);
lean_inc(v_version_3750_);
lean_inc(v_lintDriverArgs_3749_);
lean_inc(v_lintDriver_3748_);
lean_inc(v_testDriverArgs_3747_);
lean_inc(v_testDriver_3746_);
lean_inc(v_buildArchive_3744_);
lean_inc(v_releaseRepo_3743_);
lean_inc(v_irDir_3742_);
lean_inc(v_binDir_3741_);
lean_inc(v_nativeLibDir_3740_);
lean_inc(v_leanLibDir_3739_);
lean_inc(v_buildDir_3738_);
lean_inc(v_srcDir_3737_);
lean_inc(v_moreGlobalServerArgs_3736_);
lean_inc(v_extraDepTargets_3734_);
lean_inc(v_toWorkspaceConfig_3732_);
lean_dec(v_cfg_3731_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 1, v_val_3730_);
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_toWorkspaceConfig_3732_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v_val_3730_);
lean_ctor_set(v_reuseFailAlloc_3769_, 2, v_extraDepTargets_3734_);
lean_ctor_set(v_reuseFailAlloc_3769_, 3, v_moreGlobalServerArgs_3736_);
lean_ctor_set(v_reuseFailAlloc_3769_, 4, v_srcDir_3737_);
lean_ctor_set(v_reuseFailAlloc_3769_, 5, v_buildDir_3738_);
lean_ctor_set(v_reuseFailAlloc_3769_, 6, v_leanLibDir_3739_);
lean_ctor_set(v_reuseFailAlloc_3769_, 7, v_nativeLibDir_3740_);
lean_ctor_set(v_reuseFailAlloc_3769_, 8, v_binDir_3741_);
lean_ctor_set(v_reuseFailAlloc_3769_, 9, v_irDir_3742_);
lean_ctor_set(v_reuseFailAlloc_3769_, 10, v_releaseRepo_3743_);
lean_ctor_set(v_reuseFailAlloc_3769_, 11, v_buildArchive_3744_);
lean_ctor_set(v_reuseFailAlloc_3769_, 12, v_testDriver_3746_);
lean_ctor_set(v_reuseFailAlloc_3769_, 13, v_testDriverArgs_3747_);
lean_ctor_set(v_reuseFailAlloc_3769_, 14, v_lintDriver_3748_);
lean_ctor_set(v_reuseFailAlloc_3769_, 15, v_lintDriverArgs_3749_);
lean_ctor_set(v_reuseFailAlloc_3769_, 16, v_version_3750_);
lean_ctor_set(v_reuseFailAlloc_3769_, 17, v_versionTags_3751_);
lean_ctor_set(v_reuseFailAlloc_3769_, 18, v_description_3752_);
lean_ctor_set(v_reuseFailAlloc_3769_, 19, v_keywords_3753_);
lean_ctor_set(v_reuseFailAlloc_3769_, 20, v_homepage_3754_);
lean_ctor_set(v_reuseFailAlloc_3769_, 21, v_license_3755_);
lean_ctor_set(v_reuseFailAlloc_3769_, 22, v_licenseFiles_3756_);
lean_ctor_set(v_reuseFailAlloc_3769_, 23, v_readmeFile_3757_);
lean_ctor_set(v_reuseFailAlloc_3769_, 24, v_enableArtifactCache_x3f_3759_);
lean_ctor_set(v_reuseFailAlloc_3769_, 25, v_restoreAllArtifacts_x3f_3760_);
lean_ctor_set_uint8(v_reuseFailAlloc_3769_, sizeof(void*)*26, v_bootstrap_3733_);
lean_ctor_set_uint8(v_reuseFailAlloc_3769_, sizeof(void*)*26 + 1, v_precompileModules_3735_);
lean_ctor_set_uint8(v_reuseFailAlloc_3769_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3745_);
lean_ctor_set_uint8(v_reuseFailAlloc_3769_, sizeof(void*)*26 + 3, v_reservoir_3758_);
lean_ctor_set_uint8(v_reuseFailAlloc_3769_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3761_);
lean_ctor_set_uint8(v_reuseFailAlloc_3769_, sizeof(void*)*26 + 5, v_allowImportAll_3762_);
lean_ctor_set_uint8(v_reuseFailAlloc_3769_, sizeof(void*)*26 + 6, v_fixedToolchain_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__2(lean_object* v_f_3772_, lean_object* v_cfg_3773_){
_start:
{
lean_object* v_toWorkspaceConfig_3774_; lean_object* v_toLeanConfig_3775_; uint8_t v_bootstrap_3776_; lean_object* v_extraDepTargets_3777_; uint8_t v_precompileModules_3778_; lean_object* v_moreGlobalServerArgs_3779_; lean_object* v_srcDir_3780_; lean_object* v_buildDir_3781_; lean_object* v_leanLibDir_3782_; lean_object* v_nativeLibDir_3783_; lean_object* v_binDir_3784_; lean_object* v_irDir_3785_; lean_object* v_releaseRepo_3786_; lean_object* v_buildArchive_3787_; uint8_t v_preferReleaseBuild_3788_; lean_object* v_testDriver_3789_; lean_object* v_testDriverArgs_3790_; lean_object* v_lintDriver_3791_; lean_object* v_lintDriverArgs_3792_; lean_object* v_version_3793_; lean_object* v_versionTags_3794_; lean_object* v_description_3795_; lean_object* v_keywords_3796_; lean_object* v_homepage_3797_; lean_object* v_license_3798_; lean_object* v_licenseFiles_3799_; lean_object* v_readmeFile_3800_; uint8_t v_reservoir_3801_; lean_object* v_enableArtifactCache_x3f_3802_; lean_object* v_restoreAllArtifacts_x3f_3803_; uint8_t v_libPrefixOnWindows_3804_; uint8_t v_allowImportAll_3805_; uint8_t v_fixedToolchain_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3814_; 
v_toWorkspaceConfig_3774_ = lean_ctor_get(v_cfg_3773_, 0);
v_toLeanConfig_3775_ = lean_ctor_get(v_cfg_3773_, 1);
v_bootstrap_3776_ = lean_ctor_get_uint8(v_cfg_3773_, sizeof(void*)*26);
v_extraDepTargets_3777_ = lean_ctor_get(v_cfg_3773_, 2);
v_precompileModules_3778_ = lean_ctor_get_uint8(v_cfg_3773_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3779_ = lean_ctor_get(v_cfg_3773_, 3);
v_srcDir_3780_ = lean_ctor_get(v_cfg_3773_, 4);
v_buildDir_3781_ = lean_ctor_get(v_cfg_3773_, 5);
v_leanLibDir_3782_ = lean_ctor_get(v_cfg_3773_, 6);
v_nativeLibDir_3783_ = lean_ctor_get(v_cfg_3773_, 7);
v_binDir_3784_ = lean_ctor_get(v_cfg_3773_, 8);
v_irDir_3785_ = lean_ctor_get(v_cfg_3773_, 9);
v_releaseRepo_3786_ = lean_ctor_get(v_cfg_3773_, 10);
v_buildArchive_3787_ = lean_ctor_get(v_cfg_3773_, 11);
v_preferReleaseBuild_3788_ = lean_ctor_get_uint8(v_cfg_3773_, sizeof(void*)*26 + 2);
v_testDriver_3789_ = lean_ctor_get(v_cfg_3773_, 12);
v_testDriverArgs_3790_ = lean_ctor_get(v_cfg_3773_, 13);
v_lintDriver_3791_ = lean_ctor_get(v_cfg_3773_, 14);
v_lintDriverArgs_3792_ = lean_ctor_get(v_cfg_3773_, 15);
v_version_3793_ = lean_ctor_get(v_cfg_3773_, 16);
v_versionTags_3794_ = lean_ctor_get(v_cfg_3773_, 17);
v_description_3795_ = lean_ctor_get(v_cfg_3773_, 18);
v_keywords_3796_ = lean_ctor_get(v_cfg_3773_, 19);
v_homepage_3797_ = lean_ctor_get(v_cfg_3773_, 20);
v_license_3798_ = lean_ctor_get(v_cfg_3773_, 21);
v_licenseFiles_3799_ = lean_ctor_get(v_cfg_3773_, 22);
v_readmeFile_3800_ = lean_ctor_get(v_cfg_3773_, 23);
v_reservoir_3801_ = lean_ctor_get_uint8(v_cfg_3773_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3802_ = lean_ctor_get(v_cfg_3773_, 24);
v_restoreAllArtifacts_x3f_3803_ = lean_ctor_get(v_cfg_3773_, 25);
v_libPrefixOnWindows_3804_ = lean_ctor_get_uint8(v_cfg_3773_, sizeof(void*)*26 + 4);
v_allowImportAll_3805_ = lean_ctor_get_uint8(v_cfg_3773_, sizeof(void*)*26 + 5);
v_fixedToolchain_3806_ = lean_ctor_get_uint8(v_cfg_3773_, sizeof(void*)*26 + 6);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_cfg_3773_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3808_ = v_cfg_3773_;
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3803_);
lean_inc(v_enableArtifactCache_x3f_3802_);
lean_inc(v_readmeFile_3800_);
lean_inc(v_licenseFiles_3799_);
lean_inc(v_license_3798_);
lean_inc(v_homepage_3797_);
lean_inc(v_keywords_3796_);
lean_inc(v_description_3795_);
lean_inc(v_versionTags_3794_);
lean_inc(v_version_3793_);
lean_inc(v_lintDriverArgs_3792_);
lean_inc(v_lintDriver_3791_);
lean_inc(v_testDriverArgs_3790_);
lean_inc(v_testDriver_3789_);
lean_inc(v_buildArchive_3787_);
lean_inc(v_releaseRepo_3786_);
lean_inc(v_irDir_3785_);
lean_inc(v_binDir_3784_);
lean_inc(v_nativeLibDir_3783_);
lean_inc(v_leanLibDir_3782_);
lean_inc(v_buildDir_3781_);
lean_inc(v_srcDir_3780_);
lean_inc(v_moreGlobalServerArgs_3779_);
lean_inc(v_extraDepTargets_3777_);
lean_inc(v_toLeanConfig_3775_);
lean_inc(v_toWorkspaceConfig_3774_);
lean_dec(v_cfg_3773_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3810_ = lean_apply_1(v_f_3772_, v_toLeanConfig_3775_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 1, v___x_3810_);
v___x_3812_ = v___x_3808_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_toWorkspaceConfig_3774_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v___x_3810_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_extraDepTargets_3777_);
lean_ctor_set(v_reuseFailAlloc_3813_, 3, v_moreGlobalServerArgs_3779_);
lean_ctor_set(v_reuseFailAlloc_3813_, 4, v_srcDir_3780_);
lean_ctor_set(v_reuseFailAlloc_3813_, 5, v_buildDir_3781_);
lean_ctor_set(v_reuseFailAlloc_3813_, 6, v_leanLibDir_3782_);
lean_ctor_set(v_reuseFailAlloc_3813_, 7, v_nativeLibDir_3783_);
lean_ctor_set(v_reuseFailAlloc_3813_, 8, v_binDir_3784_);
lean_ctor_set(v_reuseFailAlloc_3813_, 9, v_irDir_3785_);
lean_ctor_set(v_reuseFailAlloc_3813_, 10, v_releaseRepo_3786_);
lean_ctor_set(v_reuseFailAlloc_3813_, 11, v_buildArchive_3787_);
lean_ctor_set(v_reuseFailAlloc_3813_, 12, v_testDriver_3789_);
lean_ctor_set(v_reuseFailAlloc_3813_, 13, v_testDriverArgs_3790_);
lean_ctor_set(v_reuseFailAlloc_3813_, 14, v_lintDriver_3791_);
lean_ctor_set(v_reuseFailAlloc_3813_, 15, v_lintDriverArgs_3792_);
lean_ctor_set(v_reuseFailAlloc_3813_, 16, v_version_3793_);
lean_ctor_set(v_reuseFailAlloc_3813_, 17, v_versionTags_3794_);
lean_ctor_set(v_reuseFailAlloc_3813_, 18, v_description_3795_);
lean_ctor_set(v_reuseFailAlloc_3813_, 19, v_keywords_3796_);
lean_ctor_set(v_reuseFailAlloc_3813_, 20, v_homepage_3797_);
lean_ctor_set(v_reuseFailAlloc_3813_, 21, v_license_3798_);
lean_ctor_set(v_reuseFailAlloc_3813_, 22, v_licenseFiles_3799_);
lean_ctor_set(v_reuseFailAlloc_3813_, 23, v_readmeFile_3800_);
lean_ctor_set(v_reuseFailAlloc_3813_, 24, v_enableArtifactCache_x3f_3802_);
lean_ctor_set(v_reuseFailAlloc_3813_, 25, v_restoreAllArtifacts_x3f_3803_);
lean_ctor_set_uint8(v_reuseFailAlloc_3813_, sizeof(void*)*26, v_bootstrap_3776_);
lean_ctor_set_uint8(v_reuseFailAlloc_3813_, sizeof(void*)*26 + 1, v_precompileModules_3778_);
lean_ctor_set_uint8(v_reuseFailAlloc_3813_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3788_);
lean_ctor_set_uint8(v_reuseFailAlloc_3813_, sizeof(void*)*26 + 3, v_reservoir_3801_);
lean_ctor_set_uint8(v_reuseFailAlloc_3813_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3804_);
lean_ctor_set_uint8(v_reuseFailAlloc_3813_, sizeof(void*)*26 + 5, v_allowImportAll_3805_);
lean_ctor_set_uint8(v_reuseFailAlloc_3813_, sizeof(void*)*26 + 6, v_fixedToolchain_3806_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3(lean_object* v_x_3815_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection(lean_object* v_p_4295_, lean_object* v_n_4296_){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4297_ = lean_unsigned_to_nat(1u);
v___x_4298_ = lean_mk_empty_array_with_capacity(v___x_4297_);
lean_dec_ref(v___x_4298_);
v___x_4299_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___closed__9, &l_Lake_instInhabitedPackageConfig_default___closed__9_once, _init_l_Lake_instInhabitedPackageConfig_default___closed__9);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___boxed(lean_object* v_p_4300_, lean_object* v_n_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Lake_PackageConfig_instEmptyCollection(v_p_4300_, v_n_4301_);
lean_dec(v_n_4301_);
lean_dec(v_p_4300_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg(lean_object* v_n_4303_){
_start:
{
lean_inc(v_n_4303_);
return v_n_4303_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg___boxed(lean_object* v_n_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Lake_PackageConfig_origName___redArg(v_n_4304_);
lean_dec(v_n_4304_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName(lean_object* v_p_4306_, lean_object* v_n_4307_, lean_object* v_x_4308_){
_start:
{
lean_inc(v_n_4307_);
return v_n_4307_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___boxed(lean_object* v_p_4309_, lean_object* v_n_4310_, lean_object* v_x_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_Lake_PackageConfig_origName(v_p_4309_, v_n_4310_, v_x_4311_);
lean_dec_ref(v_x_4311_);
lean_dec(v_n_4310_);
lean_dec(v_p_4309_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name(lean_object* v_self_4320_){
_start:
{
lean_object* v_keyName_4321_; 
v_keyName_4321_ = lean_ctor_get(v_self_4320_, 1);
lean_inc(v_keyName_4321_);
return v_keyName_4321_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name___boxed(lean_object* v_self_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l_Lake_PackageDecl_name(v_self_4322_);
lean_dec_ref(v_self_4322_);
return v_res_4323_;
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
