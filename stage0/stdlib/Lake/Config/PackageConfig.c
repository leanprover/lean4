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
static const lean_string_object l_Lake_defaultBuildArchive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_defaultBuildArchive___closed__0 = (const lean_object*)&l_Lake_defaultBuildArchive___closed__0_value;
static const lean_string_object l_Lake_defaultBuildArchive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".tar.gz"};
static const lean_object* l_Lake_defaultBuildArchive___closed__1 = (const lean_object*)&l_Lake_defaultBuildArchive___closed__1_value;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
LEAN_EXPORT lean_object* l_Lake_defaultBuildArchive(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_instInhabitedPackageConfig_default___closed__0;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__1_value;
lean_object* l_Lake_instInhabitedPattern_default__1(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedPackageConfig_default___closed__2;
extern lean_object* l_Lake_instInhabitedStdVer_default;
extern lean_object* l_System_instInhabitedFilePath_default;
extern lean_object* l_Lake_instInhabitedLeanConfig_default;
extern lean_object* l_Lake_instInhabitedWorkspaceConfig_default;
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0;
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
static lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0;
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
extern lean_object* l_Lake_defaultBuildDir;
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
extern lean_object* l_Lake_defaultLeanLibDir;
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
extern lean_object* l_Lake_defaultNativeLibDir;
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
extern lean_object* l_Lake_defaultBinDir;
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
extern lean_object* l_Lake_defaultIrDir;
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
extern lean_object* l_Lake_defaultVersionTags;
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
static lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__2;
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
LEAN_EXPORT uint8_t l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___boxed(lean_object*, lean_object*);
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
extern lean_object* l_Lake_defaultPackagesDir;
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
static lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0;
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
static lean_object* l_Lake_PackageConfig___fields___closed__0;
static const lean_string_object l_Lake_PackageConfig___fields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bootstrap"};
static const lean_object* l_Lake_PackageConfig___fields___closed__1 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 243, 17, 14, 190, 232, 38, 153)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__2 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__2_value;
static lean_object* l_Lake_PackageConfig___fields___closed__3;
static lean_object* l_Lake_PackageConfig___fields___closed__4;
static const lean_string_object l_Lake_PackageConfig___fields___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "manifestFile"};
static const lean_object* l_Lake_PackageConfig___fields___closed__5 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__5_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__5_value),LEAN_SCALAR_PTR_LITERAL(119, 77, 202, 12, 106, 133, 208, 66)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__6 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__6_value;
static lean_object* l_Lake_PackageConfig___fields___closed__7;
static lean_object* l_Lake_PackageConfig___fields___closed__8;
static const lean_string_object l_Lake_PackageConfig___fields___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "extraDepTargets"};
static const lean_object* l_Lake_PackageConfig___fields___closed__9 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__9_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__9_value),LEAN_SCALAR_PTR_LITERAL(232, 29, 68, 154, 160, 50, 56, 5)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__10 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__10_value;
static lean_object* l_Lake_PackageConfig___fields___closed__11;
static lean_object* l_Lake_PackageConfig___fields___closed__12;
static const lean_string_object l_Lake_PackageConfig___fields___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precompileModules"};
static const lean_object* l_Lake_PackageConfig___fields___closed__13 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__13_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__13_value),LEAN_SCALAR_PTR_LITERAL(210, 72, 98, 56, 225, 29, 247, 45)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__14 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__14_value;
static lean_object* l_Lake_PackageConfig___fields___closed__15;
static lean_object* l_Lake_PackageConfig___fields___closed__16;
static const lean_string_object l_Lake_PackageConfig___fields___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "moreGlobalServerArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__17 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__17_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__17_value),LEAN_SCALAR_PTR_LITERAL(217, 219, 52, 240, 88, 87, 45, 147)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__18 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__18_value;
static lean_object* l_Lake_PackageConfig___fields___closed__19;
static lean_object* l_Lake_PackageConfig___fields___closed__20;
static const lean_string_object l_Lake_PackageConfig___fields___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "moreServerArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__21 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__21_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 197, 113, 7, 119, 120, 175, 89)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__22 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__22_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__22_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__18_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__23 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__23_value;
static lean_object* l_Lake_PackageConfig___fields___closed__24;
static const lean_string_object l_Lake_PackageConfig___fields___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "srcDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__25 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__25_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__25_value),LEAN_SCALAR_PTR_LITERAL(82, 241, 97, 48, 55, 77, 36, 145)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__26 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__26_value;
static lean_object* l_Lake_PackageConfig___fields___closed__27;
static lean_object* l_Lake_PackageConfig___fields___closed__28;
static const lean_string_object l_Lake_PackageConfig___fields___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "buildDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__29 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__29_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__29_value),LEAN_SCALAR_PTR_LITERAL(249, 192, 208, 78, 51, 18, 78, 228)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__30 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__30_value;
static lean_object* l_Lake_PackageConfig___fields___closed__31;
static lean_object* l_Lake_PackageConfig___fields___closed__32;
static const lean_string_object l_Lake_PackageConfig___fields___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanLibDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__33 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__33_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__33_value),LEAN_SCALAR_PTR_LITERAL(1, 89, 218, 214, 52, 197, 188, 252)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__34 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__34_value;
static lean_object* l_Lake_PackageConfig___fields___closed__35;
static lean_object* l_Lake_PackageConfig___fields___closed__36;
static const lean_string_object l_Lake_PackageConfig___fields___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nativeLibDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__37 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__37_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__37_value),LEAN_SCALAR_PTR_LITERAL(82, 8, 215, 104, 60, 212, 87, 97)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__38 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__38_value;
static lean_object* l_Lake_PackageConfig___fields___closed__39;
static lean_object* l_Lake_PackageConfig___fields___closed__40;
static const lean_string_object l_Lake_PackageConfig___fields___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__41 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__41_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__41_value),LEAN_SCALAR_PTR_LITERAL(76, 64, 142, 71, 135, 199, 112, 75)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__42 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__42_value;
static lean_object* l_Lake_PackageConfig___fields___closed__43;
static lean_object* l_Lake_PackageConfig___fields___closed__44;
static const lean_string_object l_Lake_PackageConfig___fields___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "irDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__45 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__45_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__45_value),LEAN_SCALAR_PTR_LITERAL(103, 157, 139, 154, 172, 117, 115, 135)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__46 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__46_value;
static lean_object* l_Lake_PackageConfig___fields___closed__47;
static lean_object* l_Lake_PackageConfig___fields___closed__48;
static const lean_string_object l_Lake_PackageConfig___fields___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "releaseRepo"};
static const lean_object* l_Lake_PackageConfig___fields___closed__49 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__49_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__49_value),LEAN_SCALAR_PTR_LITERAL(200, 115, 184, 27, 119, 80, 150, 143)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__50 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__50_value;
static lean_object* l_Lake_PackageConfig___fields___closed__51;
static lean_object* l_Lake_PackageConfig___fields___closed__52;
static const lean_string_object l_Lake_PackageConfig___fields___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "releaseRepo\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__53 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__53_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__53_value),LEAN_SCALAR_PTR_LITERAL(110, 119, 158, 92, 2, 186, 119, 253)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__54 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__54_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__54_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__50_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__55 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__55_value;
static lean_object* l_Lake_PackageConfig___fields___closed__56;
static const lean_string_object l_Lake_PackageConfig___fields___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "buildArchive"};
static const lean_object* l_Lake_PackageConfig___fields___closed__57 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__57_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__57_value),LEAN_SCALAR_PTR_LITERAL(13, 161, 176, 165, 88, 62, 216, 20)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__58 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__58_value;
static lean_object* l_Lake_PackageConfig___fields___closed__59;
static lean_object* l_Lake_PackageConfig___fields___closed__60;
static const lean_string_object l_Lake_PackageConfig___fields___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "buildArchive\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__61 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__61_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__61_value),LEAN_SCALAR_PTR_LITERAL(206, 154, 251, 129, 245, 231, 210, 109)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__62 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__62_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__62_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__58_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__63 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__63_value;
static lean_object* l_Lake_PackageConfig___fields___closed__64;
static const lean_string_object l_Lake_PackageConfig___fields___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "preferReleaseBuild"};
static const lean_object* l_Lake_PackageConfig___fields___closed__65 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__65_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__65_value),LEAN_SCALAR_PTR_LITERAL(75, 209, 233, 233, 163, 174, 95, 235)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__66 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__66_value;
static lean_object* l_Lake_PackageConfig___fields___closed__67;
static lean_object* l_Lake_PackageConfig___fields___closed__68;
static const lean_string_object l_Lake_PackageConfig___fields___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "testDriver"};
static const lean_object* l_Lake_PackageConfig___fields___closed__69 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__69_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__69_value),LEAN_SCALAR_PTR_LITERAL(187, 40, 173, 233, 223, 78, 220, 191)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__70 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__70_value;
static lean_object* l_Lake_PackageConfig___fields___closed__71;
static lean_object* l_Lake_PackageConfig___fields___closed__72;
static const lean_string_object l_Lake_PackageConfig___fields___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "testRunner"};
static const lean_object* l_Lake_PackageConfig___fields___closed__73 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__73_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__73_value),LEAN_SCALAR_PTR_LITERAL(58, 61, 59, 86, 150, 111, 127, 182)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__74 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__74_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__74_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__70_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__75 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__75_value;
static lean_object* l_Lake_PackageConfig___fields___closed__76;
static const lean_string_object l_Lake_PackageConfig___fields___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "testDriverArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__77 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__77_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__77_value),LEAN_SCALAR_PTR_LITERAL(40, 188, 168, 214, 71, 6, 72, 93)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__78 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__78_value;
static lean_object* l_Lake_PackageConfig___fields___closed__79;
static lean_object* l_Lake_PackageConfig___fields___closed__80;
static const lean_string_object l_Lake_PackageConfig___fields___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lintDriver"};
static const lean_object* l_Lake_PackageConfig___fields___closed__81 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__81_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__81_value),LEAN_SCALAR_PTR_LITERAL(164, 80, 113, 139, 118, 238, 67, 240)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__82 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__82_value;
static lean_object* l_Lake_PackageConfig___fields___closed__83;
static lean_object* l_Lake_PackageConfig___fields___closed__84;
static const lean_string_object l_Lake_PackageConfig___fields___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lintDriverArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__85 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__85_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__85_value),LEAN_SCALAR_PTR_LITERAL(102, 206, 227, 73, 236, 117, 156, 150)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__86 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__86_value;
static lean_object* l_Lake_PackageConfig___fields___closed__87;
static lean_object* l_Lake_PackageConfig___fields___closed__88;
static const lean_string_object l_Lake_PackageConfig___fields___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lake_PackageConfig___fields___closed__89 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__89_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__89_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 50, 73, 160, 48, 142, 108)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__90 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__90_value;
static lean_object* l_Lake_PackageConfig___fields___closed__91;
static lean_object* l_Lake_PackageConfig___fields___closed__92;
static const lean_string_object l_Lake_PackageConfig___fields___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "versionTags"};
static const lean_object* l_Lake_PackageConfig___fields___closed__93 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__93_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__93_value),LEAN_SCALAR_PTR_LITERAL(76, 44, 235, 102, 59, 70, 79, 98)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__94 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__94_value;
static lean_object* l_Lake_PackageConfig___fields___closed__95;
static lean_object* l_Lake_PackageConfig___fields___closed__96;
static const lean_string_object l_Lake_PackageConfig___fields___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "description"};
static const lean_object* l_Lake_PackageConfig___fields___closed__97 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__97_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__97_value),LEAN_SCALAR_PTR_LITERAL(85, 116, 204, 74, 85, 134, 17, 161)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__98 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__98_value;
static lean_object* l_Lake_PackageConfig___fields___closed__99;
static lean_object* l_Lake_PackageConfig___fields___closed__100;
static const lean_string_object l_Lake_PackageConfig___fields___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "keywords"};
static const lean_object* l_Lake_PackageConfig___fields___closed__101 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__101_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__101_value),LEAN_SCALAR_PTR_LITERAL(84, 45, 198, 62, 56, 187, 72, 125)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__102 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__102_value;
static lean_object* l_Lake_PackageConfig___fields___closed__103;
static lean_object* l_Lake_PackageConfig___fields___closed__104;
static const lean_string_object l_Lake_PackageConfig___fields___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "homepage"};
static const lean_object* l_Lake_PackageConfig___fields___closed__105 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__105_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__105_value),LEAN_SCALAR_PTR_LITERAL(73, 148, 206, 183, 90, 222, 74, 16)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__106 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__106_value;
static lean_object* l_Lake_PackageConfig___fields___closed__107;
static lean_object* l_Lake_PackageConfig___fields___closed__108;
static const lean_string_object l_Lake_PackageConfig___fields___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "license"};
static const lean_object* l_Lake_PackageConfig___fields___closed__109 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__109_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__109_value),LEAN_SCALAR_PTR_LITERAL(149, 142, 81, 8, 241, 47, 83, 51)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__110 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__110_value;
static lean_object* l_Lake_PackageConfig___fields___closed__111;
static lean_object* l_Lake_PackageConfig___fields___closed__112;
static const lean_string_object l_Lake_PackageConfig___fields___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "licenseFiles"};
static const lean_object* l_Lake_PackageConfig___fields___closed__113 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__113_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__113_value),LEAN_SCALAR_PTR_LITERAL(115, 188, 70, 201, 62, 96, 76, 55)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__114 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__114_value;
static lean_object* l_Lake_PackageConfig___fields___closed__115;
static lean_object* l_Lake_PackageConfig___fields___closed__116;
static const lean_string_object l_Lake_PackageConfig___fields___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "readmeFile"};
static const lean_object* l_Lake_PackageConfig___fields___closed__117 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__117_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__117_value),LEAN_SCALAR_PTR_LITERAL(86, 68, 195, 254, 204, 64, 41, 249)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__118 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__118_value;
static lean_object* l_Lake_PackageConfig___fields___closed__119;
static lean_object* l_Lake_PackageConfig___fields___closed__120;
static const lean_string_object l_Lake_PackageConfig___fields___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reservoir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__121 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__121_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__121_value),LEAN_SCALAR_PTR_LITERAL(98, 62, 227, 196, 233, 158, 105, 168)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__122 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__122_value;
static lean_object* l_Lake_PackageConfig___fields___closed__123;
static lean_object* l_Lake_PackageConfig___fields___closed__124;
static const lean_string_object l_Lake_PackageConfig___fields___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "enableArtifactCache\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__125 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__125_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__125_value),LEAN_SCALAR_PTR_LITERAL(190, 150, 150, 100, 20, 242, 199, 174)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__126 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__126_value;
static lean_object* l_Lake_PackageConfig___fields___closed__127;
static lean_object* l_Lake_PackageConfig___fields___closed__128;
static const lean_string_object l_Lake_PackageConfig___fields___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "enableArtifactCache"};
static const lean_object* l_Lake_PackageConfig___fields___closed__129 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__129_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__129_value),LEAN_SCALAR_PTR_LITERAL(69, 183, 189, 255, 13, 235, 31, 38)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__130 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__130_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__130_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__126_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__131 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__131_value;
static lean_object* l_Lake_PackageConfig___fields___closed__132;
static const lean_string_object l_Lake_PackageConfig___fields___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "restoreAllArtifacts"};
static const lean_object* l_Lake_PackageConfig___fields___closed__133 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__133_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__133_value),LEAN_SCALAR_PTR_LITERAL(172, 122, 225, 122, 213, 189, 222, 165)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__134 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__134_value;
static lean_object* l_Lake_PackageConfig___fields___closed__135;
static lean_object* l_Lake_PackageConfig___fields___closed__136;
static const lean_string_object l_Lake_PackageConfig___fields___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "libPrefixOnWindows"};
static const lean_object* l_Lake_PackageConfig___fields___closed__137 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__137_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__137_value),LEAN_SCALAR_PTR_LITERAL(26, 75, 58, 45, 181, 132, 175, 34)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__138 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__138_value;
static lean_object* l_Lake_PackageConfig___fields___closed__139;
static lean_object* l_Lake_PackageConfig___fields___closed__140;
static const lean_string_object l_Lake_PackageConfig___fields___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "allowImportAll"};
static const lean_object* l_Lake_PackageConfig___fields___closed__141 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__141_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__141_value),LEAN_SCALAR_PTR_LITERAL(243, 199, 75, 91, 118, 43, 12, 210)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__142 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__142_value;
static lean_object* l_Lake_PackageConfig___fields___closed__143;
static lean_object* l_Lake_PackageConfig___fields___closed__144;
extern lean_object* l_Lake_WorkspaceConfig___fields;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig___fields___closed__145;
static const lean_string_object l_Lake_PackageConfig___fields___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "toWorkspaceConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__146 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__146_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__146_value),LEAN_SCALAR_PTR_LITERAL(135, 228, 155, 156, 156, 252, 46, 118)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__147 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__147_value;
static lean_object* l_Lake_PackageConfig___fields___closed__148;
static lean_object* l_Lake_PackageConfig___fields___closed__149;
extern lean_object* l_Lake_LeanConfig___fields;
static lean_object* l_Lake_PackageConfig___fields___closed__150;
static const lean_string_object l_Lake_PackageConfig___fields___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toLeanConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__151 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__151_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__151_value),LEAN_SCALAR_PTR_LITERAL(201, 26, 194, 50, 195, 212, 218, 10)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__152 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__152_value;
static lean_object* l_Lake_PackageConfig___fields___closed__153;
static lean_object* l_Lake_PackageConfig___fields___closed__154;
LEAN_EXPORT lean_object* l_Lake_PackageConfig___fields;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_PackageConfig_instConfigInfo___closed__0;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__1 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__1_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__2 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__2_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__3 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__3_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__4 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__4_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__5 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__5_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__6 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__6_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__7 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__7_value;
static const lean_ctor_object l_Lake_PackageConfig_instConfigInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__1_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__2_value)}};
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__8 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__8_value;
static const lean_ctor_object l_Lake_PackageConfig_instConfigInfo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__8_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__3_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__4_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__5_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__6_value)}};
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__9 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__9_value;
static const lean_ctor_object l_Lake_PackageConfig_instConfigInfo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__9_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__7_value)}};
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__10 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__10_value;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static uint8_t l_Lake_PackageConfig_instConfigInfo___closed__11;
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_instConfigInfo___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__12 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__12_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static uint8_t l_Lake_PackageConfig_instConfigInfo___closed__13;
size_t lean_usize_of_nat(lean_object*);
static size_t l_Lake_PackageConfig_instConfigInfo___closed__14;
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_instConfigInfo___closed__15;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo;
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value_aux_0),((lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(253, 117, 189, 141, 218, 132, 90, 198)}};
static const lean_object* l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value;
LEAN_EXPORT const lean_object* l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNamePackageDecl = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l_Lake_defaultBuildArchive(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = 0;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = ((lean_object*)(l_Lake_defaultBuildArchive___closed__0));
x_5 = lean_string_append(x_3, x_4);
x_6 = l_System_Platform_target;
x_7 = lean_string_append(x_5, x_6);
x_8 = ((lean_object*)(l_Lake_defaultBuildArchive___closed__1));
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageConfig_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageConfig_default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedPattern_default__1(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageConfig_default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_1 = l_Lake_instInhabitedPackageConfig_default___closed__2;
x_2 = l_Lake_instInhabitedStdVer_default;
x_3 = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
x_4 = l_System_instInhabitedFilePath_default;
x_5 = l_Lake_instInhabitedPackageConfig_default___closed__0;
x_6 = lean_box(0);
x_7 = 0;
x_8 = l_Lake_instInhabitedLeanConfig_default;
x_9 = l_Lake_instInhabitedWorkspaceConfig_default;
x_10 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set(x_10, 4, x_5);
lean_ctor_set(x_10, 5, x_4);
lean_ctor_set(x_10, 6, x_4);
lean_ctor_set(x_10, 7, x_4);
lean_ctor_set(x_10, 8, x_4);
lean_ctor_set(x_10, 9, x_4);
lean_ctor_set(x_10, 10, x_4);
lean_ctor_set(x_10, 11, x_6);
lean_ctor_set(x_10, 12, x_6);
lean_ctor_set(x_10, 13, x_3);
lean_ctor_set(x_10, 14, x_5);
lean_ctor_set(x_10, 15, x_3);
lean_ctor_set(x_10, 16, x_5);
lean_ctor_set(x_10, 17, x_2);
lean_ctor_set(x_10, 18, x_1);
lean_ctor_set(x_10, 19, x_3);
lean_ctor_set(x_10, 20, x_5);
lean_ctor_set(x_10, 21, x_3);
lean_ctor_set(x_10, 22, x_3);
lean_ctor_set(x_10, 23, x_5);
lean_ctor_set(x_10, 24, x_4);
lean_ctor_set(x_10, 25, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*26 + 1, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*26 + 2, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*26 + 3, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*26 + 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*26 + 5, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*26 + 6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instInhabitedPackageConfig_default___closed__3;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instInhabitedPackageConfig_default(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instInhabitedPackageConfig_default(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instInhabitedPackageConfig(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*26);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_PackageConfig_bootstrap___proj___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_2, sizeof(void*)*26, x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_9 = lean_ctor_get(x_2, 4);
x_10 = lean_ctor_get(x_2, 5);
x_11 = lean_ctor_get(x_2, 6);
x_12 = lean_ctor_get(x_2, 7);
x_13 = lean_ctor_get(x_2, 8);
x_14 = lean_ctor_get(x_2, 9);
x_15 = lean_ctor_get(x_2, 10);
x_16 = lean_ctor_get(x_2, 11);
x_17 = lean_ctor_get(x_2, 12);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_19 = lean_ctor_get(x_2, 13);
x_20 = lean_ctor_get(x_2, 14);
x_21 = lean_ctor_get(x_2, 15);
x_22 = lean_ctor_get(x_2, 16);
x_23 = lean_ctor_get(x_2, 17);
x_24 = lean_ctor_get(x_2, 18);
x_25 = lean_ctor_get(x_2, 19);
x_26 = lean_ctor_get(x_2, 20);
x_27 = lean_ctor_get(x_2, 21);
x_28 = lean_ctor_get(x_2, 22);
x_29 = lean_ctor_get(x_2, 23);
x_30 = lean_ctor_get(x_2, 24);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_32 = lean_ctor_get(x_2, 25);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_36, 2, x_6);
lean_ctor_set(x_36, 3, x_7);
lean_ctor_set(x_36, 4, x_9);
lean_ctor_set(x_36, 5, x_10);
lean_ctor_set(x_36, 6, x_11);
lean_ctor_set(x_36, 7, x_12);
lean_ctor_set(x_36, 8, x_13);
lean_ctor_set(x_36, 9, x_14);
lean_ctor_set(x_36, 10, x_15);
lean_ctor_set(x_36, 11, x_16);
lean_ctor_set(x_36, 12, x_17);
lean_ctor_set(x_36, 13, x_19);
lean_ctor_set(x_36, 14, x_20);
lean_ctor_set(x_36, 15, x_21);
lean_ctor_set(x_36, 16, x_22);
lean_ctor_set(x_36, 17, x_23);
lean_ctor_set(x_36, 18, x_24);
lean_ctor_set(x_36, 19, x_25);
lean_ctor_set(x_36, 20, x_26);
lean_ctor_set(x_36, 21, x_27);
lean_ctor_set(x_36, 22, x_28);
lean_ctor_set(x_36, 23, x_29);
lean_ctor_set(x_36, 24, x_30);
lean_ctor_set(x_36, 25, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*26, x_1);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 1, x_8);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 2, x_18);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 3, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 4, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 5, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 6, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_PackageConfig_bootstrap___proj___lam__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_5 = lean_box(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_ctor_set_uint8(x_2, sizeof(void*)*26, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_14 = lean_ctor_get(x_2, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_ctor_get(x_2, 6);
x_17 = lean_ctor_get(x_2, 7);
x_18 = lean_ctor_get(x_2, 8);
x_19 = lean_ctor_get(x_2, 9);
x_20 = lean_ctor_get(x_2, 10);
x_21 = lean_ctor_get(x_2, 11);
x_22 = lean_ctor_get(x_2, 12);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_24 = lean_ctor_get(x_2, 13);
x_25 = lean_ctor_get(x_2, 14);
x_26 = lean_ctor_get(x_2, 15);
x_27 = lean_ctor_get(x_2, 16);
x_28 = lean_ctor_get(x_2, 17);
x_29 = lean_ctor_get(x_2, 18);
x_30 = lean_ctor_get(x_2, 19);
x_31 = lean_ctor_get(x_2, 20);
x_32 = lean_ctor_get(x_2, 21);
x_33 = lean_ctor_get(x_2, 22);
x_34 = lean_ctor_get(x_2, 23);
x_35 = lean_ctor_get(x_2, 24);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_37 = lean_ctor_get(x_2, 25);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_41 = lean_box(x_10);
x_42 = lean_apply_1(x_1, x_41);
x_43 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_11);
lean_ctor_set(x_43, 3, x_12);
lean_ctor_set(x_43, 4, x_14);
lean_ctor_set(x_43, 5, x_15);
lean_ctor_set(x_43, 6, x_16);
lean_ctor_set(x_43, 7, x_17);
lean_ctor_set(x_43, 8, x_18);
lean_ctor_set(x_43, 9, x_19);
lean_ctor_set(x_43, 10, x_20);
lean_ctor_set(x_43, 11, x_21);
lean_ctor_set(x_43, 12, x_22);
lean_ctor_set(x_43, 13, x_24);
lean_ctor_set(x_43, 14, x_25);
lean_ctor_set(x_43, 15, x_26);
lean_ctor_set(x_43, 16, x_27);
lean_ctor_set(x_43, 17, x_28);
lean_ctor_set(x_43, 18, x_29);
lean_ctor_set(x_43, 19, x_30);
lean_ctor_set(x_43, 20, x_31);
lean_ctor_set(x_43, 21, x_32);
lean_ctor_set(x_43, 22, x_33);
lean_ctor_set(x_43, 23, x_34);
lean_ctor_set(x_43, 24, x_35);
lean_ctor_set(x_43, 25, x_37);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*26, x_44);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 1, x_13);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 2, x_23);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 3, x_36);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 4, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 5, x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 6, x_40);
return x_43;
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__3(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_PackageConfig_bootstrap___proj___lam__3(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_bootstrap___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_bootstrap___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_bootstrap___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_bootstrap_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_manifestFile___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 2);
lean_dec(x_4);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_1);
lean_ctor_set(x_37, 3, x_8);
lean_ctor_set(x_37, 4, x_10);
lean_ctor_set(x_37, 5, x_11);
lean_ctor_set(x_37, 6, x_12);
lean_ctor_set(x_37, 7, x_13);
lean_ctor_set(x_37, 8, x_14);
lean_ctor_set(x_37, 9, x_15);
lean_ctor_set(x_37, 10, x_16);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_9);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 2, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_9);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_manifestFile___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_manifestFile___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_manifestFile___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_manifestFile___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_manifestFile_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_extraDepTargets___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 3);
lean_dec(x_4);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_1);
lean_ctor_set(x_37, 4, x_10);
lean_ctor_set(x_37, 5, x_11);
lean_ctor_set(x_37, 6, x_12);
lean_ctor_set(x_37, 7, x_13);
lean_ctor_set(x_37, 8, x_14);
lean_ctor_set(x_37, 9, x_15);
lean_ctor_set(x_37, 10, x_16);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_9);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 3, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_10);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_extraDepTargets___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_extraDepTargets___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_extraDepTargets___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_extraDepTargets_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___proj___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*26 + 1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_PackageConfig_precompileModules___proj___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 1, x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
x_10 = lean_ctor_get(x_2, 5);
x_11 = lean_ctor_get(x_2, 6);
x_12 = lean_ctor_get(x_2, 7);
x_13 = lean_ctor_get(x_2, 8);
x_14 = lean_ctor_get(x_2, 9);
x_15 = lean_ctor_get(x_2, 10);
x_16 = lean_ctor_get(x_2, 11);
x_17 = lean_ctor_get(x_2, 12);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_19 = lean_ctor_get(x_2, 13);
x_20 = lean_ctor_get(x_2, 14);
x_21 = lean_ctor_get(x_2, 15);
x_22 = lean_ctor_get(x_2, 16);
x_23 = lean_ctor_get(x_2, 17);
x_24 = lean_ctor_get(x_2, 18);
x_25 = lean_ctor_get(x_2, 19);
x_26 = lean_ctor_get(x_2, 20);
x_27 = lean_ctor_get(x_2, 21);
x_28 = lean_ctor_get(x_2, 22);
x_29 = lean_ctor_get(x_2, 23);
x_30 = lean_ctor_get(x_2, 24);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_32 = lean_ctor_get(x_2, 25);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_36, 2, x_7);
lean_ctor_set(x_36, 3, x_8);
lean_ctor_set(x_36, 4, x_9);
lean_ctor_set(x_36, 5, x_10);
lean_ctor_set(x_36, 6, x_11);
lean_ctor_set(x_36, 7, x_12);
lean_ctor_set(x_36, 8, x_13);
lean_ctor_set(x_36, 9, x_14);
lean_ctor_set(x_36, 10, x_15);
lean_ctor_set(x_36, 11, x_16);
lean_ctor_set(x_36, 12, x_17);
lean_ctor_set(x_36, 13, x_19);
lean_ctor_set(x_36, 14, x_20);
lean_ctor_set(x_36, 15, x_21);
lean_ctor_set(x_36, 16, x_22);
lean_ctor_set(x_36, 17, x_23);
lean_ctor_set(x_36, 18, x_24);
lean_ctor_set(x_36, 19, x_25);
lean_ctor_set(x_36, 20, x_26);
lean_ctor_set(x_36, 21, x_27);
lean_ctor_set(x_36, 22, x_28);
lean_ctor_set(x_36, 23, x_29);
lean_ctor_set(x_36, 24, x_30);
lean_ctor_set(x_36, 25, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*26, x_6);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 1, x_1);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 2, x_18);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 3, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 4, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 5, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 6, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_PackageConfig_precompileModules___proj___lam__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_5 = lean_box(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 1, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_14 = lean_ctor_get(x_2, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_ctor_get(x_2, 6);
x_17 = lean_ctor_get(x_2, 7);
x_18 = lean_ctor_get(x_2, 8);
x_19 = lean_ctor_get(x_2, 9);
x_20 = lean_ctor_get(x_2, 10);
x_21 = lean_ctor_get(x_2, 11);
x_22 = lean_ctor_get(x_2, 12);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_24 = lean_ctor_get(x_2, 13);
x_25 = lean_ctor_get(x_2, 14);
x_26 = lean_ctor_get(x_2, 15);
x_27 = lean_ctor_get(x_2, 16);
x_28 = lean_ctor_get(x_2, 17);
x_29 = lean_ctor_get(x_2, 18);
x_30 = lean_ctor_get(x_2, 19);
x_31 = lean_ctor_get(x_2, 20);
x_32 = lean_ctor_get(x_2, 21);
x_33 = lean_ctor_get(x_2, 22);
x_34 = lean_ctor_get(x_2, 23);
x_35 = lean_ctor_get(x_2, 24);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_37 = lean_ctor_get(x_2, 25);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_41 = lean_box(x_13);
x_42 = lean_apply_1(x_1, x_41);
x_43 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_11);
lean_ctor_set(x_43, 3, x_12);
lean_ctor_set(x_43, 4, x_14);
lean_ctor_set(x_43, 5, x_15);
lean_ctor_set(x_43, 6, x_16);
lean_ctor_set(x_43, 7, x_17);
lean_ctor_set(x_43, 8, x_18);
lean_ctor_set(x_43, 9, x_19);
lean_ctor_set(x_43, 10, x_20);
lean_ctor_set(x_43, 11, x_21);
lean_ctor_set(x_43, 12, x_22);
lean_ctor_set(x_43, 13, x_24);
lean_ctor_set(x_43, 14, x_25);
lean_ctor_set(x_43, 15, x_26);
lean_ctor_set(x_43, 16, x_27);
lean_ctor_set(x_43, 17, x_28);
lean_ctor_set(x_43, 18, x_29);
lean_ctor_set(x_43, 19, x_30);
lean_ctor_set(x_43, 20, x_31);
lean_ctor_set(x_43, 21, x_32);
lean_ctor_set(x_43, 22, x_33);
lean_ctor_set(x_43, 23, x_34);
lean_ctor_set(x_43, 24, x_35);
lean_ctor_set(x_43, 25, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*26, x_10);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 1, x_44);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 2, x_23);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 3, x_36);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 4, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 5, x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 6, x_40);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_precompileModules___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_precompileModules___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_precompileModules___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_precompileModules_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 4);
lean_dec(x_4);
lean_ctor_set(x_2, 4, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_1);
lean_ctor_set(x_37, 5, x_11);
lean_ctor_set(x_37, 6, x_12);
lean_ctor_set(x_37, 7, x_13);
lean_ctor_set(x_37, 8, x_14);
lean_ctor_set(x_37, 9, x_15);
lean_ctor_set(x_37, 10, x_16);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 4, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_12);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_moreGlobalServerArgs___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_moreGlobalServerArgs___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_moreGlobalServerArgs___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_moreServerArgs_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_srcDir___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 5);
lean_dec(x_4);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_1);
lean_ctor_set(x_37, 6, x_12);
lean_ctor_set(x_37, 7, x_13);
lean_ctor_set(x_37, 8, x_14);
lean_ctor_set(x_37, 9, x_15);
lean_ctor_set(x_37, 10, x_16);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 5);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 5, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_13);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___lam__3___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_srcDir___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_srcDir___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_srcDir___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_srcDir_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_buildDir___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 6);
lean_dec(x_4);
lean_ctor_set(x_2, 6, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_1);
lean_ctor_set(x_37, 7, x_13);
lean_ctor_set(x_37, 8, x_14);
lean_ctor_set(x_37, 9, x_15);
lean_ctor_set(x_37, 10, x_16);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 6);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 6, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_14);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_39);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_defaultBuildDir;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_buildDir___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_buildDir___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_buildDir___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_buildDir___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_buildDir_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_leanLibDir___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 7);
lean_dec(x_4);
lean_ctor_set(x_2, 7, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_1);
lean_ctor_set(x_37, 8, x_14);
lean_ctor_set(x_37, 9, x_15);
lean_ctor_set(x_37, 10, x_16);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 7);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 7, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_15);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_39);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_defaultLeanLibDir;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_leanLibDir___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_leanLibDir___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_leanLibDir___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_leanLibDir___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_leanLibDir_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_nativeLibDir___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 8);
lean_dec(x_4);
lean_ctor_set(x_2, 8, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_1);
lean_ctor_set(x_37, 9, x_15);
lean_ctor_set(x_37, 10, x_16);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 8);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 8, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_16);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_39);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_defaultNativeLibDir;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_nativeLibDir___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_nativeLibDir___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_nativeLibDir___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_nativeLibDir___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_nativeLibDir_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_binDir___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 9);
lean_dec(x_4);
lean_ctor_set(x_2, 9, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_1);
lean_ctor_set(x_37, 10, x_16);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 9);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 9, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_17);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_39);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_defaultBinDir;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_binDir___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_binDir___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_binDir___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_binDir___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_binDir_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 10);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_irDir___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 10);
lean_dec(x_4);
lean_ctor_set(x_2, 10, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_1);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 10);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 10, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_18);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_39);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_defaultIrDir;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_irDir___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_irDir___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_irDir___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_irDir___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_irDir_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 11);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_releaseRepo___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 11);
lean_dec(x_4);
lean_ctor_set(x_2, 11, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_1);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 11);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 11, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_19);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_39);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_releaseRepo___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_releaseRepo___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_releaseRepo___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_releaseRepo_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_releaseRepo___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 12);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_buildArchive___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 12);
lean_dec(x_4);
lean_ctor_set(x_2, 12, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_1);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 12);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 12, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_20);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_39);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_buildArchive___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_buildArchive___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_buildArchive___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_buildArchive_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_buildArchive___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_buildArchive_x3f_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*26 + 2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 2, x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get(x_2, 13);
x_20 = lean_ctor_get(x_2, 14);
x_21 = lean_ctor_get(x_2, 15);
x_22 = lean_ctor_get(x_2, 16);
x_23 = lean_ctor_get(x_2, 17);
x_24 = lean_ctor_get(x_2, 18);
x_25 = lean_ctor_get(x_2, 19);
x_26 = lean_ctor_get(x_2, 20);
x_27 = lean_ctor_get(x_2, 21);
x_28 = lean_ctor_get(x_2, 22);
x_29 = lean_ctor_get(x_2, 23);
x_30 = lean_ctor_get(x_2, 24);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_32 = lean_ctor_get(x_2, 25);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_36, 2, x_7);
lean_ctor_set(x_36, 3, x_8);
lean_ctor_set(x_36, 4, x_10);
lean_ctor_set(x_36, 5, x_11);
lean_ctor_set(x_36, 6, x_12);
lean_ctor_set(x_36, 7, x_13);
lean_ctor_set(x_36, 8, x_14);
lean_ctor_set(x_36, 9, x_15);
lean_ctor_set(x_36, 10, x_16);
lean_ctor_set(x_36, 11, x_17);
lean_ctor_set(x_36, 12, x_18);
lean_ctor_set(x_36, 13, x_19);
lean_ctor_set(x_36, 14, x_20);
lean_ctor_set(x_36, 15, x_21);
lean_ctor_set(x_36, 16, x_22);
lean_ctor_set(x_36, 17, x_23);
lean_ctor_set(x_36, 18, x_24);
lean_ctor_set(x_36, 19, x_25);
lean_ctor_set(x_36, 20, x_26);
lean_ctor_set(x_36, 21, x_27);
lean_ctor_set(x_36, 22, x_28);
lean_ctor_set(x_36, 23, x_29);
lean_ctor_set(x_36, 24, x_30);
lean_ctor_set(x_36, 25, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*26, x_6);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 1, x_9);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 2, x_1);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 3, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 4, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 5, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 6, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_5 = lean_box(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 2, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_14 = lean_ctor_get(x_2, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_ctor_get(x_2, 6);
x_17 = lean_ctor_get(x_2, 7);
x_18 = lean_ctor_get(x_2, 8);
x_19 = lean_ctor_get(x_2, 9);
x_20 = lean_ctor_get(x_2, 10);
x_21 = lean_ctor_get(x_2, 11);
x_22 = lean_ctor_get(x_2, 12);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_24 = lean_ctor_get(x_2, 13);
x_25 = lean_ctor_get(x_2, 14);
x_26 = lean_ctor_get(x_2, 15);
x_27 = lean_ctor_get(x_2, 16);
x_28 = lean_ctor_get(x_2, 17);
x_29 = lean_ctor_get(x_2, 18);
x_30 = lean_ctor_get(x_2, 19);
x_31 = lean_ctor_get(x_2, 20);
x_32 = lean_ctor_get(x_2, 21);
x_33 = lean_ctor_get(x_2, 22);
x_34 = lean_ctor_get(x_2, 23);
x_35 = lean_ctor_get(x_2, 24);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_37 = lean_ctor_get(x_2, 25);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_41 = lean_box(x_23);
x_42 = lean_apply_1(x_1, x_41);
x_43 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_11);
lean_ctor_set(x_43, 3, x_12);
lean_ctor_set(x_43, 4, x_14);
lean_ctor_set(x_43, 5, x_15);
lean_ctor_set(x_43, 6, x_16);
lean_ctor_set(x_43, 7, x_17);
lean_ctor_set(x_43, 8, x_18);
lean_ctor_set(x_43, 9, x_19);
lean_ctor_set(x_43, 10, x_20);
lean_ctor_set(x_43, 11, x_21);
lean_ctor_set(x_43, 12, x_22);
lean_ctor_set(x_43, 13, x_24);
lean_ctor_set(x_43, 14, x_25);
lean_ctor_set(x_43, 15, x_26);
lean_ctor_set(x_43, 16, x_27);
lean_ctor_set(x_43, 17, x_28);
lean_ctor_set(x_43, 18, x_29);
lean_ctor_set(x_43, 19, x_30);
lean_ctor_set(x_43, 20, x_31);
lean_ctor_set(x_43, 21, x_32);
lean_ctor_set(x_43, 22, x_33);
lean_ctor_set(x_43, 23, x_34);
lean_ctor_set(x_43, 24, x_35);
lean_ctor_set(x_43, 25, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*26, x_10);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 1, x_13);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 2, x_44);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 3, x_36);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 4, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 5, x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 6, x_40);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_preferReleaseBuild___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_preferReleaseBuild___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_preferReleaseBuild___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_preferReleaseBuild_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 13);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_testDriver___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 13);
lean_dec(x_4);
lean_ctor_set(x_2, 13, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_1);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 13);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 13, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_22);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_39);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_testDriver___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_testDriver___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_testDriver___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_testDriver___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_testDriver_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_testDriver___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_testRunner_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 14);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_testDriverArgs___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 14);
lean_dec(x_4);
lean_ctor_set(x_2, 14, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_1);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 14);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 14, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_23);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_39);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_testDriverArgs___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_testDriverArgs___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_testDriverArgs___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_testDriverArgs_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 15);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_lintDriver___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 15);
lean_dec(x_4);
lean_ctor_set(x_2, 15, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_1);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 15);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 15, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_24);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_39);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_lintDriver___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_lintDriver___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_lintDriver___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_lintDriver_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 16);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 16);
lean_dec(x_4);
lean_ctor_set(x_2, 16, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_23);
lean_ctor_set(x_37, 16, x_1);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 16);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 16, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_25);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_39);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_lintDriverArgs___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_lintDriverArgs___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_lintDriverArgs___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_lintDriverArgs_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 17);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_version___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 17);
lean_dec(x_4);
lean_ctor_set(x_2, 17, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_23);
lean_ctor_set(x_37, 16, x_24);
lean_ctor_set(x_37, 17, x_1);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 17);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 17, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_26);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_39);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lake_PackageConfig_version___proj___lam__3___closed__1));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_version___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_version___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_version___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_version___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_version_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 18);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_versionTags___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 18);
lean_dec(x_4);
lean_ctor_set(x_2, 18, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_23);
lean_ctor_set(x_37, 16, x_24);
lean_ctor_set(x_37, 17, x_25);
lean_ctor_set(x_37, 18, x_1);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 18);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 18, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_27);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_39);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_defaultVersionTags;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_versionTags___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_versionTags___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_versionTags___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_versionTags___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_versionTags_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 19);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_description___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 19);
lean_dec(x_4);
lean_ctor_set(x_2, 19, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 18);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_23);
lean_ctor_set(x_37, 16, x_24);
lean_ctor_set(x_37, 17, x_25);
lean_ctor_set(x_37, 18, x_26);
lean_ctor_set(x_37, 19, x_1);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 19);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 19, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_28);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_39);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_description___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_description___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_description___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_description_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 20);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_keywords___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 20);
lean_dec(x_4);
lean_ctor_set(x_2, 20, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 18);
x_27 = lean_ctor_get(x_2, 19);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_23);
lean_ctor_set(x_37, 16, x_24);
lean_ctor_set(x_37, 17, x_25);
lean_ctor_set(x_37, 18, x_26);
lean_ctor_set(x_37, 19, x_27);
lean_ctor_set(x_37, 20, x_1);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 20);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 20, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_29);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_39);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_keywords___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_keywords___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_keywords___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_keywords_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 21);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_homepage___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 21);
lean_dec(x_4);
lean_ctor_set(x_2, 21, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 18);
x_27 = lean_ctor_get(x_2, 19);
x_28 = lean_ctor_get(x_2, 20);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_23);
lean_ctor_set(x_37, 16, x_24);
lean_ctor_set(x_37, 17, x_25);
lean_ctor_set(x_37, 18, x_26);
lean_ctor_set(x_37, 19, x_27);
lean_ctor_set(x_37, 20, x_28);
lean_ctor_set(x_37, 21, x_1);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 21);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 21, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_30);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_39);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_homepage___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_homepage___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_homepage___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_homepage_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 22);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_license___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 22);
lean_dec(x_4);
lean_ctor_set(x_2, 22, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 18);
x_27 = lean_ctor_get(x_2, 19);
x_28 = lean_ctor_get(x_2, 20);
x_29 = lean_ctor_get(x_2, 21);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_23);
lean_ctor_set(x_37, 16, x_24);
lean_ctor_set(x_37, 17, x_25);
lean_ctor_set(x_37, 18, x_26);
lean_ctor_set(x_37, 19, x_27);
lean_ctor_set(x_37, 20, x_28);
lean_ctor_set(x_37, 21, x_29);
lean_ctor_set(x_37, 22, x_1);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 22);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 22, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_31);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_39);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_license___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_license___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_license___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_license_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 23);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_licenseFiles___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 23);
lean_dec(x_4);
lean_ctor_set(x_2, 23, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 18);
x_27 = lean_ctor_get(x_2, 19);
x_28 = lean_ctor_get(x_2, 20);
x_29 = lean_ctor_get(x_2, 21);
x_30 = lean_ctor_get(x_2, 22);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_23);
lean_ctor_set(x_37, 16, x_24);
lean_ctor_set(x_37, 17, x_25);
lean_ctor_set(x_37, 18, x_26);
lean_ctor_set(x_37, 19, x_27);
lean_ctor_set(x_37, 20, x_28);
lean_ctor_set(x_37, 21, x_29);
lean_ctor_set(x_37, 22, x_30);
lean_ctor_set(x_37, 23, x_1);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 23);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 23, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_32);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_39);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__0));
x_2 = l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__2;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_licenseFiles___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_licenseFiles___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_licenseFiles___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_licenseFiles_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 24);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_readmeFile___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 24);
lean_dec(x_4);
lean_ctor_set(x_2, 24, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 18);
x_27 = lean_ctor_get(x_2, 19);
x_28 = lean_ctor_get(x_2, 20);
x_29 = lean_ctor_get(x_2, 21);
x_30 = lean_ctor_get(x_2, 22);
x_31 = lean_ctor_get(x_2, 23);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_23);
lean_ctor_set(x_37, 16, x_24);
lean_ctor_set(x_37, 17, x_25);
lean_ctor_set(x_37, 18, x_26);
lean_ctor_set(x_37, 19, x_27);
lean_ctor_set(x_37, 20, x_28);
lean_ctor_set(x_37, 21, x_29);
lean_ctor_set(x_37, 22, x_30);
lean_ctor_set(x_37, 23, x_31);
lean_ctor_set(x_37, 24, x_1);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 24);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 24, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_33);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_39);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___lam__3___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_readmeFile___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_readmeFile___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_readmeFile___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_readmeFile_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*26 + 3);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_PackageConfig_reservoir___proj___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 3, x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get(x_2, 25);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_36, 2, x_7);
lean_ctor_set(x_36, 3, x_8);
lean_ctor_set(x_36, 4, x_10);
lean_ctor_set(x_36, 5, x_11);
lean_ctor_set(x_36, 6, x_12);
lean_ctor_set(x_36, 7, x_13);
lean_ctor_set(x_36, 8, x_14);
lean_ctor_set(x_36, 9, x_15);
lean_ctor_set(x_36, 10, x_16);
lean_ctor_set(x_36, 11, x_17);
lean_ctor_set(x_36, 12, x_18);
lean_ctor_set(x_36, 13, x_20);
lean_ctor_set(x_36, 14, x_21);
lean_ctor_set(x_36, 15, x_22);
lean_ctor_set(x_36, 16, x_23);
lean_ctor_set(x_36, 17, x_24);
lean_ctor_set(x_36, 18, x_25);
lean_ctor_set(x_36, 19, x_26);
lean_ctor_set(x_36, 20, x_27);
lean_ctor_set(x_36, 21, x_28);
lean_ctor_set(x_36, 22, x_29);
lean_ctor_set(x_36, 23, x_30);
lean_ctor_set(x_36, 24, x_31);
lean_ctor_set(x_36, 25, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*26, x_6);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 1, x_9);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 3, x_1);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 4, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 5, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 6, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_PackageConfig_reservoir___proj___lam__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_5 = lean_box(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 3, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_14 = lean_ctor_get(x_2, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_ctor_get(x_2, 6);
x_17 = lean_ctor_get(x_2, 7);
x_18 = lean_ctor_get(x_2, 8);
x_19 = lean_ctor_get(x_2, 9);
x_20 = lean_ctor_get(x_2, 10);
x_21 = lean_ctor_get(x_2, 11);
x_22 = lean_ctor_get(x_2, 12);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_24 = lean_ctor_get(x_2, 13);
x_25 = lean_ctor_get(x_2, 14);
x_26 = lean_ctor_get(x_2, 15);
x_27 = lean_ctor_get(x_2, 16);
x_28 = lean_ctor_get(x_2, 17);
x_29 = lean_ctor_get(x_2, 18);
x_30 = lean_ctor_get(x_2, 19);
x_31 = lean_ctor_get(x_2, 20);
x_32 = lean_ctor_get(x_2, 21);
x_33 = lean_ctor_get(x_2, 22);
x_34 = lean_ctor_get(x_2, 23);
x_35 = lean_ctor_get(x_2, 24);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_37 = lean_ctor_get(x_2, 25);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_41 = lean_box(x_36);
x_42 = lean_apply_1(x_1, x_41);
x_43 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_11);
lean_ctor_set(x_43, 3, x_12);
lean_ctor_set(x_43, 4, x_14);
lean_ctor_set(x_43, 5, x_15);
lean_ctor_set(x_43, 6, x_16);
lean_ctor_set(x_43, 7, x_17);
lean_ctor_set(x_43, 8, x_18);
lean_ctor_set(x_43, 9, x_19);
lean_ctor_set(x_43, 10, x_20);
lean_ctor_set(x_43, 11, x_21);
lean_ctor_set(x_43, 12, x_22);
lean_ctor_set(x_43, 13, x_24);
lean_ctor_set(x_43, 14, x_25);
lean_ctor_set(x_43, 15, x_26);
lean_ctor_set(x_43, 16, x_27);
lean_ctor_set(x_43, 17, x_28);
lean_ctor_set(x_43, 18, x_29);
lean_ctor_set(x_43, 19, x_30);
lean_ctor_set(x_43, 20, x_31);
lean_ctor_set(x_43, 21, x_32);
lean_ctor_set(x_43, 22, x_33);
lean_ctor_set(x_43, 23, x_34);
lean_ctor_set(x_43, 24, x_35);
lean_ctor_set(x_43, 25, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*26, x_10);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 1, x_13);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 2, x_23);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 3, x_44);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 4, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 5, x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 6, x_40);
return x_43;
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__3(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_PackageConfig_reservoir___proj___lam__3(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_reservoir___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_reservoir___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_reservoir___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_reservoir_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 25);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 25);
lean_dec(x_4);
lean_ctor_set(x_2, 25, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 18);
x_27 = lean_ctor_get(x_2, 19);
x_28 = lean_ctor_get(x_2, 20);
x_29 = lean_ctor_get(x_2, 21);
x_30 = lean_ctor_get(x_2, 22);
x_31 = lean_ctor_get(x_2, 23);
x_32 = lean_ctor_get(x_2, 24);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_14);
lean_ctor_set(x_37, 8, x_15);
lean_ctor_set(x_37, 9, x_16);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_21);
lean_ctor_set(x_37, 14, x_22);
lean_ctor_set(x_37, 15, x_23);
lean_ctor_set(x_37, 16, x_24);
lean_ctor_set(x_37, 17, x_25);
lean_ctor_set(x_37, 18, x_26);
lean_ctor_set(x_37, 19, x_27);
lean_ctor_set(x_37, 20, x_28);
lean_ctor_set(x_37, 21, x_29);
lean_ctor_set(x_37, 22, x_30);
lean_ctor_set(x_37, 23, x_31);
lean_ctor_set(x_37, 24, x_32);
lean_ctor_set(x_37, 25, x_1);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_7);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 25);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 25, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_35);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_enableArtifactCache_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*26 + 4);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 4, x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_36, 2, x_7);
lean_ctor_set(x_36, 3, x_8);
lean_ctor_set(x_36, 4, x_10);
lean_ctor_set(x_36, 5, x_11);
lean_ctor_set(x_36, 6, x_12);
lean_ctor_set(x_36, 7, x_13);
lean_ctor_set(x_36, 8, x_14);
lean_ctor_set(x_36, 9, x_15);
lean_ctor_set(x_36, 10, x_16);
lean_ctor_set(x_36, 11, x_17);
lean_ctor_set(x_36, 12, x_18);
lean_ctor_set(x_36, 13, x_20);
lean_ctor_set(x_36, 14, x_21);
lean_ctor_set(x_36, 15, x_22);
lean_ctor_set(x_36, 16, x_23);
lean_ctor_set(x_36, 17, x_24);
lean_ctor_set(x_36, 18, x_25);
lean_ctor_set(x_36, 19, x_26);
lean_ctor_set(x_36, 20, x_27);
lean_ctor_set(x_36, 21, x_28);
lean_ctor_set(x_36, 22, x_29);
lean_ctor_set(x_36, 23, x_30);
lean_ctor_set(x_36, 24, x_31);
lean_ctor_set(x_36, 25, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*26, x_6);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 1, x_9);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 4, x_1);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 5, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 6, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_5 = lean_box(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 4, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_14 = lean_ctor_get(x_2, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_ctor_get(x_2, 6);
x_17 = lean_ctor_get(x_2, 7);
x_18 = lean_ctor_get(x_2, 8);
x_19 = lean_ctor_get(x_2, 9);
x_20 = lean_ctor_get(x_2, 10);
x_21 = lean_ctor_get(x_2, 11);
x_22 = lean_ctor_get(x_2, 12);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_24 = lean_ctor_get(x_2, 13);
x_25 = lean_ctor_get(x_2, 14);
x_26 = lean_ctor_get(x_2, 15);
x_27 = lean_ctor_get(x_2, 16);
x_28 = lean_ctor_get(x_2, 17);
x_29 = lean_ctor_get(x_2, 18);
x_30 = lean_ctor_get(x_2, 19);
x_31 = lean_ctor_get(x_2, 20);
x_32 = lean_ctor_get(x_2, 21);
x_33 = lean_ctor_get(x_2, 22);
x_34 = lean_ctor_get(x_2, 23);
x_35 = lean_ctor_get(x_2, 24);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_37 = lean_ctor_get(x_2, 25);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_41 = lean_box(x_38);
x_42 = lean_apply_1(x_1, x_41);
x_43 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_11);
lean_ctor_set(x_43, 3, x_12);
lean_ctor_set(x_43, 4, x_14);
lean_ctor_set(x_43, 5, x_15);
lean_ctor_set(x_43, 6, x_16);
lean_ctor_set(x_43, 7, x_17);
lean_ctor_set(x_43, 8, x_18);
lean_ctor_set(x_43, 9, x_19);
lean_ctor_set(x_43, 10, x_20);
lean_ctor_set(x_43, 11, x_21);
lean_ctor_set(x_43, 12, x_22);
lean_ctor_set(x_43, 13, x_24);
lean_ctor_set(x_43, 14, x_25);
lean_ctor_set(x_43, 15, x_26);
lean_ctor_set(x_43, 16, x_27);
lean_ctor_set(x_43, 17, x_28);
lean_ctor_set(x_43, 18, x_29);
lean_ctor_set(x_43, 19, x_30);
lean_ctor_set(x_43, 20, x_31);
lean_ctor_set(x_43, 21, x_32);
lean_ctor_set(x_43, 22, x_33);
lean_ctor_set(x_43, 23, x_34);
lean_ctor_set(x_43, 24, x_35);
lean_ctor_set(x_43, 25, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*26, x_10);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 1, x_13);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 2, x_23);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 3, x_36);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 4, x_44);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 5, x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 6, x_40);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_restoreAllArtifacts___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_restoreAllArtifacts___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_restoreAllArtifacts___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*26 + 5);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 5, x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_36, 2, x_7);
lean_ctor_set(x_36, 3, x_8);
lean_ctor_set(x_36, 4, x_10);
lean_ctor_set(x_36, 5, x_11);
lean_ctor_set(x_36, 6, x_12);
lean_ctor_set(x_36, 7, x_13);
lean_ctor_set(x_36, 8, x_14);
lean_ctor_set(x_36, 9, x_15);
lean_ctor_set(x_36, 10, x_16);
lean_ctor_set(x_36, 11, x_17);
lean_ctor_set(x_36, 12, x_18);
lean_ctor_set(x_36, 13, x_20);
lean_ctor_set(x_36, 14, x_21);
lean_ctor_set(x_36, 15, x_22);
lean_ctor_set(x_36, 16, x_23);
lean_ctor_set(x_36, 17, x_24);
lean_ctor_set(x_36, 18, x_25);
lean_ctor_set(x_36, 19, x_26);
lean_ctor_set(x_36, 20, x_27);
lean_ctor_set(x_36, 21, x_28);
lean_ctor_set(x_36, 22, x_29);
lean_ctor_set(x_36, 23, x_30);
lean_ctor_set(x_36, 24, x_31);
lean_ctor_set(x_36, 25, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*26, x_6);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 1, x_9);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 5, x_1);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 6, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_5 = lean_box(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 5, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_14 = lean_ctor_get(x_2, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_ctor_get(x_2, 6);
x_17 = lean_ctor_get(x_2, 7);
x_18 = lean_ctor_get(x_2, 8);
x_19 = lean_ctor_get(x_2, 9);
x_20 = lean_ctor_get(x_2, 10);
x_21 = lean_ctor_get(x_2, 11);
x_22 = lean_ctor_get(x_2, 12);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_24 = lean_ctor_get(x_2, 13);
x_25 = lean_ctor_get(x_2, 14);
x_26 = lean_ctor_get(x_2, 15);
x_27 = lean_ctor_get(x_2, 16);
x_28 = lean_ctor_get(x_2, 17);
x_29 = lean_ctor_get(x_2, 18);
x_30 = lean_ctor_get(x_2, 19);
x_31 = lean_ctor_get(x_2, 20);
x_32 = lean_ctor_get(x_2, 21);
x_33 = lean_ctor_get(x_2, 22);
x_34 = lean_ctor_get(x_2, 23);
x_35 = lean_ctor_get(x_2, 24);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_37 = lean_ctor_get(x_2, 25);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_41 = lean_box(x_39);
x_42 = lean_apply_1(x_1, x_41);
x_43 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_11);
lean_ctor_set(x_43, 3, x_12);
lean_ctor_set(x_43, 4, x_14);
lean_ctor_set(x_43, 5, x_15);
lean_ctor_set(x_43, 6, x_16);
lean_ctor_set(x_43, 7, x_17);
lean_ctor_set(x_43, 8, x_18);
lean_ctor_set(x_43, 9, x_19);
lean_ctor_set(x_43, 10, x_20);
lean_ctor_set(x_43, 11, x_21);
lean_ctor_set(x_43, 12, x_22);
lean_ctor_set(x_43, 13, x_24);
lean_ctor_set(x_43, 14, x_25);
lean_ctor_set(x_43, 15, x_26);
lean_ctor_set(x_43, 16, x_27);
lean_ctor_set(x_43, 17, x_28);
lean_ctor_set(x_43, 18, x_29);
lean_ctor_set(x_43, 19, x_30);
lean_ctor_set(x_43, 20, x_31);
lean_ctor_set(x_43, 21, x_32);
lean_ctor_set(x_43, 22, x_33);
lean_ctor_set(x_43, 23, x_34);
lean_ctor_set(x_43, 24, x_35);
lean_ctor_set(x_43, 25, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*26, x_10);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 1, x_13);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 2, x_23);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 3, x_36);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 4, x_38);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 5, x_44);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 6, x_40);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_libPrefixOnWindows___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_libPrefixOnWindows___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_allowImportAll___proj___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*26 + 6);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_PackageConfig_allowImportAll___proj___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 6, x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_36, 2, x_7);
lean_ctor_set(x_36, 3, x_8);
lean_ctor_set(x_36, 4, x_10);
lean_ctor_set(x_36, 5, x_11);
lean_ctor_set(x_36, 6, x_12);
lean_ctor_set(x_36, 7, x_13);
lean_ctor_set(x_36, 8, x_14);
lean_ctor_set(x_36, 9, x_15);
lean_ctor_set(x_36, 10, x_16);
lean_ctor_set(x_36, 11, x_17);
lean_ctor_set(x_36, 12, x_18);
lean_ctor_set(x_36, 13, x_20);
lean_ctor_set(x_36, 14, x_21);
lean_ctor_set(x_36, 15, x_22);
lean_ctor_set(x_36, 16, x_23);
lean_ctor_set(x_36, 17, x_24);
lean_ctor_set(x_36, 18, x_25);
lean_ctor_set(x_36, 19, x_26);
lean_ctor_set(x_36, 20, x_27);
lean_ctor_set(x_36, 21, x_28);
lean_ctor_set(x_36, 22, x_29);
lean_ctor_set(x_36, 23, x_30);
lean_ctor_set(x_36, 24, x_31);
lean_ctor_set(x_36, 25, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*26, x_6);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 1, x_9);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*26 + 6, x_1);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_PackageConfig_allowImportAll___proj___lam__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
x_5 = lean_box(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_ctor_set_uint8(x_2, sizeof(void*)*26 + 6, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_14 = lean_ctor_get(x_2, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_ctor_get(x_2, 6);
x_17 = lean_ctor_get(x_2, 7);
x_18 = lean_ctor_get(x_2, 8);
x_19 = lean_ctor_get(x_2, 9);
x_20 = lean_ctor_get(x_2, 10);
x_21 = lean_ctor_get(x_2, 11);
x_22 = lean_ctor_get(x_2, 12);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_24 = lean_ctor_get(x_2, 13);
x_25 = lean_ctor_get(x_2, 14);
x_26 = lean_ctor_get(x_2, 15);
x_27 = lean_ctor_get(x_2, 16);
x_28 = lean_ctor_get(x_2, 17);
x_29 = lean_ctor_get(x_2, 18);
x_30 = lean_ctor_get(x_2, 19);
x_31 = lean_ctor_get(x_2, 20);
x_32 = lean_ctor_get(x_2, 21);
x_33 = lean_ctor_get(x_2, 22);
x_34 = lean_ctor_get(x_2, 23);
x_35 = lean_ctor_get(x_2, 24);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_37 = lean_ctor_get(x_2, 25);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_41 = lean_box(x_40);
x_42 = lean_apply_1(x_1, x_41);
x_43 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_11);
lean_ctor_set(x_43, 3, x_12);
lean_ctor_set(x_43, 4, x_14);
lean_ctor_set(x_43, 5, x_15);
lean_ctor_set(x_43, 6, x_16);
lean_ctor_set(x_43, 7, x_17);
lean_ctor_set(x_43, 8, x_18);
lean_ctor_set(x_43, 9, x_19);
lean_ctor_set(x_43, 10, x_20);
lean_ctor_set(x_43, 11, x_21);
lean_ctor_set(x_43, 12, x_22);
lean_ctor_set(x_43, 13, x_24);
lean_ctor_set(x_43, 14, x_25);
lean_ctor_set(x_43, 15, x_26);
lean_ctor_set(x_43, 16, x_27);
lean_ctor_set(x_43, 17, x_28);
lean_ctor_set(x_43, 18, x_29);
lean_ctor_set(x_43, 19, x_30);
lean_ctor_set(x_43, 20, x_31);
lean_ctor_set(x_43, 21, x_32);
lean_ctor_set(x_43, 22, x_33);
lean_ctor_set(x_43, 23, x_34);
lean_ctor_set(x_43, 24, x_35);
lean_ctor_set(x_43, 25, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*26, x_10);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 1, x_13);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 2, x_23);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 3, x_36);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 4, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 5, x_39);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*26 + 6, x_44);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_allowImportAll___proj___closed__3));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_allowImportAll___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_allowImportAll___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_allowImportAll_instConfigField(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_5);
lean_ctor_set(x_37, 2, x_7);
lean_ctor_set(x_37, 3, x_8);
lean_ctor_set(x_37, 4, x_10);
lean_ctor_set(x_37, 5, x_11);
lean_ctor_set(x_37, 6, x_12);
lean_ctor_set(x_37, 7, x_13);
lean_ctor_set(x_37, 8, x_14);
lean_ctor_set(x_37, 9, x_15);
lean_ctor_set(x_37, 10, x_16);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_9);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_6);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_defaultPackagesDir;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_toWorkspaceConfig___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_toWorkspaceConfig___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_toLeanConfig___proj___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
x_29 = lean_ctor_get(x_2, 22);
x_30 = lean_ctor_get(x_2, 23);
x_31 = lean_ctor_get(x_2, 24);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_33 = lean_ctor_get(x_2, 25);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_1);
lean_ctor_set(x_37, 2, x_7);
lean_ctor_set(x_37, 3, x_8);
lean_ctor_set(x_37, 4, x_10);
lean_ctor_set(x_37, 5, x_11);
lean_ctor_set(x_37, 6, x_12);
lean_ctor_set(x_37, 7, x_13);
lean_ctor_set(x_37, 8, x_14);
lean_ctor_set(x_37, 9, x_15);
lean_ctor_set(x_37, 10, x_16);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_29);
lean_ctor_set(x_37, 23, x_30);
lean_ctor_set(x_37, 24, x_31);
lean_ctor_set(x_37, 25, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*26, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 1, x_9);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 2, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*26 + 6, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
x_22 = lean_ctor_get(x_2, 13);
x_23 = lean_ctor_get(x_2, 14);
x_24 = lean_ctor_get(x_2, 15);
x_25 = lean_ctor_get(x_2, 16);
x_26 = lean_ctor_get(x_2, 17);
x_27 = lean_ctor_get(x_2, 18);
x_28 = lean_ctor_get(x_2, 19);
x_29 = lean_ctor_get(x_2, 20);
x_30 = lean_ctor_get(x_2, 21);
x_31 = lean_ctor_get(x_2, 22);
x_32 = lean_ctor_get(x_2, 23);
x_33 = lean_ctor_get(x_2, 24);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
x_35 = lean_ctor_get(x_2, 25);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 6);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_7);
x_40 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_10);
lean_ctor_set(x_40, 4, x_12);
lean_ctor_set(x_40, 5, x_13);
lean_ctor_set(x_40, 6, x_14);
lean_ctor_set(x_40, 7, x_15);
lean_ctor_set(x_40, 8, x_16);
lean_ctor_set(x_40, 9, x_17);
lean_ctor_set(x_40, 10, x_18);
lean_ctor_set(x_40, 11, x_19);
lean_ctor_set(x_40, 12, x_20);
lean_ctor_set(x_40, 13, x_22);
lean_ctor_set(x_40, 14, x_23);
lean_ctor_set(x_40, 15, x_24);
lean_ctor_set(x_40, 16, x_25);
lean_ctor_set(x_40, 17, x_26);
lean_ctor_set(x_40, 18, x_27);
lean_ctor_set(x_40, 19, x_28);
lean_ctor_set(x_40, 20, x_29);
lean_ctor_set(x_40, 21, x_30);
lean_ctor_set(x_40, 22, x_31);
lean_ctor_set(x_40, 23, x_32);
lean_ctor_set(x_40, 24, x_33);
lean_ctor_set(x_40, 25, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*26, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 1, x_11);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 2, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 3, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*26 + 6, x_38);
return x_40;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 2;
x_3 = l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0;
x_4 = 3;
x_5 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_3);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_3);
lean_ctor_set(x_5, 9, x_3);
lean_ctor_set(x_5, 10, x_1);
lean_ctor_set(x_5, 11, x_3);
lean_ctor_set(x_5, 12, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*13, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*13 + 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_toLeanConfig___proj___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___closed__4));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_toLeanConfig_instConfigParent(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__3() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__2));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__3;
x_2 = l_Lake_PackageConfig___fields___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__7() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__6));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__7;
x_2 = l_Lake_PackageConfig___fields___closed__4;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__11() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__10));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__11;
x_2 = l_Lake_PackageConfig___fields___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__15() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__14));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__15;
x_2 = l_Lake_PackageConfig___fields___closed__12;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__19() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__18));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__19;
x_2 = l_Lake_PackageConfig___fields___closed__16;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__23));
x_2 = l_Lake_PackageConfig___fields___closed__20;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__27() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__26));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__27;
x_2 = l_Lake_PackageConfig___fields___closed__24;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__31() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__30));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__31;
x_2 = l_Lake_PackageConfig___fields___closed__28;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__35() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__34));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__35;
x_2 = l_Lake_PackageConfig___fields___closed__32;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__39() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__38));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__39;
x_2 = l_Lake_PackageConfig___fields___closed__36;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__43() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__42));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__43;
x_2 = l_Lake_PackageConfig___fields___closed__40;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__47() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__46));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__47;
x_2 = l_Lake_PackageConfig___fields___closed__44;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__51() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__50));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__51;
x_2 = l_Lake_PackageConfig___fields___closed__48;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__55));
x_2 = l_Lake_PackageConfig___fields___closed__52;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__59() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__58));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__59;
x_2 = l_Lake_PackageConfig___fields___closed__56;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__63));
x_2 = l_Lake_PackageConfig___fields___closed__60;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__67() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__66));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__67;
x_2 = l_Lake_PackageConfig___fields___closed__64;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__71() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__70));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__72() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__71;
x_2 = l_Lake_PackageConfig___fields___closed__68;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__75));
x_2 = l_Lake_PackageConfig___fields___closed__72;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__79() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__78));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__80() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__79;
x_2 = l_Lake_PackageConfig___fields___closed__76;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__83() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__82));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__84() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__83;
x_2 = l_Lake_PackageConfig___fields___closed__80;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__87() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__86));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__88() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__87;
x_2 = l_Lake_PackageConfig___fields___closed__84;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__91() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__90));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__92() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__91;
x_2 = l_Lake_PackageConfig___fields___closed__88;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__95() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__94));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__96() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__95;
x_2 = l_Lake_PackageConfig___fields___closed__92;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__99() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__98));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__100() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__99;
x_2 = l_Lake_PackageConfig___fields___closed__96;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__103() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__102));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__104() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__103;
x_2 = l_Lake_PackageConfig___fields___closed__100;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__107() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__106));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__108() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__107;
x_2 = l_Lake_PackageConfig___fields___closed__104;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__111() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__110));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__112() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__111;
x_2 = l_Lake_PackageConfig___fields___closed__108;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__115() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__114));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__116() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__115;
x_2 = l_Lake_PackageConfig___fields___closed__112;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__119() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__118));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__120() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__119;
x_2 = l_Lake_PackageConfig___fields___closed__116;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__123() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__122));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__124() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__123;
x_2 = l_Lake_PackageConfig___fields___closed__120;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__127() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__126));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__128() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__127;
x_2 = l_Lake_PackageConfig___fields___closed__124;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__132() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__131));
x_2 = l_Lake_PackageConfig___fields___closed__128;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__135() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__134));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__136() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__135;
x_2 = l_Lake_PackageConfig___fields___closed__132;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__139() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__138));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__140() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__139;
x_2 = l_Lake_PackageConfig___fields___closed__136;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__143() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__142));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__144() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__143;
x_2 = l_Lake_PackageConfig___fields___closed__140;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__145() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_WorkspaceConfig___fields;
x_2 = l_Lake_PackageConfig___fields___closed__144;
x_3 = l_Array_append___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__148() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = 0;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__147));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__149() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__148;
x_2 = l_Lake_PackageConfig___fields___closed__145;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__150() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanConfig___fields;
x_2 = l_Lake_PackageConfig___fields___closed__149;
x_3 = l_Array_append___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__153() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = 0;
x_3 = ((lean_object*)(l_Lake_PackageConfig___fields___closed__152));
x_4 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__154() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig___fields___closed__153;
x_2 = l_Lake_PackageConfig___fields___closed__150;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageConfig___fields___closed__154;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig___fields;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_instConfigFields(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_PackageConfig___fields;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_PackageConfig_instConfigInfo___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__13() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_PackageConfig_instConfigInfo___closed__0;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lake_PackageConfig_instConfigInfo___closed__14() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_PackageConfig_instConfigInfo___closed__0;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__15() {
_start:
{
lean_object* x_1; size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(1);
x_2 = l_Lake_PackageConfig_instConfigInfo___closed__14;
x_3 = 0;
x_4 = l_Lake_PackageConfig___fields;
x_5 = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__12));
x_6 = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__10));
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_5, x_4, x_3, x_2, x_1);
return x_7;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_6; uint8_t x_7; 
x_1 = l_Lake_PackageConfig___fields;
x_6 = lean_box(1);
x_7 = l_Lake_PackageConfig_instConfigInfo___closed__11;
if (x_7 == 0)
{
x_2 = x_6;
goto block_5;
}
else
{
uint8_t x_8; 
x_8 = l_Lake_PackageConfig_instConfigInfo___closed__13;
if (x_8 == 0)
{
if (x_7 == 0)
{
x_2 = x_6;
goto block_5;
}
else
{
lean_object* x_9; 
x_9 = l_Lake_PackageConfig_instConfigInfo___closed__15;
x_2 = x_9;
goto block_5;
}
}
else
{
lean_object* x_10; 
x_10 = l_Lake_PackageConfig_instConfigInfo___closed__15;
x_2 = x_10;
goto block_5;
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___lam__3___closed__0));
x_3 = l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__2;
x_4 = l_Lake_defaultVersionTags;
x_5 = ((lean_object*)(l_Lake_PackageConfig_version___proj___lam__3___closed__1));
x_6 = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
x_7 = l_Lake_defaultIrDir;
x_8 = l_Lake_defaultBinDir;
x_9 = l_Lake_defaultNativeLibDir;
x_10 = l_Lake_defaultLeanLibDir;
x_11 = l_Lake_defaultBuildDir;
x_12 = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___lam__3___closed__0));
x_13 = l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0;
x_14 = lean_box(0);
x_15 = 0;
x_16 = l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1;
x_17 = l_Lake_defaultPackagesDir;
x_18 = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_13);
lean_ctor_set(x_18, 5, x_12);
lean_ctor_set(x_18, 6, x_11);
lean_ctor_set(x_18, 7, x_10);
lean_ctor_set(x_18, 8, x_9);
lean_ctor_set(x_18, 9, x_8);
lean_ctor_set(x_18, 10, x_7);
lean_ctor_set(x_18, 11, x_14);
lean_ctor_set(x_18, 12, x_14);
lean_ctor_set(x_18, 13, x_6);
lean_ctor_set(x_18, 14, x_13);
lean_ctor_set(x_18, 15, x_6);
lean_ctor_set(x_18, 16, x_13);
lean_ctor_set(x_18, 17, x_5);
lean_ctor_set(x_18, 18, x_4);
lean_ctor_set(x_18, 19, x_6);
lean_ctor_set(x_18, 20, x_13);
lean_ctor_set(x_18, 21, x_6);
lean_ctor_set(x_18, 22, x_6);
lean_ctor_set(x_18, 23, x_3);
lean_ctor_set(x_18, 24, x_2);
lean_ctor_set(x_18, 25, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*26, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*26 + 1, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*26 + 2, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*26 + 3, x_1);
lean_ctor_set_uint8(x_18, sizeof(void*)*26 + 4, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*26 + 5, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*26 + 6, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_instEmptyCollection___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_instEmptyCollection(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_origName___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_PackageConfig_origName(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
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
l_Lake_instInhabitedPackageConfig_default___closed__0 = _init_l_Lake_instInhabitedPackageConfig_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedPackageConfig_default___closed__0);
l_Lake_instInhabitedPackageConfig_default___closed__2 = _init_l_Lake_instInhabitedPackageConfig_default___closed__2();
lean_mark_persistent(l_Lake_instInhabitedPackageConfig_default___closed__2);
l_Lake_instInhabitedPackageConfig_default___closed__3 = _init_l_Lake_instInhabitedPackageConfig_default___closed__3();
lean_mark_persistent(l_Lake_instInhabitedPackageConfig_default___closed__3);
l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0 = _init_l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0();
lean_mark_persistent(l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0);
l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0 = _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0();
lean_mark_persistent(l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0);
l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1 = _init_l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1();
lean_mark_persistent(l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1);
l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__2 = _init_l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__2();
lean_mark_persistent(l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__2);
l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0 = _init_l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0();
lean_mark_persistent(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0);
l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1 = _init_l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1();
lean_mark_persistent(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1);
l_Lake_PackageConfig___fields___closed__0 = _init_l_Lake_PackageConfig___fields___closed__0();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__0);
l_Lake_PackageConfig___fields___closed__3 = _init_l_Lake_PackageConfig___fields___closed__3();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__3);
l_Lake_PackageConfig___fields___closed__4 = _init_l_Lake_PackageConfig___fields___closed__4();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__4);
l_Lake_PackageConfig___fields___closed__7 = _init_l_Lake_PackageConfig___fields___closed__7();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__7);
l_Lake_PackageConfig___fields___closed__8 = _init_l_Lake_PackageConfig___fields___closed__8();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__8);
l_Lake_PackageConfig___fields___closed__11 = _init_l_Lake_PackageConfig___fields___closed__11();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__11);
l_Lake_PackageConfig___fields___closed__12 = _init_l_Lake_PackageConfig___fields___closed__12();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__12);
l_Lake_PackageConfig___fields___closed__15 = _init_l_Lake_PackageConfig___fields___closed__15();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__15);
l_Lake_PackageConfig___fields___closed__16 = _init_l_Lake_PackageConfig___fields___closed__16();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__16);
l_Lake_PackageConfig___fields___closed__19 = _init_l_Lake_PackageConfig___fields___closed__19();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__19);
l_Lake_PackageConfig___fields___closed__20 = _init_l_Lake_PackageConfig___fields___closed__20();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__20);
l_Lake_PackageConfig___fields___closed__24 = _init_l_Lake_PackageConfig___fields___closed__24();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__24);
l_Lake_PackageConfig___fields___closed__27 = _init_l_Lake_PackageConfig___fields___closed__27();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__27);
l_Lake_PackageConfig___fields___closed__28 = _init_l_Lake_PackageConfig___fields___closed__28();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__28);
l_Lake_PackageConfig___fields___closed__31 = _init_l_Lake_PackageConfig___fields___closed__31();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__31);
l_Lake_PackageConfig___fields___closed__32 = _init_l_Lake_PackageConfig___fields___closed__32();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__32);
l_Lake_PackageConfig___fields___closed__35 = _init_l_Lake_PackageConfig___fields___closed__35();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__35);
l_Lake_PackageConfig___fields___closed__36 = _init_l_Lake_PackageConfig___fields___closed__36();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__36);
l_Lake_PackageConfig___fields___closed__39 = _init_l_Lake_PackageConfig___fields___closed__39();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__39);
l_Lake_PackageConfig___fields___closed__40 = _init_l_Lake_PackageConfig___fields___closed__40();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__40);
l_Lake_PackageConfig___fields___closed__43 = _init_l_Lake_PackageConfig___fields___closed__43();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__43);
l_Lake_PackageConfig___fields___closed__44 = _init_l_Lake_PackageConfig___fields___closed__44();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__44);
l_Lake_PackageConfig___fields___closed__47 = _init_l_Lake_PackageConfig___fields___closed__47();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__47);
l_Lake_PackageConfig___fields___closed__48 = _init_l_Lake_PackageConfig___fields___closed__48();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__48);
l_Lake_PackageConfig___fields___closed__51 = _init_l_Lake_PackageConfig___fields___closed__51();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__51);
l_Lake_PackageConfig___fields___closed__52 = _init_l_Lake_PackageConfig___fields___closed__52();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__52);
l_Lake_PackageConfig___fields___closed__56 = _init_l_Lake_PackageConfig___fields___closed__56();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__56);
l_Lake_PackageConfig___fields___closed__59 = _init_l_Lake_PackageConfig___fields___closed__59();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__59);
l_Lake_PackageConfig___fields___closed__60 = _init_l_Lake_PackageConfig___fields___closed__60();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__60);
l_Lake_PackageConfig___fields___closed__64 = _init_l_Lake_PackageConfig___fields___closed__64();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__64);
l_Lake_PackageConfig___fields___closed__67 = _init_l_Lake_PackageConfig___fields___closed__67();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__67);
l_Lake_PackageConfig___fields___closed__68 = _init_l_Lake_PackageConfig___fields___closed__68();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__68);
l_Lake_PackageConfig___fields___closed__71 = _init_l_Lake_PackageConfig___fields___closed__71();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__71);
l_Lake_PackageConfig___fields___closed__72 = _init_l_Lake_PackageConfig___fields___closed__72();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__72);
l_Lake_PackageConfig___fields___closed__76 = _init_l_Lake_PackageConfig___fields___closed__76();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__76);
l_Lake_PackageConfig___fields___closed__79 = _init_l_Lake_PackageConfig___fields___closed__79();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__79);
l_Lake_PackageConfig___fields___closed__80 = _init_l_Lake_PackageConfig___fields___closed__80();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__80);
l_Lake_PackageConfig___fields___closed__83 = _init_l_Lake_PackageConfig___fields___closed__83();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__83);
l_Lake_PackageConfig___fields___closed__84 = _init_l_Lake_PackageConfig___fields___closed__84();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__84);
l_Lake_PackageConfig___fields___closed__87 = _init_l_Lake_PackageConfig___fields___closed__87();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__87);
l_Lake_PackageConfig___fields___closed__88 = _init_l_Lake_PackageConfig___fields___closed__88();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__88);
l_Lake_PackageConfig___fields___closed__91 = _init_l_Lake_PackageConfig___fields___closed__91();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__91);
l_Lake_PackageConfig___fields___closed__92 = _init_l_Lake_PackageConfig___fields___closed__92();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__92);
l_Lake_PackageConfig___fields___closed__95 = _init_l_Lake_PackageConfig___fields___closed__95();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__95);
l_Lake_PackageConfig___fields___closed__96 = _init_l_Lake_PackageConfig___fields___closed__96();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__96);
l_Lake_PackageConfig___fields___closed__99 = _init_l_Lake_PackageConfig___fields___closed__99();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__99);
l_Lake_PackageConfig___fields___closed__100 = _init_l_Lake_PackageConfig___fields___closed__100();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__100);
l_Lake_PackageConfig___fields___closed__103 = _init_l_Lake_PackageConfig___fields___closed__103();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__103);
l_Lake_PackageConfig___fields___closed__104 = _init_l_Lake_PackageConfig___fields___closed__104();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__104);
l_Lake_PackageConfig___fields___closed__107 = _init_l_Lake_PackageConfig___fields___closed__107();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__107);
l_Lake_PackageConfig___fields___closed__108 = _init_l_Lake_PackageConfig___fields___closed__108();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__108);
l_Lake_PackageConfig___fields___closed__111 = _init_l_Lake_PackageConfig___fields___closed__111();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__111);
l_Lake_PackageConfig___fields___closed__112 = _init_l_Lake_PackageConfig___fields___closed__112();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__112);
l_Lake_PackageConfig___fields___closed__115 = _init_l_Lake_PackageConfig___fields___closed__115();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__115);
l_Lake_PackageConfig___fields___closed__116 = _init_l_Lake_PackageConfig___fields___closed__116();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__116);
l_Lake_PackageConfig___fields___closed__119 = _init_l_Lake_PackageConfig___fields___closed__119();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__119);
l_Lake_PackageConfig___fields___closed__120 = _init_l_Lake_PackageConfig___fields___closed__120();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__120);
l_Lake_PackageConfig___fields___closed__123 = _init_l_Lake_PackageConfig___fields___closed__123();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__123);
l_Lake_PackageConfig___fields___closed__124 = _init_l_Lake_PackageConfig___fields___closed__124();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__124);
l_Lake_PackageConfig___fields___closed__127 = _init_l_Lake_PackageConfig___fields___closed__127();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__127);
l_Lake_PackageConfig___fields___closed__128 = _init_l_Lake_PackageConfig___fields___closed__128();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__128);
l_Lake_PackageConfig___fields___closed__132 = _init_l_Lake_PackageConfig___fields___closed__132();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__132);
l_Lake_PackageConfig___fields___closed__135 = _init_l_Lake_PackageConfig___fields___closed__135();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__135);
l_Lake_PackageConfig___fields___closed__136 = _init_l_Lake_PackageConfig___fields___closed__136();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__136);
l_Lake_PackageConfig___fields___closed__139 = _init_l_Lake_PackageConfig___fields___closed__139();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__139);
l_Lake_PackageConfig___fields___closed__140 = _init_l_Lake_PackageConfig___fields___closed__140();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__140);
l_Lake_PackageConfig___fields___closed__143 = _init_l_Lake_PackageConfig___fields___closed__143();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__143);
l_Lake_PackageConfig___fields___closed__144 = _init_l_Lake_PackageConfig___fields___closed__144();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__144);
l_Lake_PackageConfig___fields___closed__145 = _init_l_Lake_PackageConfig___fields___closed__145();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__145);
l_Lake_PackageConfig___fields___closed__148 = _init_l_Lake_PackageConfig___fields___closed__148();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__148);
l_Lake_PackageConfig___fields___closed__149 = _init_l_Lake_PackageConfig___fields___closed__149();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__149);
l_Lake_PackageConfig___fields___closed__150 = _init_l_Lake_PackageConfig___fields___closed__150();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__150);
l_Lake_PackageConfig___fields___closed__153 = _init_l_Lake_PackageConfig___fields___closed__153();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__153);
l_Lake_PackageConfig___fields___closed__154 = _init_l_Lake_PackageConfig___fields___closed__154();
lean_mark_persistent(l_Lake_PackageConfig___fields___closed__154);
l_Lake_PackageConfig___fields = _init_l_Lake_PackageConfig___fields();
lean_mark_persistent(l_Lake_PackageConfig___fields);
l_Lake_PackageConfig_instConfigInfo___closed__0 = _init_l_Lake_PackageConfig_instConfigInfo___closed__0();
lean_mark_persistent(l_Lake_PackageConfig_instConfigInfo___closed__0);
l_Lake_PackageConfig_instConfigInfo___closed__11 = _init_l_Lake_PackageConfig_instConfigInfo___closed__11();
l_Lake_PackageConfig_instConfigInfo___closed__13 = _init_l_Lake_PackageConfig_instConfigInfo___closed__13();
l_Lake_PackageConfig_instConfigInfo___closed__14 = _init_l_Lake_PackageConfig_instConfigInfo___closed__14();
l_Lake_PackageConfig_instConfigInfo___closed__15 = _init_l_Lake_PackageConfig_instConfigInfo___closed__15();
lean_mark_persistent(l_Lake_PackageConfig_instConfigInfo___closed__15);
l_Lake_PackageConfig_instConfigInfo = _init_l_Lake_PackageConfig_instConfigInfo();
lean_mark_persistent(l_Lake_PackageConfig_instConfigInfo);
l_Lake_PackageConfig_instEmptyCollection___closed__0 = _init_l_Lake_PackageConfig_instEmptyCollection___closed__0();
lean_mark_persistent(l_Lake_PackageConfig_instEmptyCollection___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
