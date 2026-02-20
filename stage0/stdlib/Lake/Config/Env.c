// Lean compiler output
// Module: Lake.Config.Env
// Imports: public import Lake.Config.Cache public import Lake.Config.InstallPath import Init.System.Platform
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
static const lean_string_object l_Lake_instInhabitedEnv_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedEnv_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedEnv_default___closed__0_value;
extern lean_object* l_Lake_instInhabitedLeanInstall_default;
extern lean_object* l_Lake_instInhabitedLakeInstall_default;
static lean_object* l_Lake_instInhabitedEnv_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedEnv_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedEnv;
static const lean_string_object l_Lake_getUserHome_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HOME"};
static const lean_object* l_Lake_getUserHome_x3f___closed__0 = (const lean_object*)&l_Lake_getUserHome_x3f___closed__0_value;
static const lean_string_object l_Lake_getUserHome_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "HOMEDRIVE"};
static const lean_object* l_Lake_getUserHome_x3f___closed__1 = (const lean_object*)&l_Lake_getUserHome_x3f___closed__1_value;
static const lean_string_object l_Lake_getUserHome_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HOMEPATH"};
static const lean_object* l_Lake_getUserHome_x3f___closed__2 = (const lean_object*)&l_Lake_getUserHome_x3f___closed__2_value;
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f();
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "XDG_CACHE_HOME"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0_value;
static const lean_string_object l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ".cache"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1_value;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f();
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0_value;
static const lean_string_object l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1_value;
lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Env_computeToolchain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ELAN_TOOLCHAIN"};
static const lean_object* l_Lake_Env_computeToolchain___closed__0 = (const lean_object*)&l_Lake_Env_computeToolchain___closed__0_value;
extern lean_object* l_Lean_toolchain;
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain();
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain___boxed(lean_object*);
static const lean_string_object l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LAKE_CACHE_DIR"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f();
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfSystem_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "expected a `Name`, got '"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected a `NameMap`, got '"};
static const lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0 = (const lean_object*)&l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0_value;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(lean_object*);
static const lean_string_object l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LAKE_PKG_URL_MAP"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0_value;
static const lean_string_object l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "'LAKE_PKG_URL_MAP' has invalid JSON: "};
static const lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1_value;
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___boxed(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute___lam__0(lean_object*);
static const lean_string_object l_Lake_Env_compute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "RESERVOIR_API_BASE_URL"};
static const lean_object* l_Lake_Env_compute___closed__0 = (const lean_object*)&l_Lake_Env_compute___closed__0_value;
static const lean_string_object l_Lake_Env_compute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".lake"};
static const lean_object* l_Lake_Env_compute___closed__1 = (const lean_object*)&l_Lake_Env_compute___closed__1_value;
static const lean_string_object l_Lake_Env_compute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "config.toml"};
static const lean_object* l_Lake_Env_compute___closed__2 = (const lean_object*)&l_Lake_Env_compute___closed__2_value;
static const lean_string_object l_Lake_Env_compute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LAKE_NO_CACHE"};
static const lean_object* l_Lake_Env_compute___closed__3 = (const lean_object*)&l_Lake_Env_compute___closed__3_value;
static const lean_string_object l_Lake_Env_compute___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "LAKE_ARTIFACT_CACHE"};
static const lean_object* l_Lake_Env_compute___closed__4 = (const lean_object*)&l_Lake_Env_compute___closed__4_value;
static const lean_string_object l_Lake_Env_compute___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "LAKE_CONFIG"};
static const lean_object* l_Lake_Env_compute___closed__5 = (const lean_object*)&l_Lake_Env_compute___closed__5_value;
static const lean_string_object l_Lake_Env_compute___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LAKE_CACHE_KEY"};
static const lean_object* l_Lake_Env_compute___closed__6 = (const lean_object*)&l_Lake_Env_compute___closed__6_value;
static const lean_string_object l_Lake_Env_compute___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "LAKE_CACHE_ARTIFACT_ENDPOINT"};
static const lean_object* l_Lake_Env_compute___closed__7 = (const lean_object*)&l_Lake_Env_compute___closed__7_value;
static const lean_string_object l_Lake_Env_compute___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "LAKE_CACHE_REVISION_ENDPOINT"};
static const lean_object* l_Lake_Env_compute___closed__8 = (const lean_object*)&l_Lake_Env_compute___closed__8_value;
static const lean_string_object l_Lake_Env_compute___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LAKE_CACHE_SERVICE"};
static const lean_object* l_Lake_Env_compute___closed__9 = (const lean_object*)&l_Lake_Env_compute___closed__9_value;
static const lean_string_object l_Lake_Env_compute___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_GITHASH"};
static const lean_object* l_Lake_Env_compute___closed__10 = (const lean_object*)&l_Lake_Env_compute___closed__10_value;
static const lean_string_object l_Lake_Env_compute___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LEAN_PATH"};
static const lean_object* l_Lake_Env_compute___closed__11 = (const lean_object*)&l_Lake_Env_compute___closed__11_value;
static const lean_string_object l_Lake_Env_compute___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LEAN_SRC_PATH"};
static const lean_object* l_Lake_Env_compute___closed__12 = (const lean_object*)&l_Lake_Env_compute___closed__12_value;
static const lean_string_object l_Lake_Env_compute___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PATH"};
static const lean_object* l_Lake_Env_compute___closed__13 = (const lean_object*)&l_Lake_Env_compute___closed__13_value;
static const lean_string_object l_Lake_Env_compute___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "RESERVOIR_API_URL"};
static const lean_object* l_Lake_Env_compute___closed__14 = (const lean_object*)&l_Lake_Env_compute___closed__14_value;
static const lean_string_object l_Lake_Env_compute___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "/v1"};
static const lean_object* l_Lake_Env_compute___closed__15 = (const lean_object*)&l_Lake_Env_compute___closed__15_value;
static const lean_string_object l_Lake_Env_compute___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "https://reservoir.lean-lang.org/api"};
static const lean_object* l_Lake_Env_compute___closed__16 = (const lean_object*)&l_Lake_Env_compute___closed__16_value;
lean_object* l_Lake_envToBool_x3f(lean_object*);
lean_object* l_Lake_getSearchPath(lean_object*);
extern lean_object* l_Lake_sharedLibPathEnvVar;
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object*);
lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object*);
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_computeToolchain___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__0 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__0_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LAKE"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__1 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__1_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__2 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__2_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LAKE_OVERRIDE_LEAN"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__3 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__3_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__4 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__4_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LAKE_HOME"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__5 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__5_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__6 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__6_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LEAN"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__7 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__7_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__8 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__8_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_compute___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__9 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__9_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_SYSROOT"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__10 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__10_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__11 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__11_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LEAN_AR"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__12 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__12_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__13 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__13_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__14;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__15;
static lean_object* l_Lake_Env_noToolchainVars___closed__16;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instInhabitedEnv_default___closed__0_value)}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__17 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__17_value;
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6_value;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(lean_object*);
static const lean_string_object l_Lake_Env_baseVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LEAN_CC"};
static const lean_object* l_Lake_Env_baseVars___closed__0 = (const lean_object*)&l_Lake_Env_baseVars___closed__0_value;
static lean_object* l_Lake_Env_baseVars___closed__1;
static const lean_string_object l_Lake_Env_baseVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_Env_baseVars___closed__2 = (const lean_object*)&l_Lake_Env_baseVars___closed__2_value;
static const lean_string_object l_Lake_Env_baseVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_Env_baseVars___closed__3 = (const lean_object*)&l_Lake_Env_baseVars___closed__3_value;
static const lean_string_object l_Lake_Env_baseVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ELAN"};
static const lean_object* l_Lake_Env_baseVars___closed__4 = (const lean_object*)&l_Lake_Env_baseVars___closed__4_value;
static const lean_string_object l_Lake_Env_baseVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ELAN_HOME"};
static const lean_object* l_Lake_Env_baseVars___closed__5 = (const lean_object*)&l_Lake_Env_baseVars___closed__5_value;
lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_Env_vars___closed__0;
static const lean_ctor_object l_Lake_Env_vars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Env_baseVars___closed__2_value)}};
static const lean_object* l_Lake_Env_vars___closed__1 = (const lean_object*)&l_Lake_Env_vars___closed__1_value;
static const lean_ctor_object l_Lake_Env_vars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Env_baseVars___closed__3_value)}};
static const lean_object* l_Lake_Env_vars___closed__2 = (const lean_object*)&l_Lake_Env_vars___closed__2_value;
lean_object* l_System_SearchPath_toString(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object*);
static lean_object* _init_l_Lake_instInhabitedEnv_default___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(1);
x_4 = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
x_5 = lean_box(0);
x_6 = l_Lake_instInhabitedLeanInstall_default;
x_7 = l_Lake_instInhabitedLakeInstall_default;
x_8 = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_4);
lean_ctor_set(x_8, 5, x_3);
lean_ctor_set(x_8, 6, x_5);
lean_ctor_set(x_8, 7, x_5);
lean_ctor_set(x_8, 8, x_5);
lean_ctor_set(x_8, 9, x_5);
lean_ctor_set(x_8, 10, x_5);
lean_ctor_set(x_8, 11, x_5);
lean_ctor_set(x_8, 12, x_5);
lean_ctor_set(x_8, 13, x_5);
lean_ctor_set(x_8, 14, x_1);
lean_ctor_set(x_8, 15, x_1);
lean_ctor_set(x_8, 16, x_1);
lean_ctor_set(x_8, 17, x_1);
lean_ctor_set(x_8, 18, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*19, x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*19 + 1, x_2);
return x_8;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedEnv_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedEnv_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f() {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_Lake_getUserHome_x3f___closed__0));
x_4 = lean_io_getenv(x_3);
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = ((lean_object*)(l_Lake_getUserHome_x3f___closed__1));
x_10 = lean_io_getenv(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l_Lake_getUserHome_x3f___closed__2));
x_13 = lean_io_getenv(x_12);
if (lean_obj_tag(x_13) == 1)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_string_append(x_11, x_15);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_string_append(x_11, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_11);
x_20 = lean_box(0);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_10);
x_21 = lean_box(0);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getUserHome_x3f();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0));
x_4 = lean_io_getenv(x_3);
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
x_11 = l_System_FilePath_join(x_9, x_10);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
x_14 = l_System_FilePath_join(x_12, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0));
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = l_Lake_getUserHome_x3f();
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
x_11 = l_System_FilePath_join(x_9, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
x_14 = l_System_FilePath_join(x_12, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_7);
x_16 = lean_box(0);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getSystemCacheHome_x3f();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(x_2, x_4, x_5);
x_7 = l_System_FilePath_join(x_3, x_6);
x_8 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_9 = l_System_FilePath_join(x_7, x_8);
x_10 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1));
x_11 = l_System_FilePath_join(x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_1, x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lake_Env_computeToolchain___closed__0));
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_toolchain;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_computeToolchain();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_free_object(x_3);
lean_dec(x_6);
x_10 = lean_box(0);
return x_10;
}
else
{
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_string_utf8_byte_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfSystem_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_6 = l_System_FilePath_join(x_4, x_5);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_9 = l_System_FilePath_join(x_7, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_string_utf8_byte_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_5, x_2);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_10; 
lean_free_object(x_1);
lean_dec(x_5);
x_10 = lean_box(0);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_string_utf8_byte_size(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_11, x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_11);
x_17 = lean_box(0);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_8; lean_object* x_15; lean_object* x_16; 
x_15 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
x_16 = lean_io_getenv(x_15);
if (lean_obj_tag(x_16) == 0)
{
goto block_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec_ref(x_16);
x_24 = lean_string_utf8_byte_size(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_dec(x_23);
goto block_22;
}
else
{
lean_dec(x_1);
x_4 = x_23;
x_5 = lean_box(0);
goto block_7;
}
}
block_7:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
block_14:
{
lean_object* x_9; 
x_9 = l_Lake_getSystemCacheHome_x3f();
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_13 = l_System_FilePath_join(x_11, x_12);
x_4 = x_13;
x_5 = lean_box(0);
goto block_7;
}
}
block_22:
{
if (lean_obj_tag(x_1) == 0)
{
x_8 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_string_utf8_byte_size(x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_17, x_2);
x_4 = x_21;
x_5 = lean_box(0);
goto block_7;
}
else
{
lean_dec(x_17);
x_8 = lean_box(0);
goto block_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Env_computeCache_x3f(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
x_7 = lean_io_getenv(x_6);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_69; 
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_7);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_7, 0);
x_71 = lean_string_utf8_byte_size(x_70);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_eq(x_71, x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_4);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_4, 8);
lean_dec(x_75);
x_76 = lean_ctor_get(x_4, 7);
lean_dec(x_76);
lean_inc_ref(x_7);
lean_ctor_set(x_4, 8, x_7);
lean_ctor_set(x_4, 7, x_7);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_4);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_78 = lean_ctor_get(x_4, 0);
x_79 = lean_ctor_get(x_4, 1);
x_80 = lean_ctor_get(x_4, 2);
x_81 = lean_ctor_get(x_4, 3);
x_82 = lean_ctor_get(x_4, 4);
x_83 = lean_ctor_get(x_4, 5);
x_84 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_85 = lean_ctor_get(x_4, 6);
x_86 = lean_ctor_get_uint8(x_4, sizeof(void*)*19 + 1);
x_87 = lean_ctor_get(x_4, 9);
x_88 = lean_ctor_get(x_4, 10);
x_89 = lean_ctor_get(x_4, 11);
x_90 = lean_ctor_get(x_4, 12);
x_91 = lean_ctor_get(x_4, 13);
x_92 = lean_ctor_get(x_4, 14);
x_93 = lean_ctor_get(x_4, 15);
x_94 = lean_ctor_get(x_4, 16);
x_95 = lean_ctor_get(x_4, 17);
x_96 = lean_ctor_get(x_4, 18);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_85);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_4);
lean_inc_ref(x_7);
x_97 = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(x_97, 0, x_78);
lean_ctor_set(x_97, 1, x_79);
lean_ctor_set(x_97, 2, x_80);
lean_ctor_set(x_97, 3, x_81);
lean_ctor_set(x_97, 4, x_82);
lean_ctor_set(x_97, 5, x_83);
lean_ctor_set(x_97, 6, x_85);
lean_ctor_set(x_97, 7, x_7);
lean_ctor_set(x_97, 8, x_7);
lean_ctor_set(x_97, 9, x_87);
lean_ctor_set(x_97, 10, x_88);
lean_ctor_set(x_97, 11, x_89);
lean_ctor_set(x_97, 12, x_90);
lean_ctor_set(x_97, 13, x_91);
lean_ctor_set(x_97, 14, x_92);
lean_ctor_set(x_97, 15, x_93);
lean_ctor_set(x_97, 16, x_94);
lean_ctor_set(x_97, 17, x_95);
lean_ctor_set(x_97, 18, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*19, x_84);
lean_ctor_set_uint8(x_97, sizeof(void*)*19 + 1, x_86);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_free_object(x_7);
lean_dec(x_70);
x_99 = !lean_is_exclusive(x_4);
if (x_99 == 0)
{
lean_object* x_100; 
lean_ctor_set_uint8(x_4, sizeof(void*)*19 + 1, x_73);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_4);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_101 = lean_ctor_get(x_4, 0);
x_102 = lean_ctor_get(x_4, 1);
x_103 = lean_ctor_get(x_4, 2);
x_104 = lean_ctor_get(x_4, 3);
x_105 = lean_ctor_get(x_4, 4);
x_106 = lean_ctor_get(x_4, 5);
x_107 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_108 = lean_ctor_get(x_4, 6);
x_109 = lean_ctor_get(x_4, 7);
x_110 = lean_ctor_get(x_4, 8);
x_111 = lean_ctor_get(x_4, 9);
x_112 = lean_ctor_get(x_4, 10);
x_113 = lean_ctor_get(x_4, 11);
x_114 = lean_ctor_get(x_4, 12);
x_115 = lean_ctor_get(x_4, 13);
x_116 = lean_ctor_get(x_4, 14);
x_117 = lean_ctor_get(x_4, 15);
x_118 = lean_ctor_get(x_4, 16);
x_119 = lean_ctor_get(x_4, 17);
x_120 = lean_ctor_get(x_4, 18);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_4);
x_121 = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(x_121, 0, x_101);
lean_ctor_set(x_121, 1, x_102);
lean_ctor_set(x_121, 2, x_103);
lean_ctor_set(x_121, 3, x_104);
lean_ctor_set(x_121, 4, x_105);
lean_ctor_set(x_121, 5, x_106);
lean_ctor_set(x_121, 6, x_108);
lean_ctor_set(x_121, 7, x_109);
lean_ctor_set(x_121, 8, x_110);
lean_ctor_set(x_121, 9, x_111);
lean_ctor_set(x_121, 10, x_112);
lean_ctor_set(x_121, 11, x_113);
lean_ctor_set(x_121, 12, x_114);
lean_ctor_set(x_121, 13, x_115);
lean_ctor_set(x_121, 14, x_116);
lean_ctor_set(x_121, 15, x_117);
lean_ctor_set(x_121, 16, x_118);
lean_ctor_set(x_121, 17, x_119);
lean_ctor_set(x_121, 18, x_120);
lean_ctor_set_uint8(x_121, sizeof(void*)*19, x_107);
lean_ctor_set_uint8(x_121, sizeof(void*)*19 + 1, x_73);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = lean_ctor_get(x_7, 0);
lean_inc(x_123);
lean_dec(x_7);
x_124 = lean_string_utf8_byte_size(x_123);
x_125 = lean_unsigned_to_nat(0u);
x_126 = lean_nat_dec_eq(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_127 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_4, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_4, 5);
lean_inc(x_132);
x_133 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_134 = lean_ctor_get(x_4, 6);
lean_inc(x_134);
x_135 = lean_ctor_get_uint8(x_4, sizeof(void*)*19 + 1);
x_136 = lean_ctor_get(x_4, 9);
lean_inc(x_136);
x_137 = lean_ctor_get(x_4, 10);
lean_inc(x_137);
x_138 = lean_ctor_get(x_4, 11);
lean_inc(x_138);
x_139 = lean_ctor_get(x_4, 12);
lean_inc(x_139);
x_140 = lean_ctor_get(x_4, 13);
lean_inc(x_140);
x_141 = lean_ctor_get(x_4, 14);
lean_inc(x_141);
x_142 = lean_ctor_get(x_4, 15);
lean_inc(x_142);
x_143 = lean_ctor_get(x_4, 16);
lean_inc(x_143);
x_144 = lean_ctor_get(x_4, 17);
lean_inc(x_144);
x_145 = lean_ctor_get(x_4, 18);
lean_inc_ref(x_145);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 lean_ctor_release(x_4, 10);
 lean_ctor_release(x_4, 11);
 lean_ctor_release(x_4, 12);
 lean_ctor_release(x_4, 13);
 lean_ctor_release(x_4, 14);
 lean_ctor_release(x_4, 15);
 lean_ctor_release(x_4, 16);
 lean_ctor_release(x_4, 17);
 lean_ctor_release(x_4, 18);
 x_146 = x_4;
} else {
 lean_dec_ref(x_4);
 x_146 = lean_box(0);
}
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_123);
lean_inc_ref(x_147);
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 19, 2);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_127);
lean_ctor_set(x_148, 1, x_128);
lean_ctor_set(x_148, 2, x_129);
lean_ctor_set(x_148, 3, x_130);
lean_ctor_set(x_148, 4, x_131);
lean_ctor_set(x_148, 5, x_132);
lean_ctor_set(x_148, 6, x_134);
lean_ctor_set(x_148, 7, x_147);
lean_ctor_set(x_148, 8, x_147);
lean_ctor_set(x_148, 9, x_136);
lean_ctor_set(x_148, 10, x_137);
lean_ctor_set(x_148, 11, x_138);
lean_ctor_set(x_148, 12, x_139);
lean_ctor_set(x_148, 13, x_140);
lean_ctor_set(x_148, 14, x_141);
lean_ctor_set(x_148, 15, x_142);
lean_ctor_set(x_148, 16, x_143);
lean_ctor_set(x_148, 17, x_144);
lean_ctor_set(x_148, 18, x_145);
lean_ctor_set_uint8(x_148, sizeof(void*)*19, x_133);
lean_ctor_set_uint8(x_148, sizeof(void*)*19 + 1, x_135);
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_123);
x_150 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_151);
x_152 = lean_ctor_get(x_4, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_153);
x_154 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_154);
x_155 = lean_ctor_get(x_4, 5);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_157 = lean_ctor_get(x_4, 6);
lean_inc(x_157);
x_158 = lean_ctor_get(x_4, 7);
lean_inc(x_158);
x_159 = lean_ctor_get(x_4, 8);
lean_inc(x_159);
x_160 = lean_ctor_get(x_4, 9);
lean_inc(x_160);
x_161 = lean_ctor_get(x_4, 10);
lean_inc(x_161);
x_162 = lean_ctor_get(x_4, 11);
lean_inc(x_162);
x_163 = lean_ctor_get(x_4, 12);
lean_inc(x_163);
x_164 = lean_ctor_get(x_4, 13);
lean_inc(x_164);
x_165 = lean_ctor_get(x_4, 14);
lean_inc(x_165);
x_166 = lean_ctor_get(x_4, 15);
lean_inc(x_166);
x_167 = lean_ctor_get(x_4, 16);
lean_inc(x_167);
x_168 = lean_ctor_get(x_4, 17);
lean_inc(x_168);
x_169 = lean_ctor_get(x_4, 18);
lean_inc_ref(x_169);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 lean_ctor_release(x_4, 10);
 lean_ctor_release(x_4, 11);
 lean_ctor_release(x_4, 12);
 lean_ctor_release(x_4, 13);
 lean_ctor_release(x_4, 14);
 lean_ctor_release(x_4, 15);
 lean_ctor_release(x_4, 16);
 lean_ctor_release(x_4, 17);
 lean_ctor_release(x_4, 18);
 x_170 = x_4;
} else {
 lean_dec_ref(x_4);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 19, 2);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_150);
lean_ctor_set(x_171, 1, x_151);
lean_ctor_set(x_171, 2, x_152);
lean_ctor_set(x_171, 3, x_153);
lean_ctor_set(x_171, 4, x_154);
lean_ctor_set(x_171, 5, x_155);
lean_ctor_set(x_171, 6, x_157);
lean_ctor_set(x_171, 7, x_158);
lean_ctor_set(x_171, 8, x_159);
lean_ctor_set(x_171, 9, x_160);
lean_ctor_set(x_171, 10, x_161);
lean_ctor_set(x_171, 11, x_162);
lean_ctor_set(x_171, 12, x_163);
lean_ctor_set(x_171, 13, x_164);
lean_ctor_set(x_171, 14, x_165);
lean_ctor_set(x_171, 15, x_166);
lean_ctor_set(x_171, 16, x_167);
lean_ctor_set(x_171, 17, x_168);
lean_ctor_set(x_171, 18, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*19, x_156);
lean_ctor_set_uint8(x_171, sizeof(void*)*19 + 1, x_126);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
}
}
else
{
lean_dec(x_7);
if (lean_obj_tag(x_1) == 0)
{
goto block_68;
}
else
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_1);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_174 = lean_ctor_get(x_1, 0);
x_175 = lean_string_utf8_byte_size(x_3);
x_176 = lean_unsigned_to_nat(0u);
x_177 = lean_nat_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(x_2);
x_179 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_174, x_3);
lean_ctor_set(x_1, 0, x_179);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_207; 
x_207 = lean_box(0);
x_180 = x_207;
goto block_206;
}
else
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_178);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_178, 0);
x_210 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_211 = l_System_FilePath_join(x_209, x_210);
lean_ctor_set(x_178, 0, x_211);
x_180 = x_178;
goto block_206;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_178, 0);
lean_inc(x_212);
lean_dec(x_178);
x_213 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_214 = l_System_FilePath_join(x_212, x_213);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_180 = x_215;
goto block_206;
}
}
block_206:
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_4);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_4, 8);
lean_dec(x_182);
x_183 = lean_ctor_get(x_4, 7);
lean_dec(x_183);
lean_ctor_set(x_4, 8, x_180);
lean_ctor_set(x_4, 7, x_1);
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_4);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_185 = lean_ctor_get(x_4, 0);
x_186 = lean_ctor_get(x_4, 1);
x_187 = lean_ctor_get(x_4, 2);
x_188 = lean_ctor_get(x_4, 3);
x_189 = lean_ctor_get(x_4, 4);
x_190 = lean_ctor_get(x_4, 5);
x_191 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_192 = lean_ctor_get(x_4, 6);
x_193 = lean_ctor_get_uint8(x_4, sizeof(void*)*19 + 1);
x_194 = lean_ctor_get(x_4, 9);
x_195 = lean_ctor_get(x_4, 10);
x_196 = lean_ctor_get(x_4, 11);
x_197 = lean_ctor_get(x_4, 12);
x_198 = lean_ctor_get(x_4, 13);
x_199 = lean_ctor_get(x_4, 14);
x_200 = lean_ctor_get(x_4, 15);
x_201 = lean_ctor_get(x_4, 16);
x_202 = lean_ctor_get(x_4, 17);
x_203 = lean_ctor_get(x_4, 18);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_192);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_4);
x_204 = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(x_204, 0, x_185);
lean_ctor_set(x_204, 1, x_186);
lean_ctor_set(x_204, 2, x_187);
lean_ctor_set(x_204, 3, x_188);
lean_ctor_set(x_204, 4, x_189);
lean_ctor_set(x_204, 5, x_190);
lean_ctor_set(x_204, 6, x_192);
lean_ctor_set(x_204, 7, x_1);
lean_ctor_set(x_204, 8, x_180);
lean_ctor_set(x_204, 9, x_194);
lean_ctor_set(x_204, 10, x_195);
lean_ctor_set(x_204, 11, x_196);
lean_ctor_set(x_204, 12, x_197);
lean_ctor_set(x_204, 13, x_198);
lean_ctor_set(x_204, 14, x_199);
lean_ctor_set(x_204, 15, x_200);
lean_ctor_set(x_204, 16, x_201);
lean_ctor_set(x_204, 17, x_202);
lean_ctor_set(x_204, 18, x_203);
lean_ctor_set_uint8(x_204, sizeof(void*)*19, x_191);
lean_ctor_set_uint8(x_204, sizeof(void*)*19 + 1, x_193);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
}
else
{
lean_free_object(x_1);
lean_dec(x_174);
goto block_68;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_216 = lean_ctor_get(x_1, 0);
lean_inc(x_216);
lean_dec(x_1);
x_217 = lean_string_utf8_byte_size(x_3);
x_218 = lean_unsigned_to_nat(0u);
x_219 = lean_nat_dec_eq(x_217, x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(x_2);
x_221 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_216, x_3);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_247; 
x_247 = lean_box(0);
x_223 = x_247;
goto block_246;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_220, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_249 = x_220;
} else {
 lean_dec_ref(x_220);
 x_249 = lean_box(0);
}
x_250 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_251 = l_System_FilePath_join(x_248, x_250);
if (lean_is_scalar(x_249)) {
 x_252 = lean_alloc_ctor(1, 1, 0);
} else {
 x_252 = x_249;
}
lean_ctor_set(x_252, 0, x_251);
x_223 = x_252;
goto block_246;
}
block_246:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_224 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_224);
x_225 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_225);
x_226 = lean_ctor_get(x_4, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_228);
x_229 = lean_ctor_get(x_4, 5);
lean_inc(x_229);
x_230 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_231 = lean_ctor_get(x_4, 6);
lean_inc(x_231);
x_232 = lean_ctor_get_uint8(x_4, sizeof(void*)*19 + 1);
x_233 = lean_ctor_get(x_4, 9);
lean_inc(x_233);
x_234 = lean_ctor_get(x_4, 10);
lean_inc(x_234);
x_235 = lean_ctor_get(x_4, 11);
lean_inc(x_235);
x_236 = lean_ctor_get(x_4, 12);
lean_inc(x_236);
x_237 = lean_ctor_get(x_4, 13);
lean_inc(x_237);
x_238 = lean_ctor_get(x_4, 14);
lean_inc(x_238);
x_239 = lean_ctor_get(x_4, 15);
lean_inc(x_239);
x_240 = lean_ctor_get(x_4, 16);
lean_inc(x_240);
x_241 = lean_ctor_get(x_4, 17);
lean_inc(x_241);
x_242 = lean_ctor_get(x_4, 18);
lean_inc_ref(x_242);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 lean_ctor_release(x_4, 10);
 lean_ctor_release(x_4, 11);
 lean_ctor_release(x_4, 12);
 lean_ctor_release(x_4, 13);
 lean_ctor_release(x_4, 14);
 lean_ctor_release(x_4, 15);
 lean_ctor_release(x_4, 16);
 lean_ctor_release(x_4, 17);
 lean_ctor_release(x_4, 18);
 x_243 = x_4;
} else {
 lean_dec_ref(x_4);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 19, 2);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_224);
lean_ctor_set(x_244, 1, x_225);
lean_ctor_set(x_244, 2, x_226);
lean_ctor_set(x_244, 3, x_227);
lean_ctor_set(x_244, 4, x_228);
lean_ctor_set(x_244, 5, x_229);
lean_ctor_set(x_244, 6, x_231);
lean_ctor_set(x_244, 7, x_222);
lean_ctor_set(x_244, 8, x_223);
lean_ctor_set(x_244, 9, x_233);
lean_ctor_set(x_244, 10, x_234);
lean_ctor_set(x_244, 11, x_235);
lean_ctor_set(x_244, 12, x_236);
lean_ctor_set(x_244, 13, x_237);
lean_ctor_set(x_244, 14, x_238);
lean_ctor_set(x_244, 15, x_239);
lean_ctor_set(x_244, 16, x_240);
lean_ctor_set(x_244, 17, x_241);
lean_ctor_set(x_244, 18, x_242);
lean_ctor_set_uint8(x_244, sizeof(void*)*19, x_230);
lean_ctor_set_uint8(x_244, sizeof(void*)*19 + 1, x_232);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_244);
return x_245;
}
}
else
{
lean_dec(x_216);
goto block_68;
}
}
}
}
block_68:
{
lean_object* x_8; 
x_8 = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_4, 8);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 7);
lean_dec(x_14);
x_15 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_16 = l_System_FilePath_join(x_12, x_15);
lean_ctor_set(x_8, 0, x_16);
lean_inc_ref(x_8);
lean_ctor_set(x_4, 8, x_8);
lean_ctor_set(x_4, 7, x_8);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_ctor_get(x_4, 2);
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 4);
x_24 = lean_ctor_get(x_4, 5);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_26 = lean_ctor_get(x_4, 6);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*19 + 1);
x_28 = lean_ctor_get(x_4, 9);
x_29 = lean_ctor_get(x_4, 10);
x_30 = lean_ctor_get(x_4, 11);
x_31 = lean_ctor_get(x_4, 12);
x_32 = lean_ctor_get(x_4, 13);
x_33 = lean_ctor_get(x_4, 14);
x_34 = lean_ctor_get(x_4, 15);
x_35 = lean_ctor_get(x_4, 16);
x_36 = lean_ctor_get(x_4, 17);
x_37 = lean_ctor_get(x_4, 18);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_38 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_39 = l_System_FilePath_join(x_18, x_38);
lean_ctor_set(x_8, 0, x_39);
lean_inc_ref(x_8);
x_40 = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_20);
lean_ctor_set(x_40, 2, x_21);
lean_ctor_set(x_40, 3, x_22);
lean_ctor_set(x_40, 4, x_23);
lean_ctor_set(x_40, 5, x_24);
lean_ctor_set(x_40, 6, x_26);
lean_ctor_set(x_40, 7, x_8);
lean_ctor_set(x_40, 8, x_8);
lean_ctor_set(x_40, 9, x_28);
lean_ctor_set(x_40, 10, x_29);
lean_ctor_set(x_40, 11, x_30);
lean_ctor_set(x_40, 12, x_31);
lean_ctor_set(x_40, 13, x_32);
lean_ctor_set(x_40, 14, x_33);
lean_ctor_set(x_40, 15, x_34);
lean_ctor_set(x_40, 16, x_35);
lean_ctor_set(x_40, 17, x_36);
lean_ctor_set(x_40, 18, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*19, x_25);
lean_ctor_set_uint8(x_40, sizeof(void*)*19 + 1, x_27);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_42 = lean_ctor_get(x_8, 0);
lean_inc(x_42);
lean_dec(x_8);
x_43 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_4, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_4, 5);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_50 = lean_ctor_get(x_4, 6);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_4, sizeof(void*)*19 + 1);
x_52 = lean_ctor_get(x_4, 9);
lean_inc(x_52);
x_53 = lean_ctor_get(x_4, 10);
lean_inc(x_53);
x_54 = lean_ctor_get(x_4, 11);
lean_inc(x_54);
x_55 = lean_ctor_get(x_4, 12);
lean_inc(x_55);
x_56 = lean_ctor_get(x_4, 13);
lean_inc(x_56);
x_57 = lean_ctor_get(x_4, 14);
lean_inc(x_57);
x_58 = lean_ctor_get(x_4, 15);
lean_inc(x_58);
x_59 = lean_ctor_get(x_4, 16);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 17);
lean_inc(x_60);
x_61 = lean_ctor_get(x_4, 18);
lean_inc_ref(x_61);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 lean_ctor_release(x_4, 10);
 lean_ctor_release(x_4, 11);
 lean_ctor_release(x_4, 12);
 lean_ctor_release(x_4, 13);
 lean_ctor_release(x_4, 14);
 lean_ctor_release(x_4, 15);
 lean_ctor_release(x_4, 16);
 lean_ctor_release(x_4, 17);
 lean_ctor_release(x_4, 18);
 x_62 = x_4;
} else {
 lean_dec_ref(x_4);
 x_62 = lean_box(0);
}
x_63 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_64 = l_System_FilePath_join(x_42, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_inc_ref(x_65);
if (lean_is_scalar(x_62)) {
 x_66 = lean_alloc_ctor(0, 19, 2);
} else {
 x_66 = x_62;
}
lean_ctor_set(x_66, 0, x_43);
lean_ctor_set(x_66, 1, x_44);
lean_ctor_set(x_66, 2, x_45);
lean_ctor_set(x_66, 3, x_46);
lean_ctor_set(x_66, 4, x_47);
lean_ctor_set(x_66, 5, x_48);
lean_ctor_set(x_66, 6, x_50);
lean_ctor_set(x_66, 7, x_65);
lean_ctor_set(x_66, 8, x_65);
lean_ctor_set(x_66, 9, x_52);
lean_ctor_set(x_66, 10, x_53);
lean_ctor_set(x_66, 11, x_54);
lean_ctor_set(x_66, 12, x_55);
lean_ctor_set(x_66, 13, x_56);
lean_ctor_set(x_66, 14, x_57);
lean_ctor_set(x_66, 15, x_58);
lean_ctor_set(x_66, 16, x_59);
lean_ctor_set(x_66, 17, x_60);
lean_ctor_set(x_66, 18, x_61);
lean_ctor_set_uint8(x_66, sizeof(void*)*19, x_49);
lean_ctor_set_uint8(x_66, sizeof(void*)*19 + 1, x_51);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0));
x_11 = lean_string_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
x_12 = l_String_toName(x_3);
x_13 = l_Lean_Name_isAnonymous(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_free_object(x_7);
lean_dec(x_3);
x_14 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec_ref(x_14);
x_19 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_12, x_18, x_9);
x_1 = x_19;
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_21 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1));
x_22 = lean_string_append(x_21, x_3);
lean_dec(x_3);
x_23 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
x_24 = lean_string_append(x_22, x_23);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
else
{
lean_object* x_25; 
lean_free_object(x_7);
lean_dec(x_3);
x_25 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec_ref(x_25);
x_30 = lean_box(0);
x_31 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_30, x_29, x_9);
x_1 = x_31;
x_2 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
lean_dec(x_7);
x_34 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0));
x_35 = lean_string_dec_eq(x_3, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_inc(x_3);
x_36 = l_String_toName(x_3);
x_37 = l_Lean_Name_isAnonymous(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_3);
x_38 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_6);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec_ref(x_38);
x_43 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_36, x_42, x_33);
x_1 = x_43;
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_4);
x_45 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1));
x_46 = lean_string_append(x_45, x_3);
lean_dec(x_3);
x_47 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_3);
x_50 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_33);
lean_dec(x_6);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
lean_dec_ref(x_50);
x_55 = lean_box(0);
x_56 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_55, x_54, x_33);
x_1 = x_56;
x_2 = x_6;
goto _start;
}
}
}
}
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_1);
return x_58;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_box(1);
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0));
x_6 = lean_unsigned_to_nat(80u);
x_7 = l_Lean_Json_pretty(x_1, x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0));
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = l_Lean_Json_parse(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_4 = x_11;
goto block_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_4 = x_14;
goto block_8;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_ctor_set_tag(x_13, 0);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
block_8:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1));
x_6 = lean_string_append(x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_String_Slice_Pos_prev_x3f(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint32_t x_16; 
lean_dec_ref(x_14);
x_16 = 65;
x_2 = x_16;
goto block_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_String_Slice_Pos_get_x3f(x_14, x_17);
lean_dec(x_17);
lean_dec_ref(x_14);
if (lean_obj_tag(x_18) == 0)
{
uint32_t x_19; 
x_19 = 65;
x_2 = x_19;
goto block_11;
}
else
{
lean_object* x_20; uint32_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_unbox_uint32(x_20);
lean_dec(x_20);
x_2 = x_21;
goto block_11;
}
}
block_11:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 47;
x_4 = lean_uint32_dec_eq(x_2, x_3);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_String_Slice_Pos_prevn(x_8, x_7, x_5);
lean_dec_ref(x_8);
x_10 = lean_string_utf8_extract(x_1, x_6, x_9);
lean_dec(x_9);
lean_dec_ref(x_1);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_trimAscii(x_4);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_string_utf8_extract(x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_276; 
x_28 = ((lean_object*)(l_Lake_Env_compute___closed__0));
x_29 = lean_io_getenv(x_28);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_29, 0);
lean_inc(x_291);
lean_dec_ref(x_29);
x_292 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_291);
x_276 = x_292;
goto block_290;
}
else
{
lean_object* x_293; 
lean_dec(x_29);
x_293 = ((lean_object*)(l_Lake_Env_compute___closed__16));
x_276 = x_293;
goto block_290;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_15);
lean_inc(x_11);
lean_inc(x_3);
x_25 = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set(x_25, 2, x_3);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_8);
lean_ctor_set(x_25, 5, x_10);
lean_ctor_set(x_25, 6, x_19);
lean_ctor_set(x_25, 7, x_11);
lean_ctor_set(x_25, 8, x_11);
lean_ctor_set(x_25, 9, x_14);
lean_ctor_set(x_25, 10, x_20);
lean_ctor_set(x_25, 11, x_18);
lean_ctor_set(x_25, 12, x_16);
lean_ctor_set(x_25, 13, x_24);
lean_ctor_set(x_25, 14, x_21);
lean_ctor_set(x_25, 15, x_23);
lean_ctor_set(x_25, 16, x_9);
lean_ctor_set(x_25, 17, x_12);
lean_ctor_set(x_25, 18, x_15);
lean_ctor_set_uint8(x_25, sizeof(void*)*19, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*19 + 1, x_13);
x_26 = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(x_3, x_7, x_15, x_25);
lean_dec_ref(x_15);
return x_26;
}
block_55:
{
if (lean_obj_tag(x_35) == 0)
{
x_6 = lean_box(0);
x_7 = x_31;
x_8 = x_32;
x_9 = x_33;
x_10 = x_34;
x_11 = x_36;
x_12 = x_37;
x_13 = x_38;
x_14 = x_39;
x_15 = x_40;
x_16 = x_48;
x_17 = x_41;
x_18 = x_42;
x_19 = x_43;
x_20 = x_45;
x_21 = x_44;
x_22 = x_46;
x_23 = x_47;
x_24 = x_35;
goto block_27;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = l_Lake_Env_compute___lam__0(x_50);
lean_ctor_set(x_35, 0, x_51);
x_6 = lean_box(0);
x_7 = x_31;
x_8 = x_32;
x_9 = x_33;
x_10 = x_34;
x_11 = x_36;
x_12 = x_37;
x_13 = x_38;
x_14 = x_39;
x_15 = x_40;
x_16 = x_48;
x_17 = x_41;
x_18 = x_42;
x_19 = x_43;
x_20 = x_45;
x_21 = x_44;
x_22 = x_46;
x_23 = x_47;
x_24 = x_35;
goto block_27;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_35, 0);
lean_inc(x_52);
lean_dec(x_35);
x_53 = l_Lake_Env_compute___lam__0(x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_6 = lean_box(0);
x_7 = x_31;
x_8 = x_32;
x_9 = x_33;
x_10 = x_34;
x_11 = x_36;
x_12 = x_37;
x_13 = x_38;
x_14 = x_39;
x_15 = x_40;
x_16 = x_48;
x_17 = x_41;
x_18 = x_42;
x_19 = x_43;
x_20 = x_45;
x_21 = x_44;
x_22 = x_46;
x_23 = x_47;
x_24 = x_54;
goto block_27;
}
}
}
block_81:
{
if (lean_obj_tag(x_68) == 0)
{
x_30 = lean_box(0);
x_31 = x_57;
x_32 = x_58;
x_33 = x_59;
x_34 = x_60;
x_35 = x_61;
x_36 = x_62;
x_37 = x_63;
x_38 = x_64;
x_39 = x_65;
x_40 = x_66;
x_41 = x_67;
x_42 = x_74;
x_43 = x_69;
x_44 = x_71;
x_45 = x_70;
x_46 = x_72;
x_47 = x_73;
x_48 = x_68;
goto block_55;
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_68);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_68, 0);
x_77 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_76);
lean_ctor_set(x_68, 0, x_77);
x_30 = lean_box(0);
x_31 = x_57;
x_32 = x_58;
x_33 = x_59;
x_34 = x_60;
x_35 = x_61;
x_36 = x_62;
x_37 = x_63;
x_38 = x_64;
x_39 = x_65;
x_40 = x_66;
x_41 = x_67;
x_42 = x_74;
x_43 = x_69;
x_44 = x_71;
x_45 = x_70;
x_46 = x_72;
x_47 = x_73;
x_48 = x_68;
goto block_55;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_68, 0);
lean_inc(x_78);
lean_dec(x_68);
x_79 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_30 = lean_box(0);
x_31 = x_57;
x_32 = x_58;
x_33 = x_59;
x_34 = x_60;
x_35 = x_61;
x_36 = x_62;
x_37 = x_63;
x_38 = x_64;
x_39 = x_65;
x_40 = x_66;
x_41 = x_67;
x_42 = x_74;
x_43 = x_69;
x_44 = x_71;
x_45 = x_70;
x_46 = x_72;
x_47 = x_73;
x_48 = x_80;
goto block_55;
}
}
}
block_107:
{
if (lean_obj_tag(x_82) == 0)
{
x_56 = lean_box(0);
x_57 = x_84;
x_58 = x_85;
x_59 = x_86;
x_60 = x_87;
x_61 = x_88;
x_62 = x_89;
x_63 = x_90;
x_64 = x_91;
x_65 = x_92;
x_66 = x_93;
x_67 = x_94;
x_68 = x_95;
x_69 = x_96;
x_70 = x_100;
x_71 = x_97;
x_72 = x_98;
x_73 = x_99;
x_74 = x_82;
goto block_81;
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_82);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_82, 0);
x_103 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_102);
lean_ctor_set(x_82, 0, x_103);
x_56 = lean_box(0);
x_57 = x_84;
x_58 = x_85;
x_59 = x_86;
x_60 = x_87;
x_61 = x_88;
x_62 = x_89;
x_63 = x_90;
x_64 = x_91;
x_65 = x_92;
x_66 = x_93;
x_67 = x_94;
x_68 = x_95;
x_69 = x_96;
x_70 = x_100;
x_71 = x_97;
x_72 = x_98;
x_73 = x_99;
x_74 = x_82;
goto block_81;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_82, 0);
lean_inc(x_104);
lean_dec(x_82);
x_105 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_56 = lean_box(0);
x_57 = x_84;
x_58 = x_85;
x_59 = x_86;
x_60 = x_87;
x_61 = x_88;
x_62 = x_89;
x_63 = x_90;
x_64 = x_91;
x_65 = x_92;
x_66 = x_93;
x_67 = x_94;
x_68 = x_95;
x_69 = x_96;
x_70 = x_100;
x_71 = x_97;
x_72 = x_98;
x_73 = x_99;
x_74 = x_106;
goto block_81;
}
}
}
block_133:
{
if (lean_obj_tag(x_116) == 0)
{
x_82 = x_108;
x_83 = lean_box(0);
x_84 = x_110;
x_85 = x_111;
x_86 = x_112;
x_87 = x_113;
x_88 = x_114;
x_89 = x_115;
x_90 = x_117;
x_91 = x_118;
x_92 = x_126;
x_93 = x_119;
x_94 = x_120;
x_95 = x_121;
x_96 = x_122;
x_97 = x_123;
x_98 = x_124;
x_99 = x_125;
x_100 = x_116;
goto block_107;
}
else
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_116);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_116, 0);
x_129 = l_Lake_Env_compute___lam__0(x_128);
lean_ctor_set(x_116, 0, x_129);
x_82 = x_108;
x_83 = lean_box(0);
x_84 = x_110;
x_85 = x_111;
x_86 = x_112;
x_87 = x_113;
x_88 = x_114;
x_89 = x_115;
x_90 = x_117;
x_91 = x_118;
x_92 = x_126;
x_93 = x_119;
x_94 = x_120;
x_95 = x_121;
x_96 = x_122;
x_97 = x_123;
x_98 = x_124;
x_99 = x_125;
x_100 = x_116;
goto block_107;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_116, 0);
lean_inc(x_130);
lean_dec(x_116);
x_131 = l_Lake_Env_compute___lam__0(x_130);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_82 = x_108;
x_83 = lean_box(0);
x_84 = x_110;
x_85 = x_111;
x_86 = x_112;
x_87 = x_113;
x_88 = x_114;
x_89 = x_115;
x_90 = x_117;
x_91 = x_118;
x_92 = x_126;
x_93 = x_119;
x_94 = x_120;
x_95 = x_121;
x_96 = x_122;
x_97 = x_123;
x_98 = x_124;
x_99 = x_125;
x_100 = x_132;
goto block_107;
}
}
}
block_154:
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_108 = x_134;
x_109 = lean_box(0);
x_110 = x_136;
x_111 = x_137;
x_112 = x_138;
x_113 = x_139;
x_114 = x_140;
x_115 = x_141;
x_116 = x_142;
x_117 = x_143;
x_118 = x_144;
x_119 = x_145;
x_120 = x_146;
x_121 = x_147;
x_122 = x_148;
x_123 = x_149;
x_124 = x_150;
x_125 = x_151;
x_126 = x_153;
goto block_133;
}
block_180:
{
uint8_t x_172; lean_object* x_173; 
x_172 = 0;
x_173 = lean_box(0);
if (lean_obj_tag(x_166) == 0)
{
if (lean_obj_tag(x_157) == 0)
{
x_108 = x_155;
x_109 = lean_box(0);
x_110 = x_157;
x_111 = x_158;
x_112 = x_159;
x_113 = x_160;
x_114 = x_161;
x_115 = x_173;
x_116 = x_162;
x_117 = x_163;
x_118 = x_172;
x_119 = x_164;
x_120 = x_165;
x_121 = x_167;
x_122 = x_171;
x_123 = x_168;
x_124 = x_169;
x_125 = x_170;
x_126 = x_157;
goto block_133;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_157, 0);
x_175 = ((lean_object*)(l_Lake_Env_compute___closed__1));
lean_inc(x_174);
x_176 = l_System_FilePath_join(x_174, x_175);
x_177 = ((lean_object*)(l_Lake_Env_compute___closed__2));
x_178 = l_System_FilePath_join(x_176, x_177);
x_134 = x_155;
x_135 = lean_box(0);
x_136 = x_157;
x_137 = x_158;
x_138 = x_159;
x_139 = x_160;
x_140 = x_161;
x_141 = x_173;
x_142 = x_162;
x_143 = x_163;
x_144 = x_172;
x_145 = x_164;
x_146 = x_165;
x_147 = x_167;
x_148 = x_171;
x_149 = x_168;
x_150 = x_169;
x_151 = x_170;
x_152 = x_178;
goto block_154;
}
}
else
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_166, 0);
lean_inc(x_179);
lean_dec_ref(x_166);
x_134 = x_155;
x_135 = lean_box(0);
x_136 = x_157;
x_137 = x_158;
x_138 = x_159;
x_139 = x_160;
x_140 = x_161;
x_141 = x_173;
x_142 = x_162;
x_143 = x_163;
x_144 = x_172;
x_145 = x_164;
x_146 = x_165;
x_147 = x_167;
x_148 = x_171;
x_149 = x_168;
x_150 = x_169;
x_151 = x_170;
x_152 = x_179;
goto block_154;
}
}
block_201:
{
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_198; 
x_198 = lean_box(0);
x_155 = x_181;
x_156 = lean_box(0);
x_157 = x_183;
x_158 = x_184;
x_159 = x_186;
x_160 = x_187;
x_161 = x_188;
x_162 = x_189;
x_163 = x_190;
x_164 = x_191;
x_165 = x_197;
x_166 = x_192;
x_167 = x_193;
x_168 = x_194;
x_169 = x_195;
x_170 = x_196;
x_171 = x_198;
goto block_180;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_185, 0);
lean_inc(x_199);
lean_dec_ref(x_185);
x_200 = l_Lake_envToBool_x3f(x_199);
x_155 = x_181;
x_156 = lean_box(0);
x_157 = x_183;
x_158 = x_184;
x_159 = x_186;
x_160 = x_187;
x_161 = x_188;
x_162 = x_189;
x_163 = x_190;
x_164 = x_191;
x_165 = x_197;
x_166 = x_192;
x_167 = x_193;
x_168 = x_194;
x_169 = x_195;
x_170 = x_196;
x_171 = x_200;
goto block_180;
}
}
block_219:
{
uint8_t x_218; 
x_218 = 0;
x_181 = x_202;
x_182 = lean_box(0);
x_183 = x_204;
x_184 = x_205;
x_185 = x_206;
x_186 = x_207;
x_187 = x_208;
x_188 = x_209;
x_189 = x_210;
x_190 = x_211;
x_191 = x_212;
x_192 = x_213;
x_193 = x_214;
x_194 = x_215;
x_195 = x_216;
x_196 = x_217;
x_197 = x_218;
goto block_201;
}
block_243:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_221) == 0)
{
x_202 = x_220;
x_203 = lean_box(0);
x_204 = x_223;
x_205 = x_236;
x_206 = x_224;
x_207 = x_225;
x_208 = x_226;
x_209 = x_227;
x_210 = x_228;
x_211 = x_229;
x_212 = x_230;
x_213 = x_231;
x_214 = x_232;
x_215 = x_233;
x_216 = x_234;
x_217 = x_235;
goto block_219;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_221, 0);
lean_inc(x_237);
lean_dec_ref(x_221);
x_238 = l_Lake_envToBool_x3f(x_237);
if (lean_obj_tag(x_238) == 0)
{
x_202 = x_220;
x_203 = lean_box(0);
x_204 = x_223;
x_205 = x_236;
x_206 = x_224;
x_207 = x_225;
x_208 = x_226;
x_209 = x_227;
x_210 = x_228;
x_211 = x_229;
x_212 = x_230;
x_213 = x_231;
x_214 = x_232;
x_215 = x_233;
x_216 = x_234;
x_217 = x_235;
goto block_219;
}
else
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = lean_unbox(x_239);
lean_dec(x_239);
x_181 = x_220;
x_182 = lean_box(0);
x_183 = x_223;
x_184 = x_236;
x_185 = x_224;
x_186 = x_225;
x_187 = x_226;
x_188 = x_227;
x_189 = x_228;
x_190 = x_229;
x_191 = x_230;
x_192 = x_231;
x_193 = x_232;
x_194 = x_233;
x_195 = x_234;
x_196 = x_235;
x_197 = x_240;
goto block_201;
}
}
}
else
{
lean_object* x_241; uint8_t x_242; 
lean_dec(x_221);
x_241 = lean_ctor_get(x_4, 0);
x_242 = lean_unbox(x_241);
x_181 = x_220;
x_182 = lean_box(0);
x_183 = x_223;
x_184 = x_236;
x_185 = x_224;
x_186 = x_225;
x_187 = x_226;
x_188 = x_227;
x_189 = x_228;
x_190 = x_229;
x_191 = x_230;
x_192 = x_231;
x_193 = x_232;
x_194 = x_233;
x_195 = x_234;
x_196 = x_235;
x_197 = x_242;
goto block_201;
}
}
block_275:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_249 = ((lean_object*)(l_Lake_Env_compute___closed__3));
x_250 = lean_io_getenv(x_249);
x_251 = ((lean_object*)(l_Lake_Env_compute___closed__4));
x_252 = lean_io_getenv(x_251);
x_253 = ((lean_object*)(l_Lake_Env_compute___closed__5));
x_254 = lean_io_getenv(x_253);
x_255 = ((lean_object*)(l_Lake_Env_compute___closed__6));
x_256 = lean_io_getenv(x_255);
x_257 = ((lean_object*)(l_Lake_Env_compute___closed__7));
x_258 = lean_io_getenv(x_257);
x_259 = ((lean_object*)(l_Lake_Env_compute___closed__8));
x_260 = lean_io_getenv(x_259);
x_261 = ((lean_object*)(l_Lake_Env_compute___closed__9));
x_262 = lean_io_getenv(x_261);
x_263 = ((lean_object*)(l_Lake_Env_compute___closed__10));
x_264 = lean_io_getenv(x_263);
x_265 = ((lean_object*)(l_Lake_Env_compute___closed__11));
x_266 = l_Lake_getSearchPath(x_265);
x_267 = ((lean_object*)(l_Lake_Env_compute___closed__12));
x_268 = l_Lake_getSearchPath(x_267);
x_269 = l_Lake_sharedLibPathEnvVar;
x_270 = l_Lake_getSearchPath(x_269);
x_271 = ((lean_object*)(l_Lake_Env_compute___closed__13));
x_272 = l_Lake_getSearchPath(x_271);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_273; 
x_273 = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
x_220 = x_258;
x_221 = x_250;
x_222 = lean_box(0);
x_223 = x_245;
x_224 = x_252;
x_225 = x_270;
x_226 = x_246;
x_227 = x_262;
x_228 = x_256;
x_229 = x_272;
x_230 = x_244;
x_231 = x_254;
x_232 = x_260;
x_233 = x_266;
x_234 = x_247;
x_235 = x_268;
x_236 = x_273;
goto block_243;
}
else
{
lean_object* x_274; 
x_274 = lean_ctor_get(x_264, 0);
lean_inc(x_274);
lean_dec_ref(x_264);
x_220 = x_258;
x_221 = x_250;
x_222 = lean_box(0);
x_223 = x_245;
x_224 = x_252;
x_225 = x_270;
x_226 = x_246;
x_227 = x_262;
x_228 = x_256;
x_229 = x_272;
x_230 = x_244;
x_231 = x_254;
x_232 = x_260;
x_233 = x_266;
x_234 = x_247;
x_235 = x_268;
x_236 = x_274;
goto block_243;
}
}
block_290:
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = l_Lake_Env_computeToolchain();
x_278 = l_Lake_getUserHome_x3f();
x_279 = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
lean_dec_ref(x_279);
x_281 = ((lean_object*)(l_Lake_Env_compute___closed__14));
x_282 = lean_io_getenv(x_281);
if (lean_obj_tag(x_282) == 1)
{
lean_object* x_283; lean_object* x_284; 
lean_dec_ref(x_276);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
lean_dec_ref(x_282);
x_284 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_283);
x_244 = x_277;
x_245 = x_278;
x_246 = x_280;
x_247 = x_284;
x_248 = lean_box(0);
goto block_275;
}
else
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_282);
x_285 = ((lean_object*)(l_Lake_Env_compute___closed__15));
x_286 = lean_string_append(x_276, x_285);
x_244 = x_277;
x_245 = x_278;
x_246 = x_280;
x_247 = x_286;
x_248 = lean_box(0);
goto block_275;
}
}
else
{
uint8_t x_287; 
lean_dec(x_278);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_287 = !lean_is_exclusive(x_279);
if (x_287 == 0)
{
return x_279;
}
else
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_279, 0);
lean_inc(x_288);
lean_dec(x_279);
x_289 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_289, 0, x_288);
return x_289;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Env_compute(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_inc_ref(x_3);
return x_3;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanGithash(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 17);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_3, 6);
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
lean_inc_ref(x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_4);
lean_inc_ref(x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_inc(x_4);
lean_inc_ref(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_path(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 14);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanPath(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 15);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanSrcPath(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 16);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lake_LeanInstall_sharedLibPath(x_2);
lean_dec_ref(x_2);
x_5 = l_List_appendTR___redArg(x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__0));
x_2 = l_Lake_Env_noToolchainVars___closed__14;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__2));
x_2 = l_Lake_Env_noToolchainVars___closed__15;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*19 + 1);
x_3 = lean_ctor_get(x_1, 8);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
x_5 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
if (x_2 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
x_6 = x_4;
goto block_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_6 = x_3;
goto block_22;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_6 = x_25;
goto block_22;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_3);
x_26 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__17));
x_6 = x_26;
goto block_22;
}
block_22:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__4));
x_9 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__6));
x_10 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__8));
x_11 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__9));
x_12 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__11));
x_13 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__13));
x_14 = l_Lake_Env_noToolchainVars___closed__16;
x_15 = lean_array_push(x_14, x_7);
x_16 = lean_array_push(x_15, x_8);
x_17 = lean_array_push(x_16, x_9);
x_18 = lean_array_push(x_17, x_10);
x_19 = lean_array_push(x_18, x_11);
x_20 = lean_array_push(x_19, x_12);
x_21 = lean_array_push(x_20, x_13);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(1);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2));
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_unsigned_to_nat(276u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2));
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(277u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6));
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_unsigned_to_nat(182u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6));
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(183u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = lean_string_dec_lt(x_1, x_5);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_string_dec_eq(x_1, x_5);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(x_1, x_2, x_8);
if (lean_obj_tag(x_7) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 4);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_mul(x_19, x_13);
x_21 = lean_nat_dec_lt(x_20, x_14);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_22, x_13);
x_24 = lean_nat_add(x_23, x_14);
lean_dec(x_14);
lean_dec(x_23);
if (lean_is_scalar(x_9)) {
 x_25 = lean_alloc_ctor(0, 5, 0);
} else {
 x_25 = x_9;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_6);
lean_ctor_set(x_25, 3, x_7);
lean_ctor_set(x_25, 4, x_12);
return x_25;
}
else
{
lean_object* x_26; 
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_26 = x_12;
} else {
 lean_dec_ref(x_12);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
x_29 = lean_ctor_get(x_17, 2);
x_30 = lean_ctor_get(x_17, 3);
x_31 = lean_ctor_get(x_17, 4);
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_mul(x_33, x_32);
x_35 = lean_nat_dec_lt(x_27, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_47; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 x_36 = x_17;
} else {
 lean_dec_ref(x_17);
 x_36 = lean_box(0);
}
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_37, x_13);
x_39 = lean_nat_add(x_38, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_30, 0);
lean_inc(x_54);
x_47 = x_54;
goto block_53;
}
else
{
lean_object* x_55; 
x_55 = lean_unsigned_to_nat(0u);
x_47 = x_55;
goto block_53;
}
block_46:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_nat_add(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (lean_is_scalar(x_36)) {
 x_44 = lean_alloc_ctor(0, 5, 0);
} else {
 x_44 = x_36;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_15);
lean_ctor_set(x_44, 2, x_16);
lean_ctor_set(x_44, 3, x_31);
lean_ctor_set(x_44, 4, x_18);
if (lean_is_scalar(x_26)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_26;
}
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_28);
lean_ctor_set(x_45, 2, x_29);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 4, x_44);
return x_45;
}
block_53:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_nat_add(x_38, x_47);
lean_dec(x_47);
lean_dec(x_38);
if (lean_is_scalar(x_9)) {
 x_49 = lean_alloc_ctor(0, 5, 0);
} else {
 x_49 = x_9;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_5);
lean_ctor_set(x_49, 2, x_6);
lean_ctor_set(x_49, 3, x_7);
lean_ctor_set(x_49, 4, x_30);
x_50 = lean_nat_add(x_37, x_32);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_31, 0);
lean_inc(x_51);
x_40 = x_49;
x_41 = x_50;
x_42 = x_51;
goto block_46;
}
else
{
lean_object* x_52; 
x_52 = lean_unsigned_to_nat(0u);
x_40 = x_49;
x_41 = x_50;
x_42 = x_52;
goto block_46;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_9);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_56, x_13);
x_58 = lean_nat_add(x_57, x_14);
lean_dec(x_14);
x_59 = lean_nat_add(x_57, x_27);
lean_dec(x_57);
lean_inc_ref(x_7);
if (lean_is_scalar(x_26)) {
 x_60 = lean_alloc_ctor(0, 5, 0);
} else {
 x_60 = x_26;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_5);
lean_ctor_set(x_60, 2, x_6);
lean_ctor_set(x_60, 3, x_7);
lean_ctor_set(x_60, 4, x_17);
x_61 = !lean_is_exclusive(x_7);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_7, 4);
lean_dec(x_62);
x_63 = lean_ctor_get(x_7, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_7, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_7, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_7, 0);
lean_dec(x_66);
lean_ctor_set(x_7, 4, x_18);
lean_ctor_set(x_7, 3, x_60);
lean_ctor_set(x_7, 2, x_16);
lean_ctor_set(x_7, 1, x_15);
lean_ctor_set(x_7, 0, x_58);
return x_7;
}
else
{
lean_object* x_67; 
lean_dec(x_7);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_15);
lean_ctor_set(x_67, 2, x_16);
lean_ctor_set(x_67, 3, x_60);
lean_ctor_set(x_67, 4, x_18);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_17);
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_7);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_68 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3;
x_69 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_7);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_70 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4;
x_71 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_7, 0);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_73, x_72);
if (lean_is_scalar(x_9)) {
 x_75 = lean_alloc_ctor(0, 5, 0);
} else {
 x_75 = x_9;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_5);
lean_ctor_set(x_75, 2, x_6);
lean_ctor_set(x_75, 3, x_7);
lean_ctor_set(x_75, 4, x_12);
return x_75;
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_12, 3);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_12, 4);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_12);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_12, 0);
x_80 = lean_ctor_get(x_12, 1);
x_81 = lean_ctor_get(x_12, 2);
x_82 = lean_ctor_get(x_12, 4);
lean_dec(x_82);
x_83 = lean_ctor_get(x_12, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_76, 0);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_85, x_79);
lean_dec(x_79);
x_87 = lean_nat_add(x_85, x_84);
lean_ctor_set(x_12, 4, x_76);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 0, x_87);
if (lean_is_scalar(x_9)) {
 x_88 = lean_alloc_ctor(0, 5, 0);
} else {
 x_88 = x_9;
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_80);
lean_ctor_set(x_88, 2, x_81);
lean_ctor_set(x_88, 3, x_12);
lean_ctor_set(x_88, 4, x_77);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_89 = lean_ctor_get(x_12, 0);
x_90 = lean_ctor_get(x_12, 1);
x_91 = lean_ctor_get(x_12, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_12);
x_92 = lean_ctor_get(x_76, 0);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_93, x_89);
lean_dec(x_89);
x_95 = lean_nat_add(x_93, x_92);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_5);
lean_ctor_set(x_96, 2, x_6);
lean_ctor_set(x_96, 3, x_7);
lean_ctor_set(x_96, 4, x_76);
if (lean_is_scalar(x_9)) {
 x_97 = lean_alloc_ctor(0, 5, 0);
} else {
 x_97 = x_9;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_90);
lean_ctor_set(x_97, 2, x_91);
lean_ctor_set(x_97, 3, x_96);
lean_ctor_set(x_97, 4, x_77);
return x_97;
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_12);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_12, 4);
lean_dec(x_99);
x_100 = lean_ctor_get(x_12, 3);
lean_dec(x_100);
x_101 = lean_ctor_get(x_12, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_76);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_103 = lean_ctor_get(x_76, 1);
x_104 = lean_ctor_get(x_76, 2);
x_105 = lean_ctor_get(x_76, 4);
lean_dec(x_105);
x_106 = lean_ctor_get(x_76, 3);
lean_dec(x_106);
x_107 = lean_ctor_get(x_76, 0);
lean_dec(x_107);
x_108 = lean_unsigned_to_nat(3u);
x_109 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_76, 4, x_77);
lean_ctor_set(x_76, 3, x_77);
lean_ctor_set(x_76, 2, x_6);
lean_ctor_set(x_76, 1, x_5);
lean_ctor_set(x_76, 0, x_109);
lean_ctor_set(x_12, 3, x_77);
lean_ctor_set(x_12, 0, x_109);
if (lean_is_scalar(x_9)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_9;
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_103);
lean_ctor_set(x_110, 2, x_104);
lean_ctor_set(x_110, 3, x_76);
lean_ctor_set(x_110, 4, x_12);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_76, 1);
x_112 = lean_ctor_get(x_76, 2);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_76);
x_113 = lean_unsigned_to_nat(3u);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_5);
lean_ctor_set(x_115, 2, x_6);
lean_ctor_set(x_115, 3, x_77);
lean_ctor_set(x_115, 4, x_77);
lean_ctor_set(x_12, 3, x_77);
lean_ctor_set(x_12, 0, x_114);
if (lean_is_scalar(x_9)) {
 x_116 = lean_alloc_ctor(0, 5, 0);
} else {
 x_116 = x_9;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_116, 2, x_112);
lean_ctor_set(x_116, 3, x_115);
lean_ctor_set(x_116, 4, x_12);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_117 = lean_ctor_get(x_12, 1);
x_118 = lean_ctor_get(x_12, 2);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_12);
x_119 = lean_ctor_get(x_76, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_76, 2);
lean_inc(x_120);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 lean_ctor_release(x_76, 4);
 x_121 = x_76;
} else {
 lean_dec_ref(x_76);
 x_121 = lean_box(0);
}
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 5, 0);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_5);
lean_ctor_set(x_124, 2, x_6);
lean_ctor_set(x_124, 3, x_77);
lean_ctor_set(x_124, 4, x_77);
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_117);
lean_ctor_set(x_125, 2, x_118);
lean_ctor_set(x_125, 3, x_77);
lean_ctor_set(x_125, 4, x_77);
if (lean_is_scalar(x_9)) {
 x_126 = lean_alloc_ctor(0, 5, 0);
} else {
 x_126 = x_9;
}
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_119);
lean_ctor_set(x_126, 2, x_120);
lean_ctor_set(x_126, 3, x_124);
lean_ctor_set(x_126, 4, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_12, 4);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_12);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_129 = lean_ctor_get(x_12, 1);
x_130 = lean_ctor_get(x_12, 2);
x_131 = lean_ctor_get(x_12, 4);
lean_dec(x_131);
x_132 = lean_ctor_get(x_12, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_12, 0);
lean_dec(x_133);
x_134 = lean_unsigned_to_nat(3u);
x_135 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_12, 4, x_76);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 0, x_135);
if (lean_is_scalar(x_9)) {
 x_136 = lean_alloc_ctor(0, 5, 0);
} else {
 x_136 = x_9;
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_129);
lean_ctor_set(x_136, 2, x_130);
lean_ctor_set(x_136, 3, x_12);
lean_ctor_set(x_136, 4, x_127);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_ctor_get(x_12, 1);
x_138 = lean_ctor_get(x_12, 2);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_12);
x_139 = lean_unsigned_to_nat(3u);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_5);
lean_ctor_set(x_141, 2, x_6);
lean_ctor_set(x_141, 3, x_76);
lean_ctor_set(x_141, 4, x_76);
if (lean_is_scalar(x_9)) {
 x_142 = lean_alloc_ctor(0, 5, 0);
} else {
 x_142 = x_9;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_137);
lean_ctor_set(x_142, 2, x_138);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set(x_142, 4, x_127);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_144 = lean_alloc_ctor(0, 5, 0);
} else {
 x_144 = x_9;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_5);
lean_ctor_set(x_144, 2, x_6);
lean_ctor_set(x_144, 3, x_127);
lean_ctor_set(x_144, 4, x_12);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_9)) {
 x_146 = lean_alloc_ctor(0, 5, 0);
} else {
 x_146 = x_9;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_5);
lean_ctor_set(x_146, 2, x_6);
lean_ctor_set(x_146, 3, x_12);
lean_ctor_set(x_146, 4, x_12);
return x_146;
}
}
}
else
{
lean_object* x_147; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_147 = lean_alloc_ctor(0, 5, 0);
} else {
 x_147 = x_9;
}
lean_ctor_set(x_147, 0, x_4);
lean_ctor_set(x_147, 1, x_1);
lean_ctor_set(x_147, 2, x_2);
lean_ctor_set(x_147, 3, x_7);
lean_ctor_set(x_147, 4, x_8);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_4);
x_148 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(x_1, x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_149 = lean_ctor_get(x_8, 0);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_148, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_148, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_148, 4);
lean_inc(x_154);
x_155 = lean_unsigned_to_nat(3u);
x_156 = lean_nat_mul(x_155, x_149);
x_157 = lean_nat_dec_lt(x_156, x_150);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_nat_add(x_158, x_150);
lean_dec(x_150);
x_160 = lean_nat_add(x_159, x_149);
lean_dec(x_159);
if (lean_is_scalar(x_9)) {
 x_161 = lean_alloc_ctor(0, 5, 0);
} else {
 x_161 = x_9;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_5);
lean_ctor_set(x_161, 2, x_6);
lean_ctor_set(x_161, 3, x_148);
lean_ctor_set(x_161, 4, x_8);
return x_161;
}
else
{
lean_object* x_162; 
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 lean_ctor_release(x_148, 4);
 x_162 = x_148;
} else {
 lean_dec_ref(x_148);
 x_162 = lean_box(0);
}
if (lean_obj_tag(x_153) == 0)
{
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_163 = lean_ctor_get(x_153, 0);
x_164 = lean_ctor_get(x_154, 0);
x_165 = lean_ctor_get(x_154, 1);
x_166 = lean_ctor_get(x_154, 2);
x_167 = lean_ctor_get(x_154, 3);
x_168 = lean_ctor_get(x_154, 4);
x_169 = lean_unsigned_to_nat(2u);
x_170 = lean_nat_mul(x_169, x_163);
x_171 = lean_nat_dec_lt(x_164, x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_183; lean_object* x_184; 
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 lean_ctor_release(x_154, 3);
 lean_ctor_release(x_154, 4);
 x_172 = x_154;
} else {
 lean_dec_ref(x_154);
 x_172 = lean_box(0);
}
x_173 = lean_unsigned_to_nat(1u);
x_174 = lean_nat_add(x_173, x_150);
lean_dec(x_150);
x_175 = lean_nat_add(x_174, x_149);
lean_dec(x_174);
x_183 = lean_nat_add(x_173, x_163);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_167, 0);
lean_inc(x_191);
x_184 = x_191;
goto block_190;
}
else
{
lean_object* x_192; 
x_192 = lean_unsigned_to_nat(0u);
x_184 = x_192;
goto block_190;
}
block_182:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_nat_add(x_177, x_178);
lean_dec(x_178);
lean_dec(x_177);
if (lean_is_scalar(x_172)) {
 x_180 = lean_alloc_ctor(0, 5, 0);
} else {
 x_180 = x_172;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_5);
lean_ctor_set(x_180, 2, x_6);
lean_ctor_set(x_180, 3, x_168);
lean_ctor_set(x_180, 4, x_8);
if (lean_is_scalar(x_162)) {
 x_181 = lean_alloc_ctor(0, 5, 0);
} else {
 x_181 = x_162;
}
lean_ctor_set(x_181, 0, x_175);
lean_ctor_set(x_181, 1, x_165);
lean_ctor_set(x_181, 2, x_166);
lean_ctor_set(x_181, 3, x_176);
lean_ctor_set(x_181, 4, x_180);
return x_181;
}
block_190:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_nat_add(x_183, x_184);
lean_dec(x_184);
lean_dec(x_183);
if (lean_is_scalar(x_9)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_9;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_151);
lean_ctor_set(x_186, 2, x_152);
lean_ctor_set(x_186, 3, x_153);
lean_ctor_set(x_186, 4, x_167);
x_187 = lean_nat_add(x_173, x_149);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_168, 0);
lean_inc(x_188);
x_176 = x_186;
x_177 = x_187;
x_178 = x_188;
goto block_182;
}
else
{
lean_object* x_189; 
x_189 = lean_unsigned_to_nat(0u);
x_176 = x_186;
x_177 = x_187;
x_178 = x_189;
goto block_182;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_9);
x_193 = lean_unsigned_to_nat(1u);
x_194 = lean_nat_add(x_193, x_150);
lean_dec(x_150);
x_195 = lean_nat_add(x_194, x_149);
lean_dec(x_194);
x_196 = lean_nat_add(x_193, x_149);
x_197 = lean_nat_add(x_196, x_164);
lean_dec(x_196);
lean_inc_ref(x_8);
if (lean_is_scalar(x_162)) {
 x_198 = lean_alloc_ctor(0, 5, 0);
} else {
 x_198 = x_162;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_5);
lean_ctor_set(x_198, 2, x_6);
lean_ctor_set(x_198, 3, x_154);
lean_ctor_set(x_198, 4, x_8);
x_199 = !lean_is_exclusive(x_8);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_8, 4);
lean_dec(x_200);
x_201 = lean_ctor_get(x_8, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_8, 2);
lean_dec(x_202);
x_203 = lean_ctor_get(x_8, 1);
lean_dec(x_203);
x_204 = lean_ctor_get(x_8, 0);
lean_dec(x_204);
lean_ctor_set(x_8, 4, x_198);
lean_ctor_set(x_8, 3, x_153);
lean_ctor_set(x_8, 2, x_152);
lean_ctor_set(x_8, 1, x_151);
lean_ctor_set(x_8, 0, x_195);
return x_8;
}
else
{
lean_object* x_205; 
lean_dec(x_8);
x_205 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_151);
lean_ctor_set(x_205, 2, x_152);
lean_ctor_set(x_205, 3, x_153);
lean_ctor_set(x_205, 4, x_198);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec_ref(x_153);
lean_dec(x_162);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_206 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7;
x_207 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_206);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_162);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_208 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8;
x_209 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_208);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_8, 0);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_nat_add(x_211, x_210);
if (lean_is_scalar(x_9)) {
 x_213 = lean_alloc_ctor(0, 5, 0);
} else {
 x_213 = x_9;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_5);
lean_ctor_set(x_213, 2, x_6);
lean_ctor_set(x_213, 3, x_148);
lean_ctor_set(x_213, 4, x_8);
return x_213;
}
}
else
{
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_148, 3);
lean_inc(x_214);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_148, 4);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_148);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_217 = lean_ctor_get(x_148, 0);
x_218 = lean_ctor_get(x_148, 1);
x_219 = lean_ctor_get(x_148, 2);
x_220 = lean_ctor_get(x_148, 4);
lean_dec(x_220);
x_221 = lean_ctor_get(x_148, 3);
lean_dec(x_221);
x_222 = lean_ctor_get(x_215, 0);
x_223 = lean_unsigned_to_nat(1u);
x_224 = lean_nat_add(x_223, x_217);
lean_dec(x_217);
x_225 = lean_nat_add(x_223, x_222);
lean_ctor_set(x_148, 4, x_8);
lean_ctor_set(x_148, 3, x_215);
lean_ctor_set(x_148, 2, x_6);
lean_ctor_set(x_148, 1, x_5);
lean_ctor_set(x_148, 0, x_225);
if (lean_is_scalar(x_9)) {
 x_226 = lean_alloc_ctor(0, 5, 0);
} else {
 x_226 = x_9;
}
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_218);
lean_ctor_set(x_226, 2, x_219);
lean_ctor_set(x_226, 3, x_214);
lean_ctor_set(x_226, 4, x_148);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_227 = lean_ctor_get(x_148, 0);
x_228 = lean_ctor_get(x_148, 1);
x_229 = lean_ctor_get(x_148, 2);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_148);
x_230 = lean_ctor_get(x_215, 0);
x_231 = lean_unsigned_to_nat(1u);
x_232 = lean_nat_add(x_231, x_227);
lean_dec(x_227);
x_233 = lean_nat_add(x_231, x_230);
x_234 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_5);
lean_ctor_set(x_234, 2, x_6);
lean_ctor_set(x_234, 3, x_215);
lean_ctor_set(x_234, 4, x_8);
if (lean_is_scalar(x_9)) {
 x_235 = lean_alloc_ctor(0, 5, 0);
} else {
 x_235 = x_9;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_228);
lean_ctor_set(x_235, 2, x_229);
lean_ctor_set(x_235, 3, x_214);
lean_ctor_set(x_235, 4, x_234);
return x_235;
}
}
else
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_148);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_237 = lean_ctor_get(x_148, 1);
x_238 = lean_ctor_get(x_148, 2);
x_239 = lean_ctor_get(x_148, 4);
lean_dec(x_239);
x_240 = lean_ctor_get(x_148, 3);
lean_dec(x_240);
x_241 = lean_ctor_get(x_148, 0);
lean_dec(x_241);
x_242 = lean_unsigned_to_nat(3u);
x_243 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_148, 3, x_215);
lean_ctor_set(x_148, 2, x_6);
lean_ctor_set(x_148, 1, x_5);
lean_ctor_set(x_148, 0, x_243);
if (lean_is_scalar(x_9)) {
 x_244 = lean_alloc_ctor(0, 5, 0);
} else {
 x_244 = x_9;
}
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_237);
lean_ctor_set(x_244, 2, x_238);
lean_ctor_set(x_244, 3, x_214);
lean_ctor_set(x_244, 4, x_148);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_245 = lean_ctor_get(x_148, 1);
x_246 = lean_ctor_get(x_148, 2);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_148);
x_247 = lean_unsigned_to_nat(3u);
x_248 = lean_unsigned_to_nat(1u);
x_249 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_5);
lean_ctor_set(x_249, 2, x_6);
lean_ctor_set(x_249, 3, x_215);
lean_ctor_set(x_249, 4, x_215);
if (lean_is_scalar(x_9)) {
 x_250 = lean_alloc_ctor(0, 5, 0);
} else {
 x_250 = x_9;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_245);
lean_ctor_set(x_250, 2, x_246);
lean_ctor_set(x_250, 3, x_214);
lean_ctor_set(x_250, 4, x_249);
return x_250;
}
}
}
else
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_148, 4);
lean_inc(x_251);
if (lean_obj_tag(x_251) == 0)
{
uint8_t x_252; 
x_252 = !lean_is_exclusive(x_148);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_253 = lean_ctor_get(x_148, 1);
x_254 = lean_ctor_get(x_148, 2);
x_255 = lean_ctor_get(x_148, 4);
lean_dec(x_255);
x_256 = lean_ctor_get(x_148, 3);
lean_dec(x_256);
x_257 = lean_ctor_get(x_148, 0);
lean_dec(x_257);
x_258 = !lean_is_exclusive(x_251);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_259 = lean_ctor_get(x_251, 1);
x_260 = lean_ctor_get(x_251, 2);
x_261 = lean_ctor_get(x_251, 4);
lean_dec(x_261);
x_262 = lean_ctor_get(x_251, 3);
lean_dec(x_262);
x_263 = lean_ctor_get(x_251, 0);
lean_dec(x_263);
x_264 = lean_unsigned_to_nat(3u);
x_265 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_251, 4, x_214);
lean_ctor_set(x_251, 3, x_214);
lean_ctor_set(x_251, 2, x_254);
lean_ctor_set(x_251, 1, x_253);
lean_ctor_set(x_251, 0, x_265);
lean_ctor_set(x_148, 4, x_214);
lean_ctor_set(x_148, 2, x_6);
lean_ctor_set(x_148, 1, x_5);
lean_ctor_set(x_148, 0, x_265);
if (lean_is_scalar(x_9)) {
 x_266 = lean_alloc_ctor(0, 5, 0);
} else {
 x_266 = x_9;
}
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_259);
lean_ctor_set(x_266, 2, x_260);
lean_ctor_set(x_266, 3, x_251);
lean_ctor_set(x_266, 4, x_148);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_267 = lean_ctor_get(x_251, 1);
x_268 = lean_ctor_get(x_251, 2);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_251);
x_269 = lean_unsigned_to_nat(3u);
x_270 = lean_unsigned_to_nat(1u);
x_271 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_253);
lean_ctor_set(x_271, 2, x_254);
lean_ctor_set(x_271, 3, x_214);
lean_ctor_set(x_271, 4, x_214);
lean_ctor_set(x_148, 4, x_214);
lean_ctor_set(x_148, 2, x_6);
lean_ctor_set(x_148, 1, x_5);
lean_ctor_set(x_148, 0, x_270);
if (lean_is_scalar(x_9)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_9;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_267);
lean_ctor_set(x_272, 2, x_268);
lean_ctor_set(x_272, 3, x_271);
lean_ctor_set(x_272, 4, x_148);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_273 = lean_ctor_get(x_148, 1);
x_274 = lean_ctor_get(x_148, 2);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_148);
x_275 = lean_ctor_get(x_251, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_251, 2);
lean_inc(x_276);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 lean_ctor_release(x_251, 2);
 lean_ctor_release(x_251, 3);
 lean_ctor_release(x_251, 4);
 x_277 = x_251;
} else {
 lean_dec_ref(x_251);
 x_277 = lean_box(0);
}
x_278 = lean_unsigned_to_nat(3u);
x_279 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_277)) {
 x_280 = lean_alloc_ctor(0, 5, 0);
} else {
 x_280 = x_277;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_273);
lean_ctor_set(x_280, 2, x_274);
lean_ctor_set(x_280, 3, x_214);
lean_ctor_set(x_280, 4, x_214);
x_281 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_5);
lean_ctor_set(x_281, 2, x_6);
lean_ctor_set(x_281, 3, x_214);
lean_ctor_set(x_281, 4, x_214);
if (lean_is_scalar(x_9)) {
 x_282 = lean_alloc_ctor(0, 5, 0);
} else {
 x_282 = x_9;
}
lean_ctor_set(x_282, 0, x_278);
lean_ctor_set(x_282, 1, x_275);
lean_ctor_set(x_282, 2, x_276);
lean_ctor_set(x_282, 3, x_280);
lean_ctor_set(x_282, 4, x_281);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_284 = lean_alloc_ctor(0, 5, 0);
} else {
 x_284 = x_9;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_5);
lean_ctor_set(x_284, 2, x_6);
lean_ctor_set(x_284, 3, x_148);
lean_ctor_set(x_284, 4, x_251);
return x_284;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_9)) {
 x_286 = lean_alloc_ctor(0, 5, 0);
} else {
 x_286 = x_9;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_5);
lean_ctor_set(x_286, 2, x_6);
lean_ctor_set(x_286, 3, x_148);
lean_ctor_set(x_286, 4, x_148);
return x_286;
}
}
}
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_unsigned_to_nat(1u);
x_288 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_1);
lean_ctor_set(x_288, 2, x_2);
lean_ctor_set(x_288, 3, x_3);
lean_ctor_set(x_288, 4, x_3);
return x_288;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(x_1, x_5);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_3, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(x_9, x_10, x_7);
x_1 = x_11;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(1);
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(x_2, x_1);
x_4 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_112; lean_object* x_113; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*19);
x_7 = lean_ctor_get(x_1, 9);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 10);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 11);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 12);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 13);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 18);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_112 = ((lean_object*)(l_Lake_Env_baseVars___closed__4));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_124; 
x_124 = lean_box(0);
x_113 = x_124;
goto block_123;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_4, 0);
x_126 = lean_ctor_get(x_125, 1);
lean_inc_ref(x_126);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_113 = x_127;
goto block_123;
}
block_64:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 7);
x_24 = lean_ctor_get(x_3, 11);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
x_27 = ((lean_object*)(l_Lake_Env_compute___closed__6));
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = ((lean_object*)(l_Lake_Env_compute___closed__7));
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_9);
x_31 = ((lean_object*)(l_Lake_Env_compute___closed__8));
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_10);
x_33 = ((lean_object*)(l_Lake_Env_compute___closed__9));
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_11);
x_35 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__7));
lean_inc_ref(x_23);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_23);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__10));
lean_inc_ref(x_22);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_22);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__12));
lean_inc_ref(x_24);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_24);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = ((lean_object*)(l_Lake_Env_baseVars___closed__0));
x_45 = l_Lake_LeanInstall_leanCc_x3f(x_3);
lean_dec_ref(x_3);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lake_Env_baseVars___closed__1;
x_48 = lean_array_push(x_47, x_20);
x_49 = lean_array_push(x_48, x_15);
x_50 = lean_array_push(x_49, x_19);
x_51 = lean_array_push(x_50, x_13);
x_52 = lean_array_push(x_51, x_18);
x_53 = lean_array_push(x_52, x_17);
x_54 = lean_array_push(x_53, x_14);
x_55 = lean_array_push(x_54, x_26);
x_56 = lean_array_push(x_55, x_28);
x_57 = lean_array_push(x_56, x_30);
x_58 = lean_array_push(x_57, x_32);
x_59 = lean_array_push(x_58, x_34);
x_60 = lean_array_push(x_59, x_37);
x_61 = lean_array_push(x_60, x_40);
x_62 = lean_array_push(x_61, x_43);
x_63 = lean_array_push(x_62, x_46);
return x_63;
}
block_81:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_71);
x_73 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0));
x_74 = l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(x_5);
x_75 = l_Lean_Json_compress(x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_76);
x_78 = ((lean_object*)(l_Lake_Env_compute___closed__3));
if (x_6 == 0)
{
lean_object* x_79; 
x_79 = ((lean_object*)(l_Lake_Env_baseVars___closed__2));
x_13 = x_65;
x_14 = x_77;
x_15 = x_66;
x_16 = x_78;
x_17 = x_72;
x_18 = x_68;
x_19 = x_70;
x_20 = x_69;
x_21 = x_79;
goto block_64;
}
else
{
lean_object* x_80; 
x_80 = ((lean_object*)(l_Lake_Env_baseVars___closed__3));
x_13 = x_65;
x_14 = x_77;
x_15 = x_66;
x_16 = x_78;
x_17 = x_72;
x_18 = x_68;
x_19 = x_70;
x_20 = x_69;
x_21 = x_80;
goto block_64;
}
}
block_100:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_86 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_87);
lean_dec_ref(x_2);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_85);
x_89 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__1));
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_87);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__5));
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_86);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = ((lean_object*)(l_Lake_Env_compute___closed__5));
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_7);
if (x_96 == 0)
{
x_65 = x_91;
x_66 = x_82;
x_67 = x_95;
x_68 = x_94;
x_69 = x_84;
x_70 = x_88;
x_71 = x_7;
goto block_81;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_7, 0);
lean_inc(x_97);
lean_dec(x_7);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_65 = x_91;
x_66 = x_82;
x_67 = x_95;
x_68 = x_94;
x_69 = x_84;
x_70 = x_88;
x_71 = x_98;
goto block_81;
}
}
else
{
lean_object* x_99; 
lean_dec(x_7);
x_99 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__17));
x_65 = x_91;
x_66 = x_82;
x_67 = x_95;
x_68 = x_94;
x_69 = x_84;
x_70 = x_88;
x_71 = x_99;
goto block_81;
}
}
block_111:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_105 = ((lean_object*)(l_Lake_Env_computeToolchain___closed__0));
x_106 = lean_string_utf8_byte_size(x_12);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_eq(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_12);
x_82 = x_104;
x_83 = x_105;
x_84 = x_102;
x_85 = x_109;
goto block_100;
}
else
{
lean_object* x_110; 
lean_dec_ref(x_12);
x_110 = lean_box(0);
x_82 = x_104;
x_83 = x_105;
x_84 = x_102;
x_85 = x_110;
goto block_100;
}
}
block_123:
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = ((lean_object*)(l_Lake_Env_baseVars___closed__5));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_116; 
x_116 = lean_box(0);
x_101 = x_115;
x_102 = x_114;
x_103 = x_116;
goto block_111;
}
else
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_4);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_4, 0);
x_119 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_119);
lean_dec(x_118);
lean_ctor_set(x_4, 0, x_119);
x_101 = x_115;
x_102 = x_114;
x_103 = x_4;
goto block_111;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_4, 0);
lean_inc(x_120);
lean_dec(x_4);
x_121 = lean_ctor_get(x_120, 0);
lean_inc_ref(x_121);
lean_dec(x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_101 = x_115;
x_102 = x_114;
x_103 = x_122;
goto block_111;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_vars___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_44; lean_object* x_45; 
x_2 = lean_ctor_get(x_1, 6);
x_3 = lean_ctor_get(x_1, 7);
lean_inc(x_3);
lean_inc_ref(x_1);
x_4 = l_Lake_Env_baseVars(x_1);
x_44 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_3);
if (x_54 == 0)
{
x_45 = x_3;
goto block_53;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_3, 0);
lean_inc(x_55);
lean_dec(x_3);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_45 = x_56;
goto block_53;
}
}
else
{
lean_object* x_57; 
lean_dec(x_3);
x_57 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__17));
x_45 = x_57;
goto block_53;
}
block_43:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = ((lean_object*)(l_Lake_Env_compute___closed__11));
x_10 = l_Lake_Env_leanPath(x_1);
x_11 = l_System_SearchPath_toString(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = ((lean_object*)(l_Lake_Env_compute___closed__12));
x_15 = l_Lake_Env_leanSrcPath(x_1);
x_16 = l_System_SearchPath_toString(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = ((lean_object*)(l_Lake_Env_compute___closed__10));
x_20 = l_Lake_Env_leanGithash(x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l_Lake_Env_compute___closed__13));
x_24 = l_Lake_Env_path(x_1);
x_25 = l_System_SearchPath_toString(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lake_Env_vars___closed__0;
x_29 = lean_array_push(x_28, x_6);
x_30 = lean_array_push(x_29, x_8);
x_31 = lean_array_push(x_30, x_13);
x_32 = lean_array_push(x_31, x_18);
x_33 = lean_array_push(x_32, x_22);
x_34 = lean_array_push(x_33, x_27);
x_35 = l_Array_append___redArg(x_4, x_34);
lean_dec_ref(x_34);
x_36 = l_System_Platform_isWindows;
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = l_Lake_sharedLibPathEnvVar;
x_38 = l_Lake_Env_sharedLibPath(x_1);
x_39 = l_System_SearchPath_toString(x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_push(x_35, x_41);
return x_42;
}
else
{
lean_dec_ref(x_1);
return x_35;
}
}
block_53:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = ((lean_object*)(l_Lake_Env_compute___closed__4));
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = ((lean_object*)(l_Lake_Env_vars___closed__1));
x_5 = x_47;
x_6 = x_46;
x_7 = x_50;
goto block_43;
}
else
{
lean_object* x_51; 
x_51 = ((lean_object*)(l_Lake_Env_vars___closed__2));
x_5 = x_47;
x_6 = x_46;
x_7 = x_51;
goto block_43;
}
}
else
{
lean_object* x_52; 
x_52 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__17));
x_5 = x_47;
x_6 = x_46;
x_7 = x_52;
goto block_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_3, 3);
x_6 = l_Lake_Env_leanPath(x_1);
lean_inc_ref(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc_ref(x_4);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanSearchPath(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Env(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedEnv_default___closed__1 = _init_l_Lake_instInhabitedEnv_default___closed__1();
lean_mark_persistent(l_Lake_instInhabitedEnv_default___closed__1);
l_Lake_instInhabitedEnv_default = _init_l_Lake_instInhabitedEnv_default();
lean_mark_persistent(l_Lake_instInhabitedEnv_default);
l_Lake_instInhabitedEnv = _init_l_Lake_instInhabitedEnv();
lean_mark_persistent(l_Lake_instInhabitedEnv);
l_Lake_Env_noToolchainVars___closed__14 = _init_l_Lake_Env_noToolchainVars___closed__14();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__14);
l_Lake_Env_noToolchainVars___closed__15 = _init_l_Lake_Env_noToolchainVars___closed__15();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__15);
l_Lake_Env_noToolchainVars___closed__16 = _init_l_Lake_Env_noToolchainVars___closed__16();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__16);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8);
l_Lake_Env_baseVars___closed__1 = _init_l_Lake_Env_baseVars___closed__1();
lean_mark_persistent(l_Lake_Env_baseVars___closed__1);
l_Lake_Env_vars___closed__0 = _init_l_Lake_Env_vars___closed__0();
lean_mark_persistent(l_Lake_Env_vars___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
