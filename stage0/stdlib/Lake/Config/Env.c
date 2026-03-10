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
static lean_once_cell_t l_Lake_instInhabitedEnv_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
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
static const lean_string_object l_Lake_Env_compute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".lake"};
static const lean_object* l_Lake_Env_compute___closed__0 = (const lean_object*)&l_Lake_Env_compute___closed__0_value;
static const lean_string_object l_Lake_Env_compute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "config.toml"};
static const lean_object* l_Lake_Env_compute___closed__1 = (const lean_object*)&l_Lake_Env_compute___closed__1_value;
static const lean_string_object l_Lake_Env_compute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LAKE_NO_CACHE"};
static const lean_object* l_Lake_Env_compute___closed__2 = (const lean_object*)&l_Lake_Env_compute___closed__2_value;
static const lean_string_object l_Lake_Env_compute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "LAKE_ARTIFACT_CACHE"};
static const lean_object* l_Lake_Env_compute___closed__3 = (const lean_object*)&l_Lake_Env_compute___closed__3_value;
static const lean_string_object l_Lake_Env_compute___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "LAKE_CONFIG"};
static const lean_object* l_Lake_Env_compute___closed__4 = (const lean_object*)&l_Lake_Env_compute___closed__4_value;
static const lean_string_object l_Lake_Env_compute___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LAKE_CACHE_KEY"};
static const lean_object* l_Lake_Env_compute___closed__5 = (const lean_object*)&l_Lake_Env_compute___closed__5_value;
static const lean_string_object l_Lake_Env_compute___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "LAKE_CACHE_ARTIFACT_ENDPOINT"};
static const lean_object* l_Lake_Env_compute___closed__6 = (const lean_object*)&l_Lake_Env_compute___closed__6_value;
static const lean_string_object l_Lake_Env_compute___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "LAKE_CACHE_REVISION_ENDPOINT"};
static const lean_object* l_Lake_Env_compute___closed__7 = (const lean_object*)&l_Lake_Env_compute___closed__7_value;
static const lean_string_object l_Lake_Env_compute___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LAKE_CACHE_SERVICE"};
static const lean_object* l_Lake_Env_compute___closed__8 = (const lean_object*)&l_Lake_Env_compute___closed__8_value;
static const lean_string_object l_Lake_Env_compute___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_GITHASH"};
static const lean_object* l_Lake_Env_compute___closed__9 = (const lean_object*)&l_Lake_Env_compute___closed__9_value;
static const lean_string_object l_Lake_Env_compute___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LEAN_PATH"};
static const lean_object* l_Lake_Env_compute___closed__10 = (const lean_object*)&l_Lake_Env_compute___closed__10_value;
static const lean_string_object l_Lake_Env_compute___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LEAN_SRC_PATH"};
static const lean_object* l_Lake_Env_compute___closed__11 = (const lean_object*)&l_Lake_Env_compute___closed__11_value;
static const lean_string_object l_Lake_Env_compute___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PATH"};
static const lean_object* l_Lake_Env_compute___closed__12 = (const lean_object*)&l_Lake_Env_compute___closed__12_value;
static const lean_string_object l_Lake_Env_compute___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "RESERVOIR_API_BASE_URL"};
static const lean_object* l_Lake_Env_compute___closed__13 = (const lean_object*)&l_Lake_Env_compute___closed__13_value;
static const lean_string_object l_Lake_Env_compute___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "RESERVOIR_API_URL"};
static const lean_object* l_Lake_Env_compute___closed__14 = (const lean_object*)&l_Lake_Env_compute___closed__14_value;
static const lean_string_object l_Lake_Env_compute___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "/v1"};
static const lean_object* l_Lake_Env_compute___closed__15 = (const lean_object*)&l_Lake_Env_compute___closed__15_value;
static const lean_string_object l_Lake_Env_compute___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "https://reservoir.lean-lang.org/api"};
static const lean_object* l_Lake_Env_compute___closed__16 = (const lean_object*)&l_Lake_Env_compute___closed__16_value;
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_Lake_envToBool_x3f(lean_object*);
lean_object* l_Lake_getSearchPath(lean_object*);
extern lean_object* l_Lake_sharedLibPathEnvVar;
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain___boxed(lean_object*);
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
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_compute___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Env_noToolchainVars___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Env_noToolchainVars___closed__14;
static lean_once_cell_t l_Lake_Env_noToolchainVars___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Env_noToolchainVars___closed__15;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instInhabitedEnv_default___closed__0_value)}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__16 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__16_value;
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
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
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
static const lean_string_object l_Lake_Env_baseVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_Env_baseVars___closed__1 = (const lean_object*)&l_Lake_Env_baseVars___closed__1_value;
static const lean_string_object l_Lake_Env_baseVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_Env_baseVars___closed__2 = (const lean_object*)&l_Lake_Env_baseVars___closed__2_value;
static const lean_string_object l_Lake_Env_baseVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ELAN"};
static const lean_object* l_Lake_Env_baseVars___closed__3 = (const lean_object*)&l_Lake_Env_baseVars___closed__3_value;
static const lean_string_object l_Lake_Env_baseVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ELAN_HOME"};
static const lean_object* l_Lake_Env_baseVars___closed__4 = (const lean_object*)&l_Lake_Env_baseVars___closed__4_value;
lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_Env_vars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Env_baseVars___closed__1_value)}};
static const lean_object* l_Lake_Env_vars___closed__0 = (const lean_object*)&l_Lake_Env_vars___closed__0_value;
static const lean_ctor_object l_Lake_Env_vars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Env_baseVars___closed__2_value)}};
static const lean_object* l_Lake_Env_vars___closed__1 = (const lean_object*)&l_Lake_Env_vars___closed__1_value;
lean_object* l_System_SearchPath_toString(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object*);
static lean_object* _init_l_Lake_instInhabitedEnv_default___closed__1(void) {
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
static lean_object* _init_l_Lake_instInhabitedEnv_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lake_instInhabitedEnv_default___closed__1, &l_Lake_instInhabitedEnv_default___closed__1_once, _init_l_Lake_instInhabitedEnv_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv(void) {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_12; 
x_5 = lean_ctor_get(x_4, 0);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
x_6 = x_4;
x_7 = x_12;
goto block_11;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_8; 
if (x_7 == 0)
{
x_8 = x_6;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_box(0);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = ((lean_object*)(l_Lake_getUserHome_x3f___closed__1));
x_15 = lean_io_getenv(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l_Lake_getUserHome_x3f___closed__2));
x_18 = lean_io_getenv(x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_27; 
x_19 = lean_ctor_get(x_18, 0);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
x_20 = x_18;
x_21 = x_27;
goto block_26;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_string_append(x_16, x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_22);
x_23 = x_20;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_18);
lean_dec(x_16);
x_28 = lean_box(0);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_15);
x_29 = lean_box(0);
return x_29;
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_12; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
x_6 = x_4;
x_7 = x_12;
goto block_11;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_8; 
if (x_7 == 0)
{
x_8 = x_6;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_22; 
x_13 = lean_ctor_get(x_1, 0);
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
x_14 = x_1;
x_15 = x_22;
goto block_21;
}
else
{
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
x_17 = l_System_FilePath_join(x_13, x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = l_Lake_getUserHome_x3f();
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_22; 
x_13 = lean_ctor_get(x_12, 0);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
x_14 = x_12;
x_15 = x_22;
goto block_21;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
x_17 = l_System_FilePath_join(x_13, x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_12);
x_23 = lean_box(0);
return x_23;
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_16; 
x_5 = lean_ctor_get(x_3, 0);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
x_6 = x_3;
x_7 = x_16;
goto block_15;
}
else
{
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_string_utf8_byte_size(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_del_object(x_6);
lean_dec(x_5);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
if (x_7 == 0)
{
x_12 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_5);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
x_4 = x_1;
x_5 = x_12;
goto block_11;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_7 = l_System_FilePath_join(x_3, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_7);
x_8 = x_4;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_16; 
x_4 = lean_ctor_get(x_1, 0);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
x_5 = x_1;
x_6 = x_16;
goto block_15;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_string_utf8_byte_size(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_4, x_2);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_10);
x_11 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_del_object(x_5);
lean_dec(x_4);
x_14 = lean_box(0);
return x_14;
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
lean_object* x_4; lean_object* x_13; lean_object* x_14; 
x_13 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
x_14 = lean_io_getenv(x_13);
if (lean_obj_tag(x_14) == 0)
{
goto block_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec_ref(x_14);
x_22 = lean_string_utf8_byte_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_21);
goto block_20;
}
else
{
lean_dec(x_1);
x_4 = x_21;
goto block_6;
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
block_12:
{
lean_object* x_7; 
x_7 = l_Lake_getSystemCacheHome_x3f();
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_11 = l_System_FilePath_join(x_9, x_10);
x_4 = x_11;
goto block_6;
}
}
block_20:
{
if (lean_obj_tag(x_1) == 0)
{
goto block_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_string_utf8_byte_size(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_15, x_2);
x_4 = x_19;
goto block_6;
}
else
{
lean_dec(x_15);
goto block_12;
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
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_117; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_7, 0);
x_117 = !lean_is_exclusive(x_7);
if (x_117 == 0)
{
x_51 = x_7;
x_52 = x_117;
goto block_116;
}
else
{
lean_inc(x_50);
lean_dec(x_7);
x_51 = lean_box(0);
x_52 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_string_utf8_byte_size(x_50);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_85; 
x_56 = lean_ctor_get(x_4, 0);
x_57 = lean_ctor_get(x_4, 1);
x_58 = lean_ctor_get(x_4, 2);
x_59 = lean_ctor_get(x_4, 3);
x_60 = lean_ctor_get(x_4, 4);
x_61 = lean_ctor_get(x_4, 5);
x_62 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_63 = lean_ctor_get(x_4, 6);
x_64 = lean_ctor_get_uint8(x_4, sizeof(void*)*19 + 1);
x_65 = lean_ctor_get(x_4, 9);
x_66 = lean_ctor_get(x_4, 10);
x_67 = lean_ctor_get(x_4, 11);
x_68 = lean_ctor_get(x_4, 12);
x_69 = lean_ctor_get(x_4, 13);
x_70 = lean_ctor_get(x_4, 14);
x_71 = lean_ctor_get(x_4, 15);
x_72 = lean_ctor_get(x_4, 16);
x_73 = lean_ctor_get(x_4, 17);
x_74 = lean_ctor_get(x_4, 18);
x_85 = !lean_is_exclusive(x_4);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_4, 8);
lean_dec(x_86);
x_87 = lean_ctor_get(x_4, 7);
lean_dec(x_87);
x_75 = x_4;
x_76 = x_85;
goto block_84;
}
else
{
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_63);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_4);
x_75 = lean_box(0);
x_76 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_77; 
if (x_52 == 0)
{
x_77 = x_51;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_50);
x_77 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_78; 
lean_inc_ref(x_77);
if (x_76 == 0)
{
lean_ctor_set(x_75, 8, x_77);
lean_ctor_set(x_75, 7, x_77);
x_78 = x_75;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(x_81, 0, x_56);
lean_ctor_set(x_81, 1, x_57);
lean_ctor_set(x_81, 2, x_58);
lean_ctor_set(x_81, 3, x_59);
lean_ctor_set(x_81, 4, x_60);
lean_ctor_set(x_81, 5, x_61);
lean_ctor_set(x_81, 6, x_63);
lean_ctor_set(x_81, 7, x_77);
lean_ctor_set(x_81, 8, x_77);
lean_ctor_set(x_81, 9, x_65);
lean_ctor_set(x_81, 10, x_66);
lean_ctor_set(x_81, 11, x_67);
lean_ctor_set(x_81, 12, x_68);
lean_ctor_set(x_81, 13, x_69);
lean_ctor_set(x_81, 14, x_70);
lean_ctor_set(x_81, 15, x_71);
lean_ctor_set(x_81, 16, x_72);
lean_ctor_set(x_81, 17, x_73);
lean_ctor_set(x_81, 18, x_74);
lean_ctor_set_uint8(x_81, sizeof(void*)*19, x_62);
lean_ctor_set_uint8(x_81, sizeof(void*)*19 + 1, x_64);
x_78 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_115; 
lean_del_object(x_51);
lean_dec(x_50);
x_88 = lean_ctor_get(x_4, 0);
x_89 = lean_ctor_get(x_4, 1);
x_90 = lean_ctor_get(x_4, 2);
x_91 = lean_ctor_get(x_4, 3);
x_92 = lean_ctor_get(x_4, 4);
x_93 = lean_ctor_get(x_4, 5);
x_94 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_95 = lean_ctor_get(x_4, 6);
x_96 = lean_ctor_get(x_4, 7);
x_97 = lean_ctor_get(x_4, 8);
x_98 = lean_ctor_get(x_4, 9);
x_99 = lean_ctor_get(x_4, 10);
x_100 = lean_ctor_get(x_4, 11);
x_101 = lean_ctor_get(x_4, 12);
x_102 = lean_ctor_get(x_4, 13);
x_103 = lean_ctor_get(x_4, 14);
x_104 = lean_ctor_get(x_4, 15);
x_105 = lean_ctor_get(x_4, 16);
x_106 = lean_ctor_get(x_4, 17);
x_107 = lean_ctor_get(x_4, 18);
x_115 = !lean_is_exclusive(x_4);
if (x_115 == 0)
{
x_108 = x_4;
x_109 = x_115;
goto block_114;
}
else
{
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_4);
x_108 = lean_box(0);
x_109 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_110; 
if (x_109 == 0)
{
x_110 = x_108;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(x_113, 0, x_88);
lean_ctor_set(x_113, 1, x_89);
lean_ctor_set(x_113, 2, x_90);
lean_ctor_set(x_113, 3, x_91);
lean_ctor_set(x_113, 4, x_92);
lean_ctor_set(x_113, 5, x_93);
lean_ctor_set(x_113, 6, x_95);
lean_ctor_set(x_113, 7, x_96);
lean_ctor_set(x_113, 8, x_97);
lean_ctor_set(x_113, 9, x_98);
lean_ctor_set(x_113, 10, x_99);
lean_ctor_set(x_113, 11, x_100);
lean_ctor_set(x_113, 12, x_101);
lean_ctor_set(x_113, 13, x_102);
lean_ctor_set(x_113, 14, x_103);
lean_ctor_set(x_113, 15, x_104);
lean_ctor_set(x_113, 16, x_105);
lean_ctor_set(x_113, 17, x_106);
lean_ctor_set(x_113, 18, x_107);
lean_ctor_set_uint8(x_113, sizeof(void*)*19, x_94);
x_110 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_111; 
lean_ctor_set_uint8(x_110, sizeof(void*)*19 + 1, x_55);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
}
}
else
{
lean_dec(x_7);
if (lean_obj_tag(x_1) == 0)
{
goto block_49;
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_172; 
x_118 = lean_ctor_get(x_1, 0);
x_172 = !lean_is_exclusive(x_1);
if (x_172 == 0)
{
x_119 = x_1;
x_120 = x_172;
goto block_171;
}
else
{
lean_inc(x_118);
lean_dec(x_1);
x_119 = lean_box(0);
x_120 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_121 = lean_string_utf8_byte_size(x_3);
x_122 = lean_unsigned_to_nat(0u);
x_123 = lean_nat_dec_eq(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(x_2);
x_125 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_118, x_3);
if (x_120 == 0)
{
lean_ctor_set(x_119, 0, x_125);
x_126 = x_119;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_125);
x_126 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_127; 
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_158; 
x_158 = lean_box(0);
x_127 = x_158;
goto block_157;
}
else
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_168; 
x_159 = lean_ctor_get(x_124, 0);
x_168 = !lean_is_exclusive(x_124);
if (x_168 == 0)
{
x_160 = x_124;
x_161 = x_168;
goto block_167;
}
else
{
lean_inc(x_159);
lean_dec(x_124);
x_160 = lean_box(0);
x_161 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_163 = l_System_FilePath_join(x_159, x_162);
if (x_161 == 0)
{
lean_ctor_set(x_160, 0, x_163);
x_164 = x_160;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_163);
x_164 = x_166;
goto block_165;
}
block_165:
{
x_127 = x_164;
goto block_157;
}
}
}
block_157:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_154; 
x_128 = lean_ctor_get(x_4, 0);
x_129 = lean_ctor_get(x_4, 1);
x_130 = lean_ctor_get(x_4, 2);
x_131 = lean_ctor_get(x_4, 3);
x_132 = lean_ctor_get(x_4, 4);
x_133 = lean_ctor_get(x_4, 5);
x_134 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_135 = lean_ctor_get(x_4, 6);
x_136 = lean_ctor_get_uint8(x_4, sizeof(void*)*19 + 1);
x_137 = lean_ctor_get(x_4, 9);
x_138 = lean_ctor_get(x_4, 10);
x_139 = lean_ctor_get(x_4, 11);
x_140 = lean_ctor_get(x_4, 12);
x_141 = lean_ctor_get(x_4, 13);
x_142 = lean_ctor_get(x_4, 14);
x_143 = lean_ctor_get(x_4, 15);
x_144 = lean_ctor_get(x_4, 16);
x_145 = lean_ctor_get(x_4, 17);
x_146 = lean_ctor_get(x_4, 18);
x_154 = !lean_is_exclusive(x_4);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_4, 8);
lean_dec(x_155);
x_156 = lean_ctor_get(x_4, 7);
lean_dec(x_156);
x_147 = x_4;
x_148 = x_154;
goto block_153;
}
else
{
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_135);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_4);
x_147 = lean_box(0);
x_148 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_149; 
if (x_148 == 0)
{
lean_ctor_set(x_147, 8, x_127);
lean_ctor_set(x_147, 7, x_126);
x_149 = x_147;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(x_152, 0, x_128);
lean_ctor_set(x_152, 1, x_129);
lean_ctor_set(x_152, 2, x_130);
lean_ctor_set(x_152, 3, x_131);
lean_ctor_set(x_152, 4, x_132);
lean_ctor_set(x_152, 5, x_133);
lean_ctor_set(x_152, 6, x_135);
lean_ctor_set(x_152, 7, x_126);
lean_ctor_set(x_152, 8, x_127);
lean_ctor_set(x_152, 9, x_137);
lean_ctor_set(x_152, 10, x_138);
lean_ctor_set(x_152, 11, x_139);
lean_ctor_set(x_152, 12, x_140);
lean_ctor_set(x_152, 13, x_141);
lean_ctor_set(x_152, 14, x_142);
lean_ctor_set(x_152, 15, x_143);
lean_ctor_set(x_152, 16, x_144);
lean_ctor_set(x_152, 17, x_145);
lean_ctor_set(x_152, 18, x_146);
lean_ctor_set_uint8(x_152, sizeof(void*)*19, x_134);
lean_ctor_set_uint8(x_152, sizeof(void*)*19 + 1, x_136);
x_149 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
}
}
}
else
{
lean_del_object(x_119);
lean_dec(x_118);
goto block_49;
}
}
}
}
block_49:
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_48; 
x_10 = lean_ctor_get(x_8, 0);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
x_11 = x_8;
x_12 = x_48;
goto block_47;
}
else
{
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_44; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
x_17 = lean_ctor_get(x_4, 4);
x_18 = lean_ctor_get(x_4, 5);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*19);
x_20 = lean_ctor_get(x_4, 6);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*19 + 1);
x_22 = lean_ctor_get(x_4, 9);
x_23 = lean_ctor_get(x_4, 10);
x_24 = lean_ctor_get(x_4, 11);
x_25 = lean_ctor_get(x_4, 12);
x_26 = lean_ctor_get(x_4, 13);
x_27 = lean_ctor_get(x_4, 14);
x_28 = lean_ctor_get(x_4, 15);
x_29 = lean_ctor_get(x_4, 16);
x_30 = lean_ctor_get(x_4, 17);
x_31 = lean_ctor_get(x_4, 18);
x_44 = !lean_is_exclusive(x_4);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_4, 8);
lean_dec(x_45);
x_46 = lean_ctor_get(x_4, 7);
lean_dec(x_46);
x_32 = x_4;
x_33 = x_44;
goto block_43;
}
else
{
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
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_32 = lean_box(0);
x_33 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
x_35 = l_System_FilePath_join(x_10, x_34);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_35);
x_36 = x_11;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_35);
x_36 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_37; 
lean_inc_ref(x_36);
if (x_33 == 0)
{
lean_ctor_set(x_32, 8, x_36);
lean_ctor_set(x_32, 7, x_36);
x_37 = x_32;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(x_40, 0, x_13);
lean_ctor_set(x_40, 1, x_14);
lean_ctor_set(x_40, 2, x_15);
lean_ctor_set(x_40, 3, x_16);
lean_ctor_set(x_40, 4, x_17);
lean_ctor_set(x_40, 5, x_18);
lean_ctor_set(x_40, 6, x_20);
lean_ctor_set(x_40, 7, x_36);
lean_ctor_set(x_40, 8, x_36);
lean_ctor_set(x_40, 9, x_22);
lean_ctor_set(x_40, 10, x_23);
lean_ctor_set(x_40, 11, x_24);
lean_ctor_set(x_40, 12, x_25);
lean_ctor_set(x_40, 13, x_26);
lean_ctor_set(x_40, 14, x_27);
lean_ctor_set(x_40, 15, x_28);
lean_ctor_set(x_40, 16, x_29);
lean_ctor_set(x_40, 17, x_30);
lean_ctor_set(x_40, 18, x_31);
lean_ctor_set_uint8(x_40, sizeof(void*)*19, x_19);
lean_ctor_set_uint8(x_40, sizeof(void*)*19 + 1, x_21);
x_37 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_48; 
x_8 = lean_ctor_get(x_7, 0);
x_48 = !lean_is_exclusive(x_7);
if (x_48 == 0)
{
x_9 = x_7;
x_10 = x_48;
goto block_47;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0));
x_12 = lean_string_dec_eq(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_3);
x_13 = l_String_toName(x_3);
x_14 = l_Lean_Name_isAnonymous(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_del_object(x_9);
lean_dec(x_3);
x_15 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
x_16 = lean_ctor_get(x_15, 0);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
x_17 = x_15;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec_ref(x_15);
x_25 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_13, x_24, x_8);
x_1 = x_25;
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_27 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1));
x_28 = lean_string_append(x_27, x_3);
lean_dec(x_3);
x_29 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
x_30 = lean_string_append(x_28, x_29);
if (x_10 == 0)
{
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_30);
x_31 = x_9;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
else
{
lean_object* x_34; 
lean_del_object(x_9);
lean_dec(x_3);
x_34 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_8);
lean_dec(x_6);
x_35 = lean_ctor_get(x_34, 0);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
x_36 = x_34;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec_ref(x_34);
x_44 = lean_box(0);
x_45 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_44, x_43, x_8);
x_1 = x_45;
x_2 = x_6;
goto _start;
}
}
}
}
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_1);
return x_49;
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
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
x_16 = x_13;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
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
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = ((lean_object*)(l_Lake_Env_compute___closed__13));
x_291 = lean_io_getenv(x_290);
if (lean_obj_tag(x_291) == 1)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_291, 0);
lean_inc(x_312);
lean_dec_ref(x_291);
x_313 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_312);
x_292 = x_313;
goto block_311;
}
else
{
lean_object* x_314; 
lean_dec(x_291);
x_314 = ((lean_object*)(l_Lake_Env_compute___closed__16));
x_292 = x_314;
goto block_311;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
lean_inc_ref(x_8);
lean_inc(x_11);
lean_inc(x_3);
x_24 = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set(x_24, 3, x_9);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_10);
lean_ctor_set(x_24, 6, x_14);
lean_ctor_set(x_24, 7, x_11);
lean_ctor_set(x_24, 8, x_11);
lean_ctor_set(x_24, 9, x_17);
lean_ctor_set(x_24, 10, x_6);
lean_ctor_set(x_24, 11, x_15);
lean_ctor_set(x_24, 12, x_18);
lean_ctor_set(x_24, 13, x_23);
lean_ctor_set(x_24, 14, x_20);
lean_ctor_set(x_24, 15, x_12);
lean_ctor_set(x_24, 16, x_16);
lean_ctor_set(x_24, 17, x_21);
lean_ctor_set(x_24, 18, x_8);
lean_ctor_set_uint8(x_24, sizeof(void*)*19, x_19);
lean_ctor_set_uint8(x_24, sizeof(void*)*19 + 1, x_13);
x_25 = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(x_3, x_7, x_8, x_24);
lean_dec_ref(x_8);
return x_25;
}
block_62:
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_45; 
x_45 = lean_box(0);
x_6 = x_27;
x_7 = x_28;
x_8 = x_29;
x_9 = x_30;
x_10 = x_31;
x_11 = x_32;
x_12 = x_33;
x_13 = x_34;
x_14 = x_35;
x_15 = x_37;
x_16 = x_38;
x_17 = x_39;
x_18 = x_44;
x_19 = x_41;
x_20 = x_40;
x_21 = x_42;
x_22 = x_43;
x_23 = x_45;
goto block_26;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_61; 
x_46 = lean_ctor_get(x_36, 0);
x_61 = !lean_is_exclusive(x_36);
if (x_61 == 0)
{
x_47 = x_36;
x_48 = x_61;
goto block_60;
}
else
{
lean_inc(x_46);
lean_dec(x_36);
x_47 = lean_box(0);
x_48 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_string_utf8_byte_size(x_46);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
x_52 = l_String_Slice_trimAscii(x_51);
lean_dec_ref(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
lean_dec_ref(x_52);
x_56 = lean_string_utf8_extract(x_53, x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
if (x_48 == 0)
{
lean_ctor_set(x_47, 0, x_56);
x_57 = x_47;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
x_6 = x_27;
x_7 = x_28;
x_8 = x_29;
x_9 = x_30;
x_10 = x_31;
x_11 = x_32;
x_12 = x_33;
x_13 = x_34;
x_14 = x_35;
x_15 = x_37;
x_16 = x_38;
x_17 = x_39;
x_18 = x_44;
x_19 = x_41;
x_20 = x_40;
x_21 = x_42;
x_22 = x_43;
x_23 = x_57;
goto block_26;
}
}
}
}
block_90:
{
if (lean_obj_tag(x_72) == 0)
{
x_27 = x_63;
x_28 = x_64;
x_29 = x_65;
x_30 = x_66;
x_31 = x_67;
x_32 = x_68;
x_33 = x_69;
x_34 = x_70;
x_35 = x_71;
x_36 = x_73;
x_37 = x_80;
x_38 = x_74;
x_39 = x_75;
x_40 = x_77;
x_41 = x_76;
x_42 = x_78;
x_43 = x_79;
x_44 = x_72;
goto block_62;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_89; 
x_81 = lean_ctor_get(x_72, 0);
x_89 = !lean_is_exclusive(x_72);
if (x_89 == 0)
{
x_82 = x_72;
x_83 = x_89;
goto block_88;
}
else
{
lean_inc(x_81);
lean_dec(x_72);
x_82 = lean_box(0);
x_83 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_84; lean_object* x_85; 
x_84 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_81);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_84);
x_85 = x_82;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_84);
x_85 = x_87;
goto block_86;
}
block_86:
{
x_27 = x_63;
x_28 = x_64;
x_29 = x_65;
x_30 = x_66;
x_31 = x_67;
x_32 = x_68;
x_33 = x_69;
x_34 = x_70;
x_35 = x_71;
x_36 = x_73;
x_37 = x_80;
x_38 = x_74;
x_39 = x_75;
x_40 = x_77;
x_41 = x_76;
x_42 = x_78;
x_43 = x_79;
x_44 = x_85;
goto block_62;
}
}
}
}
block_118:
{
if (lean_obj_tag(x_101) == 0)
{
x_63 = x_108;
x_64 = x_91;
x_65 = x_92;
x_66 = x_93;
x_67 = x_94;
x_68 = x_95;
x_69 = x_96;
x_70 = x_97;
x_71 = x_98;
x_72 = x_99;
x_73 = x_100;
x_74 = x_102;
x_75 = x_103;
x_76 = x_105;
x_77 = x_104;
x_78 = x_106;
x_79 = x_107;
x_80 = x_101;
goto block_90;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_117; 
x_109 = lean_ctor_get(x_101, 0);
x_117 = !lean_is_exclusive(x_101);
if (x_117 == 0)
{
x_110 = x_101;
x_111 = x_117;
goto block_116;
}
else
{
lean_inc(x_109);
lean_dec(x_101);
x_110 = lean_box(0);
x_111 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_112; lean_object* x_113; 
x_112 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_109);
if (x_111 == 0)
{
lean_ctor_set(x_110, 0, x_112);
x_113 = x_110;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_112);
x_113 = x_115;
goto block_114;
}
block_114:
{
x_63 = x_108;
x_64 = x_91;
x_65 = x_92;
x_66 = x_93;
x_67 = x_94;
x_68 = x_95;
x_69 = x_96;
x_70 = x_97;
x_71 = x_98;
x_72 = x_99;
x_73 = x_100;
x_74 = x_102;
x_75 = x_103;
x_76 = x_105;
x_77 = x_104;
x_78 = x_106;
x_79 = x_107;
x_80 = x_113;
goto block_90;
}
}
}
}
block_153:
{
if (lean_obj_tag(x_130) == 0)
{
x_91 = x_119;
x_92 = x_120;
x_93 = x_121;
x_94 = x_122;
x_95 = x_123;
x_96 = x_124;
x_97 = x_125;
x_98 = x_126;
x_99 = x_127;
x_100 = x_128;
x_101 = x_129;
x_102 = x_131;
x_103 = x_136;
x_104 = x_133;
x_105 = x_132;
x_106 = x_134;
x_107 = x_135;
x_108 = x_130;
goto block_118;
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_152; 
x_137 = lean_ctor_get(x_130, 0);
x_152 = !lean_is_exclusive(x_130);
if (x_152 == 0)
{
x_138 = x_130;
x_139 = x_152;
goto block_151;
}
else
{
lean_inc(x_137);
lean_dec(x_130);
x_138 = lean_box(0);
x_139 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_140 = lean_unsigned_to_nat(0u);
x_141 = lean_string_utf8_byte_size(x_137);
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_141);
x_143 = l_String_Slice_trimAscii(x_142);
lean_dec_ref(x_142);
x_144 = lean_ctor_get(x_143, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 2);
lean_inc(x_146);
lean_dec_ref(x_143);
x_147 = lean_string_utf8_extract(x_144, x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
lean_dec_ref(x_144);
if (x_139 == 0)
{
lean_ctor_set(x_138, 0, x_147);
x_148 = x_138;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_147);
x_148 = x_150;
goto block_149;
}
block_149:
{
x_91 = x_119;
x_92 = x_120;
x_93 = x_121;
x_94 = x_122;
x_95 = x_123;
x_96 = x_124;
x_97 = x_125;
x_98 = x_126;
x_99 = x_127;
x_100 = x_128;
x_101 = x_129;
x_102 = x_131;
x_103 = x_136;
x_104 = x_133;
x_105 = x_132;
x_106 = x_134;
x_107 = x_135;
x_108 = x_148;
goto block_118;
}
}
}
}
block_173:
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_119 = x_154;
x_120 = x_155;
x_121 = x_156;
x_122 = x_157;
x_123 = x_158;
x_124 = x_159;
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = x_163;
x_129 = x_164;
x_130 = x_165;
x_131 = x_166;
x_132 = x_168;
x_133 = x_167;
x_134 = x_169;
x_135 = x_170;
x_136 = x_172;
goto block_153;
}
block_198:
{
uint8_t x_190; lean_object* x_191; 
x_190 = 0;
x_191 = lean_box(0);
if (lean_obj_tag(x_184) == 0)
{
if (lean_obj_tag(x_174) == 0)
{
x_119 = x_174;
x_120 = x_175;
x_121 = x_176;
x_122 = x_177;
x_123 = x_191;
x_124 = x_178;
x_125 = x_190;
x_126 = x_189;
x_127 = x_179;
x_128 = x_180;
x_129 = x_181;
x_130 = x_182;
x_131 = x_183;
x_132 = x_185;
x_133 = x_186;
x_134 = x_187;
x_135 = x_188;
x_136 = x_174;
goto block_153;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_174, 0);
x_193 = ((lean_object*)(l_Lake_Env_compute___closed__0));
lean_inc(x_192);
x_194 = l_System_FilePath_join(x_192, x_193);
x_195 = ((lean_object*)(l_Lake_Env_compute___closed__1));
x_196 = l_System_FilePath_join(x_194, x_195);
x_154 = x_174;
x_155 = x_175;
x_156 = x_176;
x_157 = x_177;
x_158 = x_191;
x_159 = x_178;
x_160 = x_190;
x_161 = x_189;
x_162 = x_179;
x_163 = x_180;
x_164 = x_181;
x_165 = x_182;
x_166 = x_183;
x_167 = x_186;
x_168 = x_185;
x_169 = x_187;
x_170 = x_188;
x_171 = x_196;
goto block_173;
}
}
else
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_184, 0);
lean_inc(x_197);
lean_dec_ref(x_184);
x_154 = x_174;
x_155 = x_175;
x_156 = x_176;
x_157 = x_177;
x_158 = x_191;
x_159 = x_178;
x_160 = x_190;
x_161 = x_189;
x_162 = x_179;
x_163 = x_180;
x_164 = x_181;
x_165 = x_182;
x_166 = x_183;
x_167 = x_186;
x_168 = x_185;
x_169 = x_187;
x_170 = x_188;
x_171 = x_197;
goto block_173;
}
}
block_218:
{
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_215; 
x_215 = lean_box(0);
x_174 = x_199;
x_175 = x_200;
x_176 = x_201;
x_177 = x_202;
x_178 = x_203;
x_179 = x_204;
x_180 = x_205;
x_181 = x_206;
x_182 = x_207;
x_183 = x_208;
x_184 = x_210;
x_185 = x_214;
x_186 = x_211;
x_187 = x_212;
x_188 = x_213;
x_189 = x_215;
goto block_198;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_209, 0);
lean_inc(x_216);
lean_dec_ref(x_209);
x_217 = l_Lake_envToBool_x3f(x_216);
x_174 = x_199;
x_175 = x_200;
x_176 = x_201;
x_177 = x_202;
x_178 = x_203;
x_179 = x_204;
x_180 = x_205;
x_181 = x_206;
x_182 = x_207;
x_183 = x_208;
x_184 = x_210;
x_185 = x_214;
x_186 = x_211;
x_187 = x_212;
x_188 = x_213;
x_189 = x_217;
goto block_198;
}
}
block_235:
{
uint8_t x_234; 
x_234 = 0;
x_199 = x_219;
x_200 = x_220;
x_201 = x_221;
x_202 = x_222;
x_203 = x_223;
x_204 = x_224;
x_205 = x_225;
x_206 = x_226;
x_207 = x_227;
x_208 = x_228;
x_209 = x_230;
x_210 = x_231;
x_211 = x_229;
x_212 = x_232;
x_213 = x_233;
x_214 = x_234;
goto block_218;
}
block_258:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_237) == 0)
{
x_219 = x_236;
x_220 = x_238;
x_221 = x_239;
x_222 = x_240;
x_223 = x_241;
x_224 = x_242;
x_225 = x_243;
x_226 = x_244;
x_227 = x_245;
x_228 = x_246;
x_229 = x_247;
x_230 = x_248;
x_231 = x_249;
x_232 = x_250;
x_233 = x_251;
goto block_235;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_237, 0);
lean_inc(x_252);
lean_dec_ref(x_237);
x_253 = l_Lake_envToBool_x3f(x_252);
if (lean_obj_tag(x_253) == 0)
{
x_219 = x_236;
x_220 = x_238;
x_221 = x_239;
x_222 = x_240;
x_223 = x_241;
x_224 = x_242;
x_225 = x_243;
x_226 = x_244;
x_227 = x_245;
x_228 = x_246;
x_229 = x_247;
x_230 = x_248;
x_231 = x_249;
x_232 = x_250;
x_233 = x_251;
goto block_235;
}
else
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = lean_unbox(x_254);
lean_dec(x_254);
x_199 = x_236;
x_200 = x_238;
x_201 = x_239;
x_202 = x_240;
x_203 = x_241;
x_204 = x_242;
x_205 = x_243;
x_206 = x_244;
x_207 = x_245;
x_208 = x_246;
x_209 = x_248;
x_210 = x_249;
x_211 = x_247;
x_212 = x_250;
x_213 = x_251;
x_214 = x_255;
goto block_218;
}
}
}
else
{
lean_object* x_256; uint8_t x_257; 
lean_dec(x_237);
x_256 = lean_ctor_get(x_4, 0);
x_257 = lean_unbox(x_256);
x_199 = x_236;
x_200 = x_238;
x_201 = x_239;
x_202 = x_240;
x_203 = x_241;
x_204 = x_242;
x_205 = x_243;
x_206 = x_244;
x_207 = x_245;
x_208 = x_246;
x_209 = x_248;
x_210 = x_249;
x_211 = x_247;
x_212 = x_250;
x_213 = x_251;
x_214 = x_257;
goto block_218;
}
}
block_289:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_263 = ((lean_object*)(l_Lake_Env_compute___closed__2));
x_264 = lean_io_getenv(x_263);
x_265 = ((lean_object*)(l_Lake_Env_compute___closed__3));
x_266 = lean_io_getenv(x_265);
x_267 = ((lean_object*)(l_Lake_Env_compute___closed__4));
x_268 = lean_io_getenv(x_267);
x_269 = ((lean_object*)(l_Lake_Env_compute___closed__5));
x_270 = lean_io_getenv(x_269);
x_271 = ((lean_object*)(l_Lake_Env_compute___closed__6));
x_272 = lean_io_getenv(x_271);
x_273 = ((lean_object*)(l_Lake_Env_compute___closed__7));
x_274 = lean_io_getenv(x_273);
x_275 = ((lean_object*)(l_Lake_Env_compute___closed__8));
x_276 = lean_io_getenv(x_275);
x_277 = ((lean_object*)(l_Lake_Env_compute___closed__9));
x_278 = lean_io_getenv(x_277);
x_279 = ((lean_object*)(l_Lake_Env_compute___closed__10));
x_280 = l_Lake_getSearchPath(x_279);
x_281 = ((lean_object*)(l_Lake_Env_compute___closed__11));
x_282 = l_Lake_getSearchPath(x_281);
x_283 = l_Lake_sharedLibPathEnvVar;
x_284 = l_Lake_getSearchPath(x_283);
x_285 = ((lean_object*)(l_Lake_Env_compute___closed__12));
x_286 = l_Lake_getSearchPath(x_285);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_287; 
x_287 = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
x_236 = x_259;
x_237 = x_264;
x_238 = x_260;
x_239 = x_262;
x_240 = x_261;
x_241 = x_282;
x_242 = x_274;
x_243 = x_276;
x_244 = x_272;
x_245 = x_270;
x_246 = x_284;
x_247 = x_280;
x_248 = x_266;
x_249 = x_268;
x_250 = x_286;
x_251 = x_287;
goto block_258;
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_278, 0);
lean_inc(x_288);
lean_dec_ref(x_278);
x_236 = x_259;
x_237 = x_264;
x_238 = x_260;
x_239 = x_262;
x_240 = x_261;
x_241 = x_282;
x_242 = x_274;
x_243 = x_276;
x_244 = x_272;
x_245 = x_270;
x_246 = x_284;
x_247 = x_280;
x_248 = x_266;
x_249 = x_268;
x_250 = x_286;
x_251 = x_288;
goto block_258;
}
}
block_311:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = l_Lake_Env_computeToolchain();
x_294 = l_Lake_getUserHome_x3f();
x_295 = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
lean_dec_ref(x_295);
x_297 = ((lean_object*)(l_Lake_Env_compute___closed__14));
x_298 = lean_io_getenv(x_297);
if (lean_obj_tag(x_298) == 1)
{
lean_object* x_299; lean_object* x_300; 
lean_dec_ref(x_292);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
lean_dec_ref(x_298);
x_300 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_299);
x_259 = x_294;
x_260 = x_293;
x_261 = x_296;
x_262 = x_300;
goto block_289;
}
else
{
lean_object* x_301; lean_object* x_302; 
lean_dec(x_298);
x_301 = ((lean_object*)(l_Lake_Env_compute___closed__15));
x_302 = lean_string_append(x_292, x_301);
x_259 = x_294;
x_260 = x_293;
x_261 = x_296;
x_262 = x_302;
goto block_289;
}
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_310; 
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec_ref(x_292);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_303 = lean_ctor_get(x_295, 0);
x_310 = !lean_is_exclusive(x_295);
if (x_310 == 0)
{
x_304 = x_295;
x_305 = x_310;
goto block_309;
}
else
{
lean_inc(x_303);
lean_dec(x_295);
x_304 = lean_box(0);
x_305 = x_310;
goto block_309;
}
block_309:
{
lean_object* x_306; 
if (x_305 == 0)
{
x_306 = x_304;
goto block_307;
}
else
{
lean_object* x_308; 
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_303);
x_306 = x_308;
goto block_307;
}
block_307:
{
return x_306;
}
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
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 18);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_cacheToolchain(x_1);
lean_dec_ref(x_1);
return x_2;
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
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__0));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_array_push(x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__2));
x_2 = lean_obj_once(&l_Lake_Env_noToolchainVars___closed__14, &l_Lake_Env_noToolchainVars___closed__14_once, _init_l_Lake_Env_noToolchainVars___closed__14);
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
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
x_23 = lean_ctor_get(x_3, 0);
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
x_24 = x_3;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
x_6 = x_26;
goto block_22;
}
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_3);
x_31 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
x_6 = x_31;
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
x_14 = lean_obj_once(&l_Lake_Env_noToolchainVars___closed__15, &l_Lake_Env_noToolchainVars___closed__15_once, _init_l_Lake_Env_noToolchainVars___closed__15);
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
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3(void) {
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
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4(void) {
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
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7(void) {
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
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8(void) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_365; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_365 = !lean_is_exclusive(x_3);
if (x_365 == 0)
{
x_9 = x_3;
x_10 = x_365;
goto block_364;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_365;
goto block_364;
}
block_364:
{
uint8_t x_11; 
x_11 = lean_string_dec_lt(x_1, x_5);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_string_dec_eq(x_1, x_5);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(x_1, x_2, x_8);
if (lean_obj_tag(x_7) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 4);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_mul(x_20, x_14);
x_22 = lean_nat_dec_lt(x_21, x_15);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_23, x_14);
x_25 = lean_nat_add(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_13);
lean_ctor_set(x_9, 0, x_25);
x_26 = x_9;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 2, x_6);
lean_ctor_set(x_28, 3, x_7);
lean_ctor_set(x_28, 4, x_13);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
else
{
lean_object* x_29; uint8_t x_30; uint8_t x_98; 
x_98 = !lean_is_exclusive(x_13);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_13, 4);
lean_dec(x_99);
x_100 = lean_ctor_get(x_13, 3);
lean_dec(x_100);
x_101 = lean_ctor_get(x_13, 2);
lean_dec(x_101);
x_102 = lean_ctor_get(x_13, 1);
lean_dec(x_102);
x_103 = lean_ctor_get(x_13, 0);
lean_dec(x_103);
x_29 = x_13;
x_30 = x_98;
goto block_97;
}
else
{
lean_dec(x_13);
x_29 = lean_box(0);
x_30 = x_98;
goto block_97;
}
block_97:
{
if (lean_obj_tag(x_18) == 0)
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
x_33 = lean_ctor_get(x_18, 2);
x_34 = lean_ctor_get(x_18, 3);
x_35 = lean_ctor_get(x_18, 4);
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_nat_mul(x_37, x_36);
x_39 = lean_nat_dec_lt(x_31, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_68; 
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_68 = !lean_is_exclusive(x_18);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_18, 4);
lean_dec(x_69);
x_70 = lean_ctor_get(x_18, 3);
lean_dec(x_70);
x_71 = lean_ctor_get(x_18, 2);
lean_dec(x_71);
x_72 = lean_ctor_get(x_18, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_18, 0);
lean_dec(x_73);
x_40 = x_18;
x_41 = x_68;
goto block_67;
}
else
{
lean_dec(x_18);
x_40 = lean_box(0);
x_41 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_56; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_42, x_14);
x_44 = lean_nat_add(x_43, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_34, 0);
lean_inc(x_65);
x_56 = x_65;
goto block_64;
}
else
{
lean_object* x_66; 
x_66 = lean_unsigned_to_nat(0u);
x_56 = x_66;
goto block_64;
}
block_55:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_nat_add(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
if (x_41 == 0)
{
lean_ctor_set(x_40, 4, x_19);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set(x_40, 2, x_17);
lean_ctor_set(x_40, 1, x_16);
lean_ctor_set(x_40, 0, x_48);
x_49 = x_40;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_16);
lean_ctor_set(x_54, 2, x_17);
lean_ctor_set(x_54, 3, x_35);
lean_ctor_set(x_54, 4, x_19);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_49);
lean_ctor_set(x_29, 3, x_45);
lean_ctor_set(x_29, 2, x_33);
lean_ctor_set(x_29, 1, x_32);
lean_ctor_set(x_29, 0, x_44);
x_50 = x_29;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_32);
lean_ctor_set(x_52, 2, x_33);
lean_ctor_set(x_52, 3, x_45);
lean_ctor_set(x_52, 4, x_49);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
block_64:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_nat_add(x_43, x_56);
lean_dec(x_56);
lean_dec(x_43);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_34);
lean_ctor_set(x_9, 0, x_57);
x_58 = x_9;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_5);
lean_ctor_set(x_63, 2, x_6);
lean_ctor_set(x_63, 3, x_7);
lean_ctor_set(x_63, 4, x_34);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
x_59 = lean_nat_add(x_42, x_36);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_35, 0);
lean_inc(x_60);
x_45 = x_58;
x_46 = x_59;
x_47 = x_60;
goto block_55;
}
else
{
lean_object* x_61; 
x_61 = lean_unsigned_to_nat(0u);
x_45 = x_58;
x_46 = x_59;
x_47 = x_61;
goto block_55;
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_del_object(x_9);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_74, x_14);
x_76 = lean_nat_add(x_75, x_15);
lean_dec(x_15);
x_77 = lean_nat_add(x_75, x_31);
lean_dec(x_75);
lean_inc_ref(x_7);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_18);
lean_ctor_set(x_29, 3, x_7);
lean_ctor_set(x_29, 2, x_6);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 0, x_77);
x_78 = x_29;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_77);
lean_ctor_set(x_92, 1, x_5);
lean_ctor_set(x_92, 2, x_6);
lean_ctor_set(x_92, 3, x_7);
lean_ctor_set(x_92, 4, x_18);
x_78 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_79; uint8_t x_80; uint8_t x_85; 
x_85 = !lean_is_exclusive(x_7);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_7, 4);
lean_dec(x_86);
x_87 = lean_ctor_get(x_7, 3);
lean_dec(x_87);
x_88 = lean_ctor_get(x_7, 2);
lean_dec(x_88);
x_89 = lean_ctor_get(x_7, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_7, 0);
lean_dec(x_90);
x_79 = x_7;
x_80 = x_85;
goto block_84;
}
else
{
lean_dec(x_7);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
lean_ctor_set(x_79, 4, x_19);
lean_ctor_set(x_79, 3, x_78);
lean_ctor_set(x_79, 2, x_17);
lean_ctor_set(x_79, 1, x_16);
lean_ctor_set(x_79, 0, x_76);
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_16);
lean_ctor_set(x_83, 2, x_17);
lean_ctor_set(x_83, 3, x_78);
lean_ctor_set(x_83, 4, x_19);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_18);
lean_del_object(x_29);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_7);
lean_del_object(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_93 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3);
x_94 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_93);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_del_object(x_29);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_7);
lean_del_object(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_95 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4);
x_96 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_7, 0);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_105, x_104);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_13);
lean_ctor_set(x_9, 0, x_106);
x_107 = x_9;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_5);
lean_ctor_set(x_109, 2, x_6);
lean_ctor_set(x_109, 3, x_7);
lean_ctor_set(x_109, 4, x_13);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_13, 3);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_13, 4);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_128; 
x_112 = lean_ctor_get(x_13, 0);
x_113 = lean_ctor_get(x_13, 1);
x_114 = lean_ctor_get(x_13, 2);
x_128 = !lean_is_exclusive(x_13);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_13, 4);
lean_dec(x_129);
x_130 = lean_ctor_get(x_13, 3);
lean_dec(x_130);
x_115 = x_13;
x_116 = x_128;
goto block_127;
}
else
{
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_13);
x_115 = lean_box(0);
x_116 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_110, 0);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_118, x_112);
lean_dec(x_112);
x_120 = lean_nat_add(x_118, x_117);
if (x_116 == 0)
{
lean_ctor_set(x_115, 4, x_110);
lean_ctor_set(x_115, 3, x_7);
lean_ctor_set(x_115, 2, x_6);
lean_ctor_set(x_115, 1, x_5);
lean_ctor_set(x_115, 0, x_120);
x_121 = x_115;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set(x_126, 1, x_5);
lean_ctor_set(x_126, 2, x_6);
lean_ctor_set(x_126, 3, x_7);
lean_ctor_set(x_126, 4, x_110);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_111);
lean_ctor_set(x_9, 3, x_121);
lean_ctor_set(x_9, 2, x_114);
lean_ctor_set(x_9, 1, x_113);
lean_ctor_set(x_9, 0, x_119);
x_122 = x_9;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_113);
lean_ctor_set(x_124, 2, x_114);
lean_ctor_set(x_124, 3, x_121);
lean_ctor_set(x_124, 4, x_111);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_156; 
x_131 = lean_ctor_get(x_13, 1);
x_132 = lean_ctor_get(x_13, 2);
x_156 = !lean_is_exclusive(x_13);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_13, 4);
lean_dec(x_157);
x_158 = lean_ctor_get(x_13, 3);
lean_dec(x_158);
x_159 = lean_ctor_get(x_13, 0);
lean_dec(x_159);
x_133 = x_13;
x_134 = x_156;
goto block_155;
}
else
{
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_13);
x_133 = lean_box(0);
x_134 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_151; 
x_135 = lean_ctor_get(x_110, 1);
x_136 = lean_ctor_get(x_110, 2);
x_151 = !lean_is_exclusive(x_110);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_110, 4);
lean_dec(x_152);
x_153 = lean_ctor_get(x_110, 3);
lean_dec(x_153);
x_154 = lean_ctor_get(x_110, 0);
lean_dec(x_154);
x_137 = x_110;
x_138 = x_151;
goto block_150;
}
else
{
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_110);
x_137 = lean_box(0);
x_138 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_unsigned_to_nat(3u);
x_140 = lean_unsigned_to_nat(1u);
if (x_138 == 0)
{
lean_ctor_set(x_137, 4, x_111);
lean_ctor_set(x_137, 3, x_111);
lean_ctor_set(x_137, 2, x_6);
lean_ctor_set(x_137, 1, x_5);
lean_ctor_set(x_137, 0, x_140);
x_141 = x_137;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_149, 0, x_140);
lean_ctor_set(x_149, 1, x_5);
lean_ctor_set(x_149, 2, x_6);
lean_ctor_set(x_149, 3, x_111);
lean_ctor_set(x_149, 4, x_111);
x_141 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_142; 
if (x_134 == 0)
{
lean_ctor_set(x_133, 3, x_111);
lean_ctor_set(x_133, 0, x_140);
x_142 = x_133;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_140);
lean_ctor_set(x_147, 1, x_131);
lean_ctor_set(x_147, 2, x_132);
lean_ctor_set(x_147, 3, x_111);
lean_ctor_set(x_147, 4, x_111);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_142);
lean_ctor_set(x_9, 3, x_141);
lean_ctor_set(x_9, 2, x_136);
lean_ctor_set(x_9, 1, x_135);
lean_ctor_set(x_9, 0, x_139);
x_143 = x_9;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_145, 0, x_139);
lean_ctor_set(x_145, 1, x_135);
lean_ctor_set(x_145, 2, x_136);
lean_ctor_set(x_145, 3, x_141);
lean_ctor_set(x_145, 4, x_142);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
}
}
}
}
else
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_13, 4);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; uint8_t x_174; 
x_161 = lean_ctor_get(x_13, 1);
x_162 = lean_ctor_get(x_13, 2);
x_174 = !lean_is_exclusive(x_13);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_13, 4);
lean_dec(x_175);
x_176 = lean_ctor_get(x_13, 3);
lean_dec(x_176);
x_177 = lean_ctor_get(x_13, 0);
lean_dec(x_177);
x_163 = x_13;
x_164 = x_174;
goto block_173;
}
else
{
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_13);
x_163 = lean_box(0);
x_164 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_unsigned_to_nat(3u);
x_166 = lean_unsigned_to_nat(1u);
if (x_164 == 0)
{
lean_ctor_set(x_163, 4, x_110);
lean_ctor_set(x_163, 2, x_6);
lean_ctor_set(x_163, 1, x_5);
lean_ctor_set(x_163, 0, x_166);
x_167 = x_163;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_172, 0, x_166);
lean_ctor_set(x_172, 1, x_5);
lean_ctor_set(x_172, 2, x_6);
lean_ctor_set(x_172, 3, x_110);
lean_ctor_set(x_172, 4, x_110);
x_167 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_168; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_160);
lean_ctor_set(x_9, 3, x_167);
lean_ctor_set(x_9, 2, x_162);
lean_ctor_set(x_9, 1, x_161);
lean_ctor_set(x_9, 0, x_165);
x_168 = x_9;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_170, 0, x_165);
lean_ctor_set(x_170, 1, x_161);
lean_ctor_set(x_170, 2, x_162);
lean_ctor_set(x_170, 3, x_167);
lean_ctor_set(x_170, 4, x_160);
x_168 = x_170;
goto block_169;
}
block_169:
{
return x_168;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_13);
lean_ctor_set(x_9, 3, x_160);
lean_ctor_set(x_9, 0, x_178);
x_179 = x_9;
goto block_180;
}
else
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_5);
lean_ctor_set(x_181, 2, x_6);
lean_ctor_set(x_181, 3, x_160);
lean_ctor_set(x_181, 4, x_13);
x_179 = x_181;
goto block_180;
}
block_180:
{
return x_179;
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_unsigned_to_nat(1u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_13);
lean_ctor_set(x_9, 3, x_13);
lean_ctor_set(x_9, 0, x_182);
x_183 = x_9;
goto block_184;
}
else
{
lean_object* x_185; 
x_185 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_5);
lean_ctor_set(x_185, 2, x_6);
lean_ctor_set(x_185, 3, x_13);
lean_ctor_set(x_185, 4, x_13);
x_183 = x_185;
goto block_184;
}
block_184:
{
return x_183;
}
}
}
}
else
{
lean_object* x_186; 
lean_dec(x_6);
lean_dec(x_5);
if (x_10 == 0)
{
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
x_186 = x_9;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_188, 0, x_4);
lean_ctor_set(x_188, 1, x_1);
lean_ctor_set(x_188, 2, x_2);
lean_ctor_set(x_188, 3, x_7);
lean_ctor_set(x_188, 4, x_8);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
else
{
lean_object* x_189; 
lean_dec(x_4);
x_189 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(x_1, x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_190 = lean_ctor_get(x_8, 0);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_189, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_189, 4);
lean_inc(x_195);
x_196 = lean_unsigned_to_nat(3u);
x_197 = lean_nat_mul(x_196, x_190);
x_198 = lean_nat_dec_lt(x_197, x_191);
lean_dec(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
x_199 = lean_unsigned_to_nat(1u);
x_200 = lean_nat_add(x_199, x_191);
lean_dec(x_191);
x_201 = lean_nat_add(x_200, x_190);
lean_dec(x_200);
if (x_10 == 0)
{
lean_ctor_set(x_9, 3, x_189);
lean_ctor_set(x_9, 0, x_201);
x_202 = x_9;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_5);
lean_ctor_set(x_204, 2, x_6);
lean_ctor_set(x_204, 3, x_189);
lean_ctor_set(x_204, 4, x_8);
x_202 = x_204;
goto block_203;
}
block_203:
{
return x_202;
}
}
else
{
lean_object* x_205; uint8_t x_206; uint8_t x_276; 
x_276 = !lean_is_exclusive(x_189);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_189, 4);
lean_dec(x_277);
x_278 = lean_ctor_get(x_189, 3);
lean_dec(x_278);
x_279 = lean_ctor_get(x_189, 2);
lean_dec(x_279);
x_280 = lean_ctor_get(x_189, 1);
lean_dec(x_280);
x_281 = lean_ctor_get(x_189, 0);
lean_dec(x_281);
x_205 = x_189;
x_206 = x_276;
goto block_275;
}
else
{
lean_dec(x_189);
x_205 = lean_box(0);
x_206 = x_276;
goto block_275;
}
block_275:
{
if (lean_obj_tag(x_194) == 0)
{
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_207 = lean_ctor_get(x_194, 0);
x_208 = lean_ctor_get(x_195, 0);
x_209 = lean_ctor_get(x_195, 1);
x_210 = lean_ctor_get(x_195, 2);
x_211 = lean_ctor_get(x_195, 3);
x_212 = lean_ctor_get(x_195, 4);
x_213 = lean_unsigned_to_nat(2u);
x_214 = lean_nat_mul(x_213, x_207);
x_215 = lean_nat_dec_lt(x_208, x_214);
lean_dec(x_214);
if (x_215 == 0)
{
lean_object* x_216; uint8_t x_217; uint8_t x_245; 
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
x_245 = !lean_is_exclusive(x_195);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_246 = lean_ctor_get(x_195, 4);
lean_dec(x_246);
x_247 = lean_ctor_get(x_195, 3);
lean_dec(x_247);
x_248 = lean_ctor_get(x_195, 2);
lean_dec(x_248);
x_249 = lean_ctor_get(x_195, 1);
lean_dec(x_249);
x_250 = lean_ctor_get(x_195, 0);
lean_dec(x_250);
x_216 = x_195;
x_217 = x_245;
goto block_244;
}
else
{
lean_dec(x_195);
x_216 = lean_box(0);
x_217 = x_245;
goto block_244;
}
block_244:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_232; lean_object* x_233; 
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_add(x_218, x_191);
lean_dec(x_191);
x_220 = lean_nat_add(x_219, x_190);
lean_dec(x_219);
x_232 = lean_nat_add(x_218, x_207);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_211, 0);
lean_inc(x_242);
x_233 = x_242;
goto block_241;
}
else
{
lean_object* x_243; 
x_243 = lean_unsigned_to_nat(0u);
x_233 = x_243;
goto block_241;
}
block_231:
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_nat_add(x_222, x_223);
lean_dec(x_223);
lean_dec(x_222);
if (x_217 == 0)
{
lean_ctor_set(x_216, 4, x_8);
lean_ctor_set(x_216, 3, x_212);
lean_ctor_set(x_216, 2, x_6);
lean_ctor_set(x_216, 1, x_5);
lean_ctor_set(x_216, 0, x_224);
x_225 = x_216;
goto block_229;
}
else
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_230, 0, x_224);
lean_ctor_set(x_230, 1, x_5);
lean_ctor_set(x_230, 2, x_6);
lean_ctor_set(x_230, 3, x_212);
lean_ctor_set(x_230, 4, x_8);
x_225 = x_230;
goto block_229;
}
block_229:
{
lean_object* x_226; 
if (x_206 == 0)
{
lean_ctor_set(x_205, 4, x_225);
lean_ctor_set(x_205, 3, x_221);
lean_ctor_set(x_205, 2, x_210);
lean_ctor_set(x_205, 1, x_209);
lean_ctor_set(x_205, 0, x_220);
x_226 = x_205;
goto block_227;
}
else
{
lean_object* x_228; 
x_228 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_228, 0, x_220);
lean_ctor_set(x_228, 1, x_209);
lean_ctor_set(x_228, 2, x_210);
lean_ctor_set(x_228, 3, x_221);
lean_ctor_set(x_228, 4, x_225);
x_226 = x_228;
goto block_227;
}
block_227:
{
return x_226;
}
}
}
block_241:
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_nat_add(x_232, x_233);
lean_dec(x_233);
lean_dec(x_232);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_211);
lean_ctor_set(x_9, 3, x_194);
lean_ctor_set(x_9, 2, x_193);
lean_ctor_set(x_9, 1, x_192);
lean_ctor_set(x_9, 0, x_234);
x_235 = x_9;
goto block_239;
}
else
{
lean_object* x_240; 
x_240 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_240, 0, x_234);
lean_ctor_set(x_240, 1, x_192);
lean_ctor_set(x_240, 2, x_193);
lean_ctor_set(x_240, 3, x_194);
lean_ctor_set(x_240, 4, x_211);
x_235 = x_240;
goto block_239;
}
block_239:
{
lean_object* x_236; 
x_236 = lean_nat_add(x_218, x_190);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_212, 0);
lean_inc(x_237);
x_221 = x_235;
x_222 = x_236;
x_223 = x_237;
goto block_231;
}
else
{
lean_object* x_238; 
x_238 = lean_unsigned_to_nat(0u);
x_221 = x_235;
x_222 = x_236;
x_223 = x_238;
goto block_231;
}
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_del_object(x_9);
x_251 = lean_unsigned_to_nat(1u);
x_252 = lean_nat_add(x_251, x_191);
lean_dec(x_191);
x_253 = lean_nat_add(x_252, x_190);
lean_dec(x_252);
x_254 = lean_nat_add(x_251, x_190);
x_255 = lean_nat_add(x_254, x_208);
lean_dec(x_254);
lean_inc_ref(x_8);
if (x_206 == 0)
{
lean_ctor_set(x_205, 4, x_8);
lean_ctor_set(x_205, 3, x_195);
lean_ctor_set(x_205, 2, x_6);
lean_ctor_set(x_205, 1, x_5);
lean_ctor_set(x_205, 0, x_255);
x_256 = x_205;
goto block_269;
}
else
{
lean_object* x_270; 
x_270 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_270, 0, x_255);
lean_ctor_set(x_270, 1, x_5);
lean_ctor_set(x_270, 2, x_6);
lean_ctor_set(x_270, 3, x_195);
lean_ctor_set(x_270, 4, x_8);
x_256 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_257; uint8_t x_258; uint8_t x_263; 
x_263 = !lean_is_exclusive(x_8);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_264 = lean_ctor_get(x_8, 4);
lean_dec(x_264);
x_265 = lean_ctor_get(x_8, 3);
lean_dec(x_265);
x_266 = lean_ctor_get(x_8, 2);
lean_dec(x_266);
x_267 = lean_ctor_get(x_8, 1);
lean_dec(x_267);
x_268 = lean_ctor_get(x_8, 0);
lean_dec(x_268);
x_257 = x_8;
x_258 = x_263;
goto block_262;
}
else
{
lean_dec(x_8);
x_257 = lean_box(0);
x_258 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_259; 
if (x_258 == 0)
{
lean_ctor_set(x_257, 4, x_256);
lean_ctor_set(x_257, 3, x_194);
lean_ctor_set(x_257, 2, x_193);
lean_ctor_set(x_257, 1, x_192);
lean_ctor_set(x_257, 0, x_253);
x_259 = x_257;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_261, 0, x_253);
lean_ctor_set(x_261, 1, x_192);
lean_ctor_set(x_261, 2, x_193);
lean_ctor_set(x_261, 3, x_194);
lean_ctor_set(x_261, 4, x_256);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec_ref(x_194);
lean_del_object(x_205);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec_ref(x_8);
lean_del_object(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_271 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7);
x_272 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_271);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_del_object(x_205);
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec_ref(x_8);
lean_del_object(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_273 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8);
x_274 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_273);
return x_274;
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_ctor_get(x_8, 0);
x_283 = lean_unsigned_to_nat(1u);
x_284 = lean_nat_add(x_283, x_282);
if (x_10 == 0)
{
lean_ctor_set(x_9, 3, x_189);
lean_ctor_set(x_9, 0, x_284);
x_285 = x_9;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_5);
lean_ctor_set(x_287, 2, x_6);
lean_ctor_set(x_287, 3, x_189);
lean_ctor_set(x_287, 4, x_8);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
else
{
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_189, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_189, 4);
lean_inc(x_289);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_306; 
x_290 = lean_ctor_get(x_189, 0);
x_291 = lean_ctor_get(x_189, 1);
x_292 = lean_ctor_get(x_189, 2);
x_306 = !lean_is_exclusive(x_189);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_189, 4);
lean_dec(x_307);
x_308 = lean_ctor_get(x_189, 3);
lean_dec(x_308);
x_293 = x_189;
x_294 = x_306;
goto block_305;
}
else
{
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_189);
x_293 = lean_box(0);
x_294 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_295 = lean_ctor_get(x_289, 0);
x_296 = lean_unsigned_to_nat(1u);
x_297 = lean_nat_add(x_296, x_290);
lean_dec(x_290);
x_298 = lean_nat_add(x_296, x_295);
if (x_294 == 0)
{
lean_ctor_set(x_293, 4, x_8);
lean_ctor_set(x_293, 3, x_289);
lean_ctor_set(x_293, 2, x_6);
lean_ctor_set(x_293, 1, x_5);
lean_ctor_set(x_293, 0, x_298);
x_299 = x_293;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_304, 0, x_298);
lean_ctor_set(x_304, 1, x_5);
lean_ctor_set(x_304, 2, x_6);
lean_ctor_set(x_304, 3, x_289);
lean_ctor_set(x_304, 4, x_8);
x_299 = x_304;
goto block_303;
}
block_303:
{
lean_object* x_300; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_299);
lean_ctor_set(x_9, 3, x_288);
lean_ctor_set(x_9, 2, x_292);
lean_ctor_set(x_9, 1, x_291);
lean_ctor_set(x_9, 0, x_297);
x_300 = x_9;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_302, 0, x_297);
lean_ctor_set(x_302, 1, x_291);
lean_ctor_set(x_302, 2, x_292);
lean_ctor_set(x_302, 3, x_288);
lean_ctor_set(x_302, 4, x_299);
x_300 = x_302;
goto block_301;
}
block_301:
{
return x_300;
}
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; uint8_t x_322; 
x_309 = lean_ctor_get(x_189, 1);
x_310 = lean_ctor_get(x_189, 2);
x_322 = !lean_is_exclusive(x_189);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_189, 4);
lean_dec(x_323);
x_324 = lean_ctor_get(x_189, 3);
lean_dec(x_324);
x_325 = lean_ctor_get(x_189, 0);
lean_dec(x_325);
x_311 = x_189;
x_312 = x_322;
goto block_321;
}
else
{
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_189);
x_311 = lean_box(0);
x_312 = x_322;
goto block_321;
}
block_321:
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_unsigned_to_nat(3u);
x_314 = lean_unsigned_to_nat(1u);
if (x_312 == 0)
{
lean_ctor_set(x_311, 3, x_289);
lean_ctor_set(x_311, 2, x_6);
lean_ctor_set(x_311, 1, x_5);
lean_ctor_set(x_311, 0, x_314);
x_315 = x_311;
goto block_319;
}
else
{
lean_object* x_320; 
x_320 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_320, 0, x_314);
lean_ctor_set(x_320, 1, x_5);
lean_ctor_set(x_320, 2, x_6);
lean_ctor_set(x_320, 3, x_289);
lean_ctor_set(x_320, 4, x_289);
x_315 = x_320;
goto block_319;
}
block_319:
{
lean_object* x_316; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_315);
lean_ctor_set(x_9, 3, x_288);
lean_ctor_set(x_9, 2, x_310);
lean_ctor_set(x_9, 1, x_309);
lean_ctor_set(x_9, 0, x_313);
x_316 = x_9;
goto block_317;
}
else
{
lean_object* x_318; 
x_318 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_318, 0, x_313);
lean_ctor_set(x_318, 1, x_309);
lean_ctor_set(x_318, 2, x_310);
lean_ctor_set(x_318, 3, x_288);
lean_ctor_set(x_318, 4, x_315);
x_316 = x_318;
goto block_317;
}
block_317:
{
return x_316;
}
}
}
}
}
else
{
lean_object* x_326; 
x_326 = lean_ctor_get(x_189, 4);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_352; 
x_327 = lean_ctor_get(x_189, 1);
x_328 = lean_ctor_get(x_189, 2);
x_352 = !lean_is_exclusive(x_189);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_189, 4);
lean_dec(x_353);
x_354 = lean_ctor_get(x_189, 3);
lean_dec(x_354);
x_355 = lean_ctor_get(x_189, 0);
lean_dec(x_355);
x_329 = x_189;
x_330 = x_352;
goto block_351;
}
else
{
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_189);
x_329 = lean_box(0);
x_330 = x_352;
goto block_351;
}
block_351:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; uint8_t x_347; 
x_331 = lean_ctor_get(x_326, 1);
x_332 = lean_ctor_get(x_326, 2);
x_347 = !lean_is_exclusive(x_326);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_326, 4);
lean_dec(x_348);
x_349 = lean_ctor_get(x_326, 3);
lean_dec(x_349);
x_350 = lean_ctor_get(x_326, 0);
lean_dec(x_350);
x_333 = x_326;
x_334 = x_347;
goto block_346;
}
else
{
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_326);
x_333 = lean_box(0);
x_334 = x_347;
goto block_346;
}
block_346:
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_unsigned_to_nat(3u);
x_336 = lean_unsigned_to_nat(1u);
if (x_334 == 0)
{
lean_ctor_set(x_333, 4, x_288);
lean_ctor_set(x_333, 3, x_288);
lean_ctor_set(x_333, 2, x_328);
lean_ctor_set(x_333, 1, x_327);
lean_ctor_set(x_333, 0, x_336);
x_337 = x_333;
goto block_344;
}
else
{
lean_object* x_345; 
x_345 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_345, 0, x_336);
lean_ctor_set(x_345, 1, x_327);
lean_ctor_set(x_345, 2, x_328);
lean_ctor_set(x_345, 3, x_288);
lean_ctor_set(x_345, 4, x_288);
x_337 = x_345;
goto block_344;
}
block_344:
{
lean_object* x_338; 
if (x_330 == 0)
{
lean_ctor_set(x_329, 4, x_288);
lean_ctor_set(x_329, 2, x_6);
lean_ctor_set(x_329, 1, x_5);
lean_ctor_set(x_329, 0, x_336);
x_338 = x_329;
goto block_342;
}
else
{
lean_object* x_343; 
x_343 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_343, 0, x_336);
lean_ctor_set(x_343, 1, x_5);
lean_ctor_set(x_343, 2, x_6);
lean_ctor_set(x_343, 3, x_288);
lean_ctor_set(x_343, 4, x_288);
x_338 = x_343;
goto block_342;
}
block_342:
{
lean_object* x_339; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_338);
lean_ctor_set(x_9, 3, x_337);
lean_ctor_set(x_9, 2, x_332);
lean_ctor_set(x_9, 1, x_331);
lean_ctor_set(x_9, 0, x_335);
x_339 = x_9;
goto block_340;
}
else
{
lean_object* x_341; 
x_341 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_341, 0, x_335);
lean_ctor_set(x_341, 1, x_331);
lean_ctor_set(x_341, 2, x_332);
lean_ctor_set(x_341, 3, x_337);
lean_ctor_set(x_341, 4, x_338);
x_339 = x_341;
goto block_340;
}
block_340:
{
return x_339;
}
}
}
}
}
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_326);
lean_ctor_set(x_9, 3, x_189);
lean_ctor_set(x_9, 0, x_356);
x_357 = x_9;
goto block_358;
}
else
{
lean_object* x_359; 
x_359 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_5);
lean_ctor_set(x_359, 2, x_6);
lean_ctor_set(x_359, 3, x_189);
lean_ctor_set(x_359, 4, x_326);
x_357 = x_359;
goto block_358;
}
block_358:
{
return x_357;
}
}
}
}
else
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_unsigned_to_nat(1u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_189);
lean_ctor_set(x_9, 3, x_189);
lean_ctor_set(x_9, 0, x_360);
x_361 = x_9;
goto block_362;
}
else
{
lean_object* x_363; 
x_363 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_5);
lean_ctor_set(x_363, 2, x_6);
lean_ctor_set(x_363, 3, x_189);
lean_ctor_set(x_363, 4, x_189);
x_361 = x_363;
goto block_362;
}
block_362:
{
return x_361;
}
}
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_unsigned_to_nat(1u);
x_367 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_1);
lean_ctor_set(x_367, 2, x_2);
lean_ctor_set(x_367, 3, x_3);
lean_ctor_set(x_367, 4, x_3);
return x_367;
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
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_141; lean_object* x_142; 
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
x_141 = ((lean_object*)(l_Lake_Env_baseVars___closed__3));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_156; 
x_156 = lean_box(0);
x_142 = x_156;
goto block_155;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_4, 0);
x_158 = lean_ctor_get(x_157, 1);
lean_inc_ref(x_158);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_142 = x_159;
goto block_155;
}
block_60:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 7);
x_28 = lean_ctor_get(x_3, 12);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_25);
x_30 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__7));
lean_inc_ref(x_27);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__10));
lean_inc_ref(x_26);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__12));
lean_inc_ref(x_28);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = ((lean_object*)(l_Lake_Env_baseVars___closed__0));
x_40 = l_Lake_LeanInstall_leanCc_x3f(x_3);
lean_dec_ref(x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_unsigned_to_nat(16u);
x_43 = lean_mk_empty_array_with_capacity(x_42);
x_44 = lean_array_push(x_43, x_15);
x_45 = lean_array_push(x_44, x_13);
x_46 = lean_array_push(x_45, x_24);
x_47 = lean_array_push(x_46, x_14);
x_48 = lean_array_push(x_47, x_22);
x_49 = lean_array_push(x_48, x_16);
x_50 = lean_array_push(x_49, x_20);
x_51 = lean_array_push(x_50, x_21);
x_52 = lean_array_push(x_51, x_17);
x_53 = lean_array_push(x_52, x_23);
x_54 = lean_array_push(x_53, x_19);
x_55 = lean_array_push(x_54, x_29);
x_56 = lean_array_push(x_55, x_32);
x_57 = lean_array_push(x_56, x_35);
x_58 = lean_array_push(x_57, x_38);
x_59 = lean_array_push(x_58, x_41);
return x_59;
}
block_88:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
x_72 = ((lean_object*)(l_Lake_Env_compute___closed__5));
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_8);
x_74 = ((lean_object*)(l_Lake_Env_compute___closed__6));
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_9);
x_76 = ((lean_object*)(l_Lake_Env_compute___closed__7));
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_10);
x_78 = ((lean_object*)(l_Lake_Env_compute___closed__8));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_79; 
x_79 = lean_box(0);
x_13 = x_61;
x_14 = x_63;
x_15 = x_62;
x_16 = x_64;
x_17 = x_73;
x_18 = x_78;
x_19 = x_77;
x_20 = x_65;
x_21 = x_71;
x_22 = x_66;
x_23 = x_75;
x_24 = x_68;
x_25 = x_79;
goto block_60;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_87; 
x_80 = lean_ctor_get(x_11, 0);
x_87 = !lean_is_exclusive(x_11);
if (x_87 == 0)
{
x_81 = x_11;
x_82 = x_87;
goto block_86;
}
else
{
lean_inc(x_80);
lean_dec(x_11);
x_81 = lean_box(0);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
if (x_82 == 0)
{
x_83 = x_81;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_80);
x_83 = x_85;
goto block_84;
}
block_84:
{
x_13 = x_61;
x_14 = x_63;
x_15 = x_62;
x_16 = x_64;
x_17 = x_73;
x_18 = x_78;
x_19 = x_77;
x_20 = x_65;
x_21 = x_71;
x_22 = x_66;
x_23 = x_75;
x_24 = x_68;
x_25 = x_83;
goto block_60;
}
}
}
}
block_105:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
x_97 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0));
x_98 = l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(x_5);
x_99 = l_Lean_Json_compress(x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
x_102 = ((lean_object*)(l_Lake_Env_compute___closed__2));
if (x_6 == 0)
{
lean_object* x_103; 
x_103 = ((lean_object*)(l_Lake_Env_baseVars___closed__1));
x_61 = x_89;
x_62 = x_91;
x_63 = x_90;
x_64 = x_96;
x_65 = x_101;
x_66 = x_93;
x_67 = x_102;
x_68 = x_94;
x_69 = x_103;
goto block_88;
}
else
{
lean_object* x_104; 
x_104 = ((lean_object*)(l_Lake_Env_baseVars___closed__2));
x_61 = x_89;
x_62 = x_91;
x_63 = x_90;
x_64 = x_96;
x_65 = x_101;
x_66 = x_93;
x_67 = x_102;
x_68 = x_94;
x_69 = x_104;
goto block_88;
}
}
block_129:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_110 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_111);
lean_dec_ref(x_2);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_109);
x_113 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__1));
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_111);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__5));
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_110);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = ((lean_object*)(l_Lake_Env_compute___closed__4));
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_127; 
x_120 = lean_ctor_get(x_7, 0);
x_127 = !lean_is_exclusive(x_7);
if (x_127 == 0)
{
x_121 = x_7;
x_122 = x_127;
goto block_126;
}
else
{
lean_inc(x_120);
lean_dec(x_7);
x_121 = lean_box(0);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_122 == 0)
{
x_123 = x_121;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
x_123 = x_125;
goto block_124;
}
block_124:
{
x_89 = x_106;
x_90 = x_115;
x_91 = x_108;
x_92 = x_119;
x_93 = x_118;
x_94 = x_112;
x_95 = x_123;
goto block_105;
}
}
}
else
{
lean_object* x_128; 
lean_dec(x_7);
x_128 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
x_89 = x_106;
x_90 = x_115;
x_91 = x_108;
x_92 = x_119;
x_93 = x_118;
x_94 = x_112;
x_95 = x_128;
goto block_105;
}
}
block_140:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_134 = ((lean_object*)(l_Lake_Env_computeToolchain___closed__0));
x_135 = lean_string_utf8_byte_size(x_12);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_eq(x_135, x_136);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_12);
x_106 = x_133;
x_107 = x_134;
x_108 = x_131;
x_109 = x_138;
goto block_129;
}
else
{
lean_object* x_139; 
lean_dec_ref(x_12);
x_139 = lean_box(0);
x_106 = x_133;
x_107 = x_134;
x_108 = x_131;
x_109 = x_139;
goto block_129;
}
}
block_155:
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = ((lean_object*)(l_Lake_Env_baseVars___closed__4));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_145; 
x_145 = lean_box(0);
x_130 = x_144;
x_131 = x_143;
x_132 = x_145;
goto block_140;
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_154; 
x_146 = lean_ctor_get(x_4, 0);
x_154 = !lean_is_exclusive(x_4);
if (x_154 == 0)
{
x_147 = x_4;
x_148 = x_154;
goto block_153;
}
else
{
lean_inc(x_146);
lean_dec(x_4);
x_147 = lean_box(0);
x_148 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_146, 0);
lean_inc_ref(x_149);
lean_dec(x_146);
if (x_148 == 0)
{
lean_ctor_set(x_147, 0, x_149);
x_150 = x_147;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_149);
x_150 = x_152;
goto block_151;
}
block_151:
{
x_130 = x_144;
x_131 = x_143;
x_132 = x_150;
goto block_140;
}
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
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_45; lean_object* x_46; 
x_2 = lean_ctor_get(x_1, 6);
x_3 = lean_ctor_get(x_1, 7);
lean_inc(x_3);
lean_inc_ref(x_1);
x_4 = l_Lake_Env_baseVars(x_1);
x_45 = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
x_55 = lean_ctor_get(x_3, 0);
x_62 = !lean_is_exclusive(x_3);
if (x_62 == 0)
{
x_56 = x_3;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_3);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
x_46 = x_58;
goto block_54;
}
}
}
else
{
lean_object* x_63; 
lean_dec(x_3);
x_63 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
x_46 = x_63;
goto block_54;
}
block_44:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = ((lean_object*)(l_Lake_Env_compute___closed__10));
x_10 = l_Lake_Env_leanPath(x_1);
x_11 = l_System_SearchPath_toString(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = ((lean_object*)(l_Lake_Env_compute___closed__11));
x_15 = l_Lake_Env_leanSrcPath(x_1);
x_16 = l_System_SearchPath_toString(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = ((lean_object*)(l_Lake_Env_compute___closed__9));
x_20 = l_Lake_Env_leanGithash(x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l_Lake_Env_compute___closed__12));
x_24 = l_Lake_Env_path(x_1);
x_25 = l_System_SearchPath_toString(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_unsigned_to_nat(6u);
x_29 = lean_mk_empty_array_with_capacity(x_28);
x_30 = lean_array_push(x_29, x_5);
x_31 = lean_array_push(x_30, x_8);
x_32 = lean_array_push(x_31, x_13);
x_33 = lean_array_push(x_32, x_18);
x_34 = lean_array_push(x_33, x_22);
x_35 = lean_array_push(x_34, x_27);
x_36 = l_Array_append___redArg(x_4, x_35);
lean_dec_ref(x_35);
x_37 = l_System_Platform_isWindows;
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = l_Lake_sharedLibPathEnvVar;
x_39 = l_Lake_Env_sharedLibPath(x_1);
x_40 = l_System_SearchPath_toString(x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_36, x_42);
return x_43;
}
else
{
lean_dec_ref(x_1);
return x_36;
}
}
block_54:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = ((lean_object*)(l_Lake_Env_compute___closed__3));
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_2, 0);
x_50 = lean_unbox(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = ((lean_object*)(l_Lake_Env_vars___closed__0));
x_5 = x_47;
x_6 = x_48;
x_7 = x_51;
goto block_44;
}
else
{
lean_object* x_52; 
x_52 = ((lean_object*)(l_Lake_Env_vars___closed__1));
x_5 = x_47;
x_6 = x_48;
x_7 = x_52;
goto block_44;
}
}
else
{
lean_object* x_53; 
x_53 = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
x_5 = x_47;
x_6 = x_48;
x_7 = x_53;
goto block_44;
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
lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Cache(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InstallPath(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedEnv_default = _init_l_Lake_instInhabitedEnv_default();
lean_mark_persistent(l_Lake_instInhabitedEnv_default);
l_Lake_instInhabitedEnv = _init_l_Lake_instInhabitedEnv();
lean_mark_persistent(l_Lake_instInhabitedEnv);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Env(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Env(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Cache(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Env(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Env(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Env(builtin);
}
#ifdef __cplusplus
}
#endif
