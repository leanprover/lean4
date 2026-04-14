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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lake_envToBool_x3f(lean_object*);
lean_object* l_Lake_getSearchPath(lean_object*);
extern lean_object* l_Lake_sharedLibPathEnvVar;
extern lean_object* l_Lean_toolchain;
extern uint8_t l_System_Platform_isWindows;
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedLeanInstall_default;
extern lean_object* l_Lake_instInhabitedLakeInstall_default;
lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedEnv_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedEnv_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedEnv_default___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f();
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "XDG_CACHE_HOME"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0_value;
static const lean_string_object l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ".cache"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f();
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0_value;
static const lean_string_object l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Env_computeToolchain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ELAN_TOOLCHAIN"};
static const lean_object* l_Lake_Env_computeToolchain___closed__0 = (const lean_object*)&l_Lake_Env_computeToolchain___closed__0_value;
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
static const lean_string_object l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected a `NameMap`, got '"};
static const lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0 = (const lean_object*)&l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(lean_object*);
static const lean_string_object l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LAKE_PKG_URL_MAP"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0_value;
static const lean_string_object l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "'LAKE_PKG_URL_MAP' has invalid JSON: "};
static const lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___boxed(lean_object*);
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
static lean_once_cell_t l_Lake_Env_noToolchainVars___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Env_noToolchainVars___closed__14;
static lean_once_cell_t l_Lake_Env_noToolchainVars___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Env_noToolchainVars___closed__15;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instInhabitedEnv_default___closed__0_value)}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__16 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__16_value;
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2_value;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_Env_vars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Env_baseVars___closed__1_value)}};
static const lean_object* l_Lake_Env_vars___closed__0 = (const lean_object*)&l_Lake_Env_vars___closed__0_value;
static const lean_ctor_object l_Lake_Env_vars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Env_baseVars___closed__2_value)}};
static const lean_object* l_Lake_Env_vars___closed__1 = (const lean_object*)&l_Lake_Env_vars___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object*);
static lean_object* _init_l_Lake_instInhabitedEnv_default___closed__1(void){
_start:
{
lean_object* v___x_2_; uint8_t v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_2_ = lean_box(0);
v___x_3_ = 0;
v___x_4_ = lean_box(1);
v___x_5_ = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
v___x_6_ = lean_box(0);
v___x_7_ = l_Lake_instInhabitedLeanInstall_default;
v___x_8_ = l_Lake_instInhabitedLakeInstall_default;
v___x_9_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_7_);
lean_ctor_set(v___x_9_, 2, v___x_6_);
lean_ctor_set(v___x_9_, 3, v___x_5_);
lean_ctor_set(v___x_9_, 4, v___x_5_);
lean_ctor_set(v___x_9_, 5, v___x_4_);
lean_ctor_set(v___x_9_, 6, v___x_6_);
lean_ctor_set(v___x_9_, 7, v___x_6_);
lean_ctor_set(v___x_9_, 8, v___x_6_);
lean_ctor_set(v___x_9_, 9, v___x_6_);
lean_ctor_set(v___x_9_, 10, v___x_6_);
lean_ctor_set(v___x_9_, 11, v___x_6_);
lean_ctor_set(v___x_9_, 12, v___x_6_);
lean_ctor_set(v___x_9_, 13, v___x_6_);
lean_ctor_set(v___x_9_, 14, v___x_2_);
lean_ctor_set(v___x_9_, 15, v___x_2_);
lean_ctor_set(v___x_9_, 16, v___x_2_);
lean_ctor_set(v___x_9_, 17, v___x_2_);
lean_ctor_set(v___x_9_, 18, v___x_5_);
lean_ctor_set_uint8(v___x_9_, sizeof(void*)*19, v___x_3_);
lean_ctor_set_uint8(v___x_9_, sizeof(void*)*19 + 1, v___x_3_);
return v___x_9_;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv_default(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Lake_instInhabitedEnv_default___closed__1, &l_Lake_instInhabitedEnv_default___closed__1_once, _init_l_Lake_instInhabitedEnv_default___closed__1);
return v___x_10_;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lake_instInhabitedEnv_default;
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f(){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_System_Platform_isWindows;
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = ((lean_object*)(l_Lake_getUserHome_x3f___closed__0));
v___x_18_ = lean_io_getenv(v___x_17_);
if (lean_obj_tag(v___x_18_) == 1)
{
lean_object* v_val_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_26_; 
v_val_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_26_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_val_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_22_ == 0)
{
v___x_24_ = v___x_21_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_val_19_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
else
{
lean_object* v___x_27_; 
lean_dec(v___x_18_);
v___x_27_ = lean_box(0);
return v___x_27_;
}
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = ((lean_object*)(l_Lake_getUserHome_x3f___closed__1));
v___x_29_ = lean_io_getenv(v___x_28_);
if (lean_obj_tag(v___x_29_) == 1)
{
lean_object* v_val_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_val_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_val_30_);
lean_dec_ref(v___x_29_);
v___x_31_ = ((lean_object*)(l_Lake_getUserHome_x3f___closed__2));
v___x_32_ = lean_io_getenv(v___x_31_);
if (lean_obj_tag(v___x_32_) == 1)
{
lean_object* v_val_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_41_; 
v_val_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_41_ == 0)
{
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_41_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_val_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_41_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_37_ = lean_string_append(v_val_30_, v_val_33_);
lean_dec(v_val_33_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_37_);
v___x_39_ = v___x_35_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_37_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
else
{
lean_object* v___x_42_; 
lean_dec(v___x_32_);
lean_dec(v_val_30_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
else
{
lean_object* v___x_43_; 
lean_dec(v___x_29_);
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f___boxed(lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lake_getUserHome_x3f();
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(lean_object* v_userHome_x3f_48_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0));
v___x_51_ = lean_io_getenv(v___x_50_);
if (lean_obj_tag(v___x_51_) == 1)
{
lean_object* v_val_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
lean_dec(v_userHome_x3f_48_);
v_val_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_val_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_val_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
else
{
lean_dec(v___x_51_);
if (lean_obj_tag(v_userHome_x3f_48_) == 1)
{
lean_object* v_val_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_69_; 
v_val_60_ = lean_ctor_get(v_userHome_x3f_48_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v_userHome_x3f_48_);
if (v_isSharedCheck_69_ == 0)
{
v___x_62_ = v_userHome_x3f_48_;
v_isShared_63_ = v_isSharedCheck_69_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_val_60_);
lean_dec(v_userHome_x3f_48_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_69_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_64_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
v___x_65_ = l_System_FilePath_join(v_val_60_, v___x_64_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_65_);
v___x_67_ = v___x_62_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
else
{
lean_object* v___x_70_; 
lean_dec(v_userHome_x3f_48_);
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___boxed(lean_object* v_userHome_x3f_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f(){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0));
v___x_76_ = lean_io_getenv(v___x_75_);
if (lean_obj_tag(v___x_76_) == 1)
{
lean_object* v_val_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
v_val_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_val_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_val_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
else
{
lean_object* v___x_85_; 
lean_dec(v___x_76_);
v___x_85_ = l_Lake_getUserHome_x3f();
if (lean_obj_tag(v___x_85_) == 1)
{
lean_object* v_val_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_95_; 
v_val_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_95_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_95_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_val_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_95_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_90_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
v___x_91_ = l_System_FilePath_join(v_val_86_, v___x_90_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_91_);
v___x_93_ = v___x_88_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v___x_85_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f___boxed(lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lake_getSystemCacheHome_x3f();
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(lean_object* v_elan_101_, lean_object* v_toolchain_102_){
_start:
{
lean_object* v_toolchainsDir_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_toolchainsDir_103_ = lean_ctor_get(v_elan_101_, 3);
lean_inc_ref(v_toolchainsDir_103_);
lean_dec_ref(v_elan_101_);
v___x_104_ = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_102_, v___x_104_, v___x_105_);
v___x_107_ = l_System_FilePath_join(v_toolchainsDir_103_, v___x_106_);
v___x_108_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_109_ = l_System_FilePath_join(v___x_107_, v___x_108_);
v___x_110_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1));
v___x_111_ = l_System_FilePath_join(v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___boxed(lean_object* v_elan_112_, lean_object* v_toolchain_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_elan_112_, v_toolchain_113_);
lean_dec_ref(v_toolchain_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(lean_object* v_elan_115_, lean_object* v_toolchain_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_string_utf8_byte_size(v_toolchain_116_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_nat_dec_eq(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_elan_115_, v_toolchain_116_);
v___x_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
lean_dec_ref(v_elan_115_);
v___x_122_ = lean_box(0);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f___boxed(lean_object* v_elan_123_, lean_object* v_toolchain_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(v_elan_123_, v_toolchain_124_);
lean_dec_ref(v_toolchain_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain(){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lake_Env_computeToolchain___closed__0));
v___x_129_ = lean_io_getenv(v___x_128_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_toolchain;
return v___x_130_;
}
else
{
lean_object* v_val_131_; 
v_val_131_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_val_131_);
lean_dec_ref(v___x_129_);
return v_val_131_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain___boxed(lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lake_Env_computeToolchain();
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f(){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
v___x_137_ = lean_io_getenv(v___x_136_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
else
{
lean_object* v_val_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_150_; 
v_val_139_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_150_ == 0)
{
v___x_141_ = v___x_137_;
v_isShared_142_ = v_isSharedCheck_150_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_val_139_);
lean_dec(v___x_137_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_150_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_143_ = lean_string_utf8_byte_size(v_val_139_);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_nat_dec_eq(v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
lean_del_object(v___x_141_);
lean_dec(v_val_139_);
v___x_146_ = lean_box(0);
return v___x_146_;
}
else
{
lean_object* v___x_148_; 
if (v_isShared_142_ == 0)
{
v___x_148_ = v___x_141_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_val_139_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___boxed(lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f();
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfSystem_x3f(lean_object* v_cacheHome_x3f_153_){
_start:
{
if (lean_obj_tag(v_cacheHome_x3f_153_) == 0)
{
lean_object* v___x_154_; 
v___x_154_ = lean_box(0);
return v___x_154_;
}
else
{
lean_object* v_val_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_164_; 
v_val_155_ = lean_ctor_get(v_cacheHome_x3f_153_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_cacheHome_x3f_153_);
if (v_isSharedCheck_164_ == 0)
{
v___x_157_ = v_cacheHome_x3f_153_;
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_val_155_);
lean_dec(v_cacheHome_x3f_153_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_159_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_160_ = l_System_FilePath_join(v_val_155_, v___x_159_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_160_);
v___x_162_ = v___x_157_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(lean_object* v_elan_x3f_165_, lean_object* v_toolchain_166_){
_start:
{
if (lean_obj_tag(v_elan_x3f_165_) == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_180_; 
v_val_168_ = lean_ctor_get(v_elan_x3f_165_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_elan_x3f_165_);
if (v_isSharedCheck_180_ == 0)
{
v___x_170_ = v_elan_x3f_165_;
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_val_168_);
lean_dec(v_elan_x3f_165_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_172_ = lean_string_utf8_byte_size(v_toolchain_166_);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_nat_dec_eq(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_168_, v_toolchain_166_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_175_);
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
else
{
lean_object* v___x_179_; 
lean_del_object(v___x_170_);
lean_dec(v_val_168_);
v___x_179_ = lean_box(0);
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f___boxed(lean_object* v_elan_x3f_181_, lean_object* v_toolchain_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(v_elan_x3f_181_, v_toolchain_182_);
lean_dec_ref(v_toolchain_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f(lean_object* v_elan_x3f_184_, lean_object* v_toolchain_185_){
_start:
{
lean_object* v_cache_188_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
v___x_197_ = lean_io_getenv(v___x_196_);
if (lean_obj_tag(v___x_197_) == 0)
{
goto v___jp_198_;
}
else
{
lean_object* v_val_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_val_204_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_val_204_);
lean_dec_ref(v___x_197_);
v___x_205_ = lean_string_utf8_byte_size(v_val_204_);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_nat_dec_eq(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_dec(v_val_204_);
goto v___jp_198_;
}
else
{
lean_dec(v_elan_x3f_184_);
v_cache_188_ = v_val_204_;
goto v___jp_187_;
}
}
v___jp_187_:
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v_cache_188_);
return v___x_189_;
}
v___jp_190_:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lake_getSystemCacheHome_x3f();
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(0);
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_val_193_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_val_193_);
lean_dec_ref(v___x_191_);
v___x_194_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_195_ = l_System_FilePath_join(v_val_193_, v___x_194_);
v_cache_188_ = v___x_195_;
goto v___jp_187_;
}
}
v___jp_198_:
{
if (lean_obj_tag(v_elan_x3f_184_) == 0)
{
goto v___jp_190_;
}
else
{
lean_object* v_val_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_val_199_ = lean_ctor_get(v_elan_x3f_184_, 0);
lean_inc(v_val_199_);
lean_dec_ref(v_elan_x3f_184_);
v___x_200_ = lean_string_utf8_byte_size(v_toolchain_185_);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_nat_dec_eq(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_199_, v_toolchain_185_);
v_cache_188_ = v___x_203_;
goto v___jp_187_;
}
else
{
lean_dec(v_val_199_);
goto v___jp_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f___boxed(lean_object* v_elan_x3f_208_, lean_object* v_toolchain_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lake_Env_computeCache_x3f(v_elan_x3f_208_, v_toolchain_209_);
lean_dec_ref(v_toolchain_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(lean_object* v_elan_x3f_212_, lean_object* v_userHome_x3f_213_, lean_object* v_toolchain_214_, lean_object* v_env_215_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
v___x_218_ = lean_io_getenv(v___x_217_);
if (lean_obj_tag(v___x_218_) == 1)
{
lean_object* v_val_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_328_; 
lean_dec(v_userHome_x3f_213_);
lean_dec(v_elan_x3f_212_);
v_val_261_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_328_ == 0)
{
v___x_263_ = v___x_218_;
v_isShared_264_ = v_isSharedCheck_328_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_val_261_);
lean_dec(v___x_218_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_328_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_265_ = lean_string_utf8_byte_size(v_val_261_);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_nat_dec_eq(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v_lake_268_; lean_object* v_lean_269_; lean_object* v_elan_x3f_270_; lean_object* v_reservoirApiUrl_271_; lean_object* v_githashOverride_272_; lean_object* v_pkgUrlMap_273_; uint8_t v_noCache_274_; lean_object* v_enableArtifactCache_x3f_275_; uint8_t v_noSystemCache_276_; lean_object* v_lakeConfig_x3f_277_; lean_object* v_cacheKey_x3f_278_; lean_object* v_cacheArtifactEndpoint_x3f_279_; lean_object* v_cacheRevisionEndpoint_x3f_280_; lean_object* v_cacheService_x3f_281_; lean_object* v_initLeanPath_282_; lean_object* v_initLeanSrcPath_283_; lean_object* v_initSharedLibPath_284_; lean_object* v_initPath_285_; lean_object* v_toolchain_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_297_; 
v_lake_268_ = lean_ctor_get(v_env_215_, 0);
v_lean_269_ = lean_ctor_get(v_env_215_, 1);
v_elan_x3f_270_ = lean_ctor_get(v_env_215_, 2);
v_reservoirApiUrl_271_ = lean_ctor_get(v_env_215_, 3);
v_githashOverride_272_ = lean_ctor_get(v_env_215_, 4);
v_pkgUrlMap_273_ = lean_ctor_get(v_env_215_, 5);
v_noCache_274_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*19);
v_enableArtifactCache_x3f_275_ = lean_ctor_get(v_env_215_, 6);
v_noSystemCache_276_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*19 + 1);
v_lakeConfig_x3f_277_ = lean_ctor_get(v_env_215_, 9);
v_cacheKey_x3f_278_ = lean_ctor_get(v_env_215_, 10);
v_cacheArtifactEndpoint_x3f_279_ = lean_ctor_get(v_env_215_, 11);
v_cacheRevisionEndpoint_x3f_280_ = lean_ctor_get(v_env_215_, 12);
v_cacheService_x3f_281_ = lean_ctor_get(v_env_215_, 13);
v_initLeanPath_282_ = lean_ctor_get(v_env_215_, 14);
v_initLeanSrcPath_283_ = lean_ctor_get(v_env_215_, 15);
v_initSharedLibPath_284_ = lean_ctor_get(v_env_215_, 16);
v_initPath_285_ = lean_ctor_get(v_env_215_, 17);
v_toolchain_286_ = lean_ctor_get(v_env_215_, 18);
v_isSharedCheck_297_ = !lean_is_exclusive(v_env_215_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; lean_object* v_unused_299_; 
v_unused_298_ = lean_ctor_get(v_env_215_, 8);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_env_215_, 7);
lean_dec(v_unused_299_);
v___x_288_ = v_env_215_;
v_isShared_289_ = v_isSharedCheck_297_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_toolchain_286_);
lean_inc(v_initPath_285_);
lean_inc(v_initSharedLibPath_284_);
lean_inc(v_initLeanSrcPath_283_);
lean_inc(v_initLeanPath_282_);
lean_inc(v_cacheService_x3f_281_);
lean_inc(v_cacheRevisionEndpoint_x3f_280_);
lean_inc(v_cacheArtifactEndpoint_x3f_279_);
lean_inc(v_cacheKey_x3f_278_);
lean_inc(v_lakeConfig_x3f_277_);
lean_inc(v_enableArtifactCache_x3f_275_);
lean_inc(v_pkgUrlMap_273_);
lean_inc(v_githashOverride_272_);
lean_inc(v_reservoirApiUrl_271_);
lean_inc(v_elan_x3f_270_);
lean_inc(v_lean_269_);
lean_inc(v_lake_268_);
lean_dec(v_env_215_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_297_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_264_ == 0)
{
v___x_291_ = v___x_263_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_val_261_);
v___x_291_ = v_reuseFailAlloc_296_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_293_; 
lean_inc_ref(v___x_291_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 8, v___x_291_);
lean_ctor_set(v___x_288_, 7, v___x_291_);
v___x_293_ = v___x_288_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_lake_268_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_lean_269_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_elan_x3f_270_);
lean_ctor_set(v_reuseFailAlloc_295_, 3, v_reservoirApiUrl_271_);
lean_ctor_set(v_reuseFailAlloc_295_, 4, v_githashOverride_272_);
lean_ctor_set(v_reuseFailAlloc_295_, 5, v_pkgUrlMap_273_);
lean_ctor_set(v_reuseFailAlloc_295_, 6, v_enableArtifactCache_x3f_275_);
lean_ctor_set(v_reuseFailAlloc_295_, 7, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_295_, 8, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_295_, 9, v_lakeConfig_x3f_277_);
lean_ctor_set(v_reuseFailAlloc_295_, 10, v_cacheKey_x3f_278_);
lean_ctor_set(v_reuseFailAlloc_295_, 11, v_cacheArtifactEndpoint_x3f_279_);
lean_ctor_set(v_reuseFailAlloc_295_, 12, v_cacheRevisionEndpoint_x3f_280_);
lean_ctor_set(v_reuseFailAlloc_295_, 13, v_cacheService_x3f_281_);
lean_ctor_set(v_reuseFailAlloc_295_, 14, v_initLeanPath_282_);
lean_ctor_set(v_reuseFailAlloc_295_, 15, v_initLeanSrcPath_283_);
lean_ctor_set(v_reuseFailAlloc_295_, 16, v_initSharedLibPath_284_);
lean_ctor_set(v_reuseFailAlloc_295_, 17, v_initPath_285_);
lean_ctor_set(v_reuseFailAlloc_295_, 18, v_toolchain_286_);
lean_ctor_set_uint8(v_reuseFailAlloc_295_, sizeof(void*)*19, v_noCache_274_);
lean_ctor_set_uint8(v_reuseFailAlloc_295_, sizeof(void*)*19 + 1, v_noSystemCache_276_);
v___x_293_ = v_reuseFailAlloc_295_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
}
else
{
lean_object* v_lake_300_; lean_object* v_lean_301_; lean_object* v_elan_x3f_302_; lean_object* v_reservoirApiUrl_303_; lean_object* v_githashOverride_304_; lean_object* v_pkgUrlMap_305_; uint8_t v_noCache_306_; lean_object* v_enableArtifactCache_x3f_307_; lean_object* v_lakeCache_x3f_308_; lean_object* v_lakeSystemCache_x3f_309_; lean_object* v_lakeConfig_x3f_310_; lean_object* v_cacheKey_x3f_311_; lean_object* v_cacheArtifactEndpoint_x3f_312_; lean_object* v_cacheRevisionEndpoint_x3f_313_; lean_object* v_cacheService_x3f_314_; lean_object* v_initLeanPath_315_; lean_object* v_initLeanSrcPath_316_; lean_object* v_initSharedLibPath_317_; lean_object* v_initPath_318_; lean_object* v_toolchain_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_327_; 
lean_del_object(v___x_263_);
lean_dec(v_val_261_);
v_lake_300_ = lean_ctor_get(v_env_215_, 0);
v_lean_301_ = lean_ctor_get(v_env_215_, 1);
v_elan_x3f_302_ = lean_ctor_get(v_env_215_, 2);
v_reservoirApiUrl_303_ = lean_ctor_get(v_env_215_, 3);
v_githashOverride_304_ = lean_ctor_get(v_env_215_, 4);
v_pkgUrlMap_305_ = lean_ctor_get(v_env_215_, 5);
v_noCache_306_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*19);
v_enableArtifactCache_x3f_307_ = lean_ctor_get(v_env_215_, 6);
v_lakeCache_x3f_308_ = lean_ctor_get(v_env_215_, 7);
v_lakeSystemCache_x3f_309_ = lean_ctor_get(v_env_215_, 8);
v_lakeConfig_x3f_310_ = lean_ctor_get(v_env_215_, 9);
v_cacheKey_x3f_311_ = lean_ctor_get(v_env_215_, 10);
v_cacheArtifactEndpoint_x3f_312_ = lean_ctor_get(v_env_215_, 11);
v_cacheRevisionEndpoint_x3f_313_ = lean_ctor_get(v_env_215_, 12);
v_cacheService_x3f_314_ = lean_ctor_get(v_env_215_, 13);
v_initLeanPath_315_ = lean_ctor_get(v_env_215_, 14);
v_initLeanSrcPath_316_ = lean_ctor_get(v_env_215_, 15);
v_initSharedLibPath_317_ = lean_ctor_get(v_env_215_, 16);
v_initPath_318_ = lean_ctor_get(v_env_215_, 17);
v_toolchain_319_ = lean_ctor_get(v_env_215_, 18);
v_isSharedCheck_327_ = !lean_is_exclusive(v_env_215_);
if (v_isSharedCheck_327_ == 0)
{
v___x_321_ = v_env_215_;
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_toolchain_319_);
lean_inc(v_initPath_318_);
lean_inc(v_initSharedLibPath_317_);
lean_inc(v_initLeanSrcPath_316_);
lean_inc(v_initLeanPath_315_);
lean_inc(v_cacheService_x3f_314_);
lean_inc(v_cacheRevisionEndpoint_x3f_313_);
lean_inc(v_cacheArtifactEndpoint_x3f_312_);
lean_inc(v_cacheKey_x3f_311_);
lean_inc(v_lakeConfig_x3f_310_);
lean_inc(v_lakeSystemCache_x3f_309_);
lean_inc(v_lakeCache_x3f_308_);
lean_inc(v_enableArtifactCache_x3f_307_);
lean_inc(v_pkgUrlMap_305_);
lean_inc(v_githashOverride_304_);
lean_inc(v_reservoirApiUrl_303_);
lean_inc(v_elan_x3f_302_);
lean_inc(v_lean_301_);
lean_inc(v_lake_300_);
lean_dec(v_env_215_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_lake_300_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_lean_301_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_elan_x3f_302_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_reservoirApiUrl_303_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_githashOverride_304_);
lean_ctor_set(v_reuseFailAlloc_326_, 5, v_pkgUrlMap_305_);
lean_ctor_set(v_reuseFailAlloc_326_, 6, v_enableArtifactCache_x3f_307_);
lean_ctor_set(v_reuseFailAlloc_326_, 7, v_lakeCache_x3f_308_);
lean_ctor_set(v_reuseFailAlloc_326_, 8, v_lakeSystemCache_x3f_309_);
lean_ctor_set(v_reuseFailAlloc_326_, 9, v_lakeConfig_x3f_310_);
lean_ctor_set(v_reuseFailAlloc_326_, 10, v_cacheKey_x3f_311_);
lean_ctor_set(v_reuseFailAlloc_326_, 11, v_cacheArtifactEndpoint_x3f_312_);
lean_ctor_set(v_reuseFailAlloc_326_, 12, v_cacheRevisionEndpoint_x3f_313_);
lean_ctor_set(v_reuseFailAlloc_326_, 13, v_cacheService_x3f_314_);
lean_ctor_set(v_reuseFailAlloc_326_, 14, v_initLeanPath_315_);
lean_ctor_set(v_reuseFailAlloc_326_, 15, v_initLeanSrcPath_316_);
lean_ctor_set(v_reuseFailAlloc_326_, 16, v_initSharedLibPath_317_);
lean_ctor_set(v_reuseFailAlloc_326_, 17, v_initPath_318_);
lean_ctor_set(v_reuseFailAlloc_326_, 18, v_toolchain_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_326_, sizeof(void*)*19, v_noCache_306_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; 
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*19 + 1, v___x_267_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
}
}
}
else
{
lean_dec(v___x_218_);
if (lean_obj_tag(v_elan_x3f_212_) == 0)
{
goto v___jp_219_;
}
else
{
lean_object* v_val_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_383_; 
v_val_329_ = lean_ctor_get(v_elan_x3f_212_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_elan_x3f_212_);
if (v_isSharedCheck_383_ == 0)
{
v___x_331_ = v_elan_x3f_212_;
v_isShared_332_ = v_isSharedCheck_383_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_val_329_);
lean_dec(v_elan_x3f_212_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_383_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_333_ = lean_string_utf8_byte_size(v_toolchain_214_);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_nat_dec_eq(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_336_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_213_);
v___x_337_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_329_, v_toolchain_214_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_337_);
v___x_339_ = v___x_331_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_382_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___y_341_; 
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
v___y_341_ = v___x_371_;
goto v___jp_340_;
}
else
{
lean_object* v_val_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_381_; 
v_val_372_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_381_ == 0)
{
v___x_374_ = v___x_336_;
v_isShared_375_ = v_isSharedCheck_381_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_val_372_);
lean_dec(v___x_336_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_381_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_376_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_377_ = l_System_FilePath_join(v_val_372_, v___x_376_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_377_);
v___x_379_ = v___x_374_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
v___y_341_ = v___x_379_;
goto v___jp_340_;
}
}
}
v___jp_340_:
{
lean_object* v_lake_342_; lean_object* v_lean_343_; lean_object* v_elan_x3f_344_; lean_object* v_reservoirApiUrl_345_; lean_object* v_githashOverride_346_; lean_object* v_pkgUrlMap_347_; uint8_t v_noCache_348_; lean_object* v_enableArtifactCache_x3f_349_; uint8_t v_noSystemCache_350_; lean_object* v_lakeConfig_x3f_351_; lean_object* v_cacheKey_x3f_352_; lean_object* v_cacheArtifactEndpoint_x3f_353_; lean_object* v_cacheRevisionEndpoint_x3f_354_; lean_object* v_cacheService_x3f_355_; lean_object* v_initLeanPath_356_; lean_object* v_initLeanSrcPath_357_; lean_object* v_initSharedLibPath_358_; lean_object* v_initPath_359_; lean_object* v_toolchain_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_368_; 
v_lake_342_ = lean_ctor_get(v_env_215_, 0);
v_lean_343_ = lean_ctor_get(v_env_215_, 1);
v_elan_x3f_344_ = lean_ctor_get(v_env_215_, 2);
v_reservoirApiUrl_345_ = lean_ctor_get(v_env_215_, 3);
v_githashOverride_346_ = lean_ctor_get(v_env_215_, 4);
v_pkgUrlMap_347_ = lean_ctor_get(v_env_215_, 5);
v_noCache_348_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*19);
v_enableArtifactCache_x3f_349_ = lean_ctor_get(v_env_215_, 6);
v_noSystemCache_350_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*19 + 1);
v_lakeConfig_x3f_351_ = lean_ctor_get(v_env_215_, 9);
v_cacheKey_x3f_352_ = lean_ctor_get(v_env_215_, 10);
v_cacheArtifactEndpoint_x3f_353_ = lean_ctor_get(v_env_215_, 11);
v_cacheRevisionEndpoint_x3f_354_ = lean_ctor_get(v_env_215_, 12);
v_cacheService_x3f_355_ = lean_ctor_get(v_env_215_, 13);
v_initLeanPath_356_ = lean_ctor_get(v_env_215_, 14);
v_initLeanSrcPath_357_ = lean_ctor_get(v_env_215_, 15);
v_initSharedLibPath_358_ = lean_ctor_get(v_env_215_, 16);
v_initPath_359_ = lean_ctor_get(v_env_215_, 17);
v_toolchain_360_ = lean_ctor_get(v_env_215_, 18);
v_isSharedCheck_368_ = !lean_is_exclusive(v_env_215_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; 
v_unused_369_ = lean_ctor_get(v_env_215_, 8);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_env_215_, 7);
lean_dec(v_unused_370_);
v___x_362_ = v_env_215_;
v_isShared_363_ = v_isSharedCheck_368_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_toolchain_360_);
lean_inc(v_initPath_359_);
lean_inc(v_initSharedLibPath_358_);
lean_inc(v_initLeanSrcPath_357_);
lean_inc(v_initLeanPath_356_);
lean_inc(v_cacheService_x3f_355_);
lean_inc(v_cacheRevisionEndpoint_x3f_354_);
lean_inc(v_cacheArtifactEndpoint_x3f_353_);
lean_inc(v_cacheKey_x3f_352_);
lean_inc(v_lakeConfig_x3f_351_);
lean_inc(v_enableArtifactCache_x3f_349_);
lean_inc(v_pkgUrlMap_347_);
lean_inc(v_githashOverride_346_);
lean_inc(v_reservoirApiUrl_345_);
lean_inc(v_elan_x3f_344_);
lean_inc(v_lean_343_);
lean_inc(v_lake_342_);
lean_dec(v_env_215_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_368_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 8, v___y_341_);
lean_ctor_set(v___x_362_, 7, v___x_339_);
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_lake_342_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_lean_343_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_elan_x3f_344_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_reservoirApiUrl_345_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v_githashOverride_346_);
lean_ctor_set(v_reuseFailAlloc_367_, 5, v_pkgUrlMap_347_);
lean_ctor_set(v_reuseFailAlloc_367_, 6, v_enableArtifactCache_x3f_349_);
lean_ctor_set(v_reuseFailAlloc_367_, 7, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_367_, 8, v___y_341_);
lean_ctor_set(v_reuseFailAlloc_367_, 9, v_lakeConfig_x3f_351_);
lean_ctor_set(v_reuseFailAlloc_367_, 10, v_cacheKey_x3f_352_);
lean_ctor_set(v_reuseFailAlloc_367_, 11, v_cacheArtifactEndpoint_x3f_353_);
lean_ctor_set(v_reuseFailAlloc_367_, 12, v_cacheRevisionEndpoint_x3f_354_);
lean_ctor_set(v_reuseFailAlloc_367_, 13, v_cacheService_x3f_355_);
lean_ctor_set(v_reuseFailAlloc_367_, 14, v_initLeanPath_356_);
lean_ctor_set(v_reuseFailAlloc_367_, 15, v_initLeanSrcPath_357_);
lean_ctor_set(v_reuseFailAlloc_367_, 16, v_initSharedLibPath_358_);
lean_ctor_set(v_reuseFailAlloc_367_, 17, v_initPath_359_);
lean_ctor_set(v_reuseFailAlloc_367_, 18, v_toolchain_360_);
lean_ctor_set_uint8(v_reuseFailAlloc_367_, sizeof(void*)*19, v_noCache_348_);
lean_ctor_set_uint8(v_reuseFailAlloc_367_, sizeof(void*)*19 + 1, v_noSystemCache_350_);
v___x_365_ = v_reuseFailAlloc_367_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
}
}
}
else
{
lean_del_object(v___x_331_);
lean_dec(v_val_329_);
goto v___jp_219_;
}
}
}
}
v___jp_219_:
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_213_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v_env_215_);
return v___x_221_;
}
else
{
lean_object* v_val_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_260_; 
v_val_222_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_260_ == 0)
{
v___x_224_ = v___x_220_;
v_isShared_225_ = v_isSharedCheck_260_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_val_222_);
lean_dec(v___x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_260_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v_lake_226_; lean_object* v_lean_227_; lean_object* v_elan_x3f_228_; lean_object* v_reservoirApiUrl_229_; lean_object* v_githashOverride_230_; lean_object* v_pkgUrlMap_231_; uint8_t v_noCache_232_; lean_object* v_enableArtifactCache_x3f_233_; uint8_t v_noSystemCache_234_; lean_object* v_lakeConfig_x3f_235_; lean_object* v_cacheKey_x3f_236_; lean_object* v_cacheArtifactEndpoint_x3f_237_; lean_object* v_cacheRevisionEndpoint_x3f_238_; lean_object* v_cacheService_x3f_239_; lean_object* v_initLeanPath_240_; lean_object* v_initLeanSrcPath_241_; lean_object* v_initSharedLibPath_242_; lean_object* v_initPath_243_; lean_object* v_toolchain_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_257_; 
v_lake_226_ = lean_ctor_get(v_env_215_, 0);
v_lean_227_ = lean_ctor_get(v_env_215_, 1);
v_elan_x3f_228_ = lean_ctor_get(v_env_215_, 2);
v_reservoirApiUrl_229_ = lean_ctor_get(v_env_215_, 3);
v_githashOverride_230_ = lean_ctor_get(v_env_215_, 4);
v_pkgUrlMap_231_ = lean_ctor_get(v_env_215_, 5);
v_noCache_232_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*19);
v_enableArtifactCache_x3f_233_ = lean_ctor_get(v_env_215_, 6);
v_noSystemCache_234_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*19 + 1);
v_lakeConfig_x3f_235_ = lean_ctor_get(v_env_215_, 9);
v_cacheKey_x3f_236_ = lean_ctor_get(v_env_215_, 10);
v_cacheArtifactEndpoint_x3f_237_ = lean_ctor_get(v_env_215_, 11);
v_cacheRevisionEndpoint_x3f_238_ = lean_ctor_get(v_env_215_, 12);
v_cacheService_x3f_239_ = lean_ctor_get(v_env_215_, 13);
v_initLeanPath_240_ = lean_ctor_get(v_env_215_, 14);
v_initLeanSrcPath_241_ = lean_ctor_get(v_env_215_, 15);
v_initSharedLibPath_242_ = lean_ctor_get(v_env_215_, 16);
v_initPath_243_ = lean_ctor_get(v_env_215_, 17);
v_toolchain_244_ = lean_ctor_get(v_env_215_, 18);
v_isSharedCheck_257_ = !lean_is_exclusive(v_env_215_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; lean_object* v_unused_259_; 
v_unused_258_ = lean_ctor_get(v_env_215_, 8);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_env_215_, 7);
lean_dec(v_unused_259_);
v___x_246_ = v_env_215_;
v_isShared_247_ = v_isSharedCheck_257_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_toolchain_244_);
lean_inc(v_initPath_243_);
lean_inc(v_initSharedLibPath_242_);
lean_inc(v_initLeanSrcPath_241_);
lean_inc(v_initLeanPath_240_);
lean_inc(v_cacheService_x3f_239_);
lean_inc(v_cacheRevisionEndpoint_x3f_238_);
lean_inc(v_cacheArtifactEndpoint_x3f_237_);
lean_inc(v_cacheKey_x3f_236_);
lean_inc(v_lakeConfig_x3f_235_);
lean_inc(v_enableArtifactCache_x3f_233_);
lean_inc(v_pkgUrlMap_231_);
lean_inc(v_githashOverride_230_);
lean_inc(v_reservoirApiUrl_229_);
lean_inc(v_elan_x3f_228_);
lean_inc(v_lean_227_);
lean_inc(v_lake_226_);
lean_dec(v_env_215_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_257_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_248_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_249_ = l_System_FilePath_join(v_val_222_, v___x_248_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_249_);
v___x_251_ = v___x_224_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_256_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_253_; 
lean_inc_ref(v___x_251_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 8, v___x_251_);
lean_ctor_set(v___x_246_, 7, v___x_251_);
v___x_253_ = v___x_246_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_lake_226_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_lean_227_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_elan_x3f_228_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_reservoirApiUrl_229_);
lean_ctor_set(v_reuseFailAlloc_255_, 4, v_githashOverride_230_);
lean_ctor_set(v_reuseFailAlloc_255_, 5, v_pkgUrlMap_231_);
lean_ctor_set(v_reuseFailAlloc_255_, 6, v_enableArtifactCache_x3f_233_);
lean_ctor_set(v_reuseFailAlloc_255_, 7, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_255_, 8, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_255_, 9, v_lakeConfig_x3f_235_);
lean_ctor_set(v_reuseFailAlloc_255_, 10, v_cacheKey_x3f_236_);
lean_ctor_set(v_reuseFailAlloc_255_, 11, v_cacheArtifactEndpoint_x3f_237_);
lean_ctor_set(v_reuseFailAlloc_255_, 12, v_cacheRevisionEndpoint_x3f_238_);
lean_ctor_set(v_reuseFailAlloc_255_, 13, v_cacheService_x3f_239_);
lean_ctor_set(v_reuseFailAlloc_255_, 14, v_initLeanPath_240_);
lean_ctor_set(v_reuseFailAlloc_255_, 15, v_initLeanSrcPath_241_);
lean_ctor_set(v_reuseFailAlloc_255_, 16, v_initSharedLibPath_242_);
lean_ctor_set(v_reuseFailAlloc_255_, 17, v_initPath_243_);
lean_ctor_set(v_reuseFailAlloc_255_, 18, v_toolchain_244_);
lean_ctor_set_uint8(v_reuseFailAlloc_255_, sizeof(void*)*19, v_noCache_232_);
lean_ctor_set_uint8(v_reuseFailAlloc_255_, sizeof(void*)*19 + 1, v_noSystemCache_234_);
v___x_253_ = v_reuseFailAlloc_255_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs___boxed(lean_object* v_elan_x3f_384_, lean_object* v_userHome_x3f_385_, lean_object* v_toolchain_386_, lean_object* v_env_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(v_elan_x3f_384_, v_userHome_x3f_385_, v_toolchain_386_, v_env_387_);
lean_dec_ref(v_toolchain_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(lean_object* v_init_393_, lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v_k_395_; lean_object* v_v_396_; lean_object* v_l_397_; lean_object* v_r_398_; lean_object* v___x_399_; 
v_k_395_ = lean_ctor_get(v_x_394_, 1);
lean_inc(v_k_395_);
v_v_396_ = lean_ctor_get(v_x_394_, 2);
lean_inc(v_v_396_);
v_l_397_ = lean_ctor_get(v_x_394_, 3);
lean_inc(v_l_397_);
v_r_398_ = lean_ctor_get(v_x_394_, 4);
lean_inc(v_r_398_);
lean_dec_ref(v_x_394_);
v___x_399_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(v_init_393_, v_l_397_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_dec(v_r_398_);
lean_dec(v_v_396_);
lean_dec(v_k_395_);
return v___x_399_;
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_440_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_440_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_440_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_440_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0));
v___x_405_ = lean_string_dec_eq(v_k_395_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v_n_406_; uint8_t v___x_407_; 
lean_inc(v_k_395_);
v_n_406_ = l_String_toName(v_k_395_);
v___x_407_ = l_Lean_Name_isAnonymous(v_n_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_del_object(v___x_402_);
lean_dec(v_k_395_);
v___x_408_ = l_Lean_Json_getStr_x3f(v_v_396_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec(v_n_406_);
lean_dec(v_a_400_);
lean_dec(v_r_398_);
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_418_; 
v_a_417_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_417_);
lean_dec_ref(v___x_408_);
v___x_418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_406_, v_a_417_, v_a_400_);
v_init_393_ = v___x_418_;
v_x_394_ = v_r_398_;
goto _start;
}
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_dec(v_n_406_);
lean_dec(v_a_400_);
lean_dec(v_r_398_);
lean_dec(v_v_396_);
v___x_420_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1));
v___x_421_ = lean_string_append(v___x_420_, v_k_395_);
lean_dec(v_k_395_);
v___x_422_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
v___x_423_ = lean_string_append(v___x_421_, v___x_422_);
if (v_isShared_403_ == 0)
{
lean_ctor_set_tag(v___x_402_, 0);
lean_ctor_set(v___x_402_, 0, v___x_423_);
v___x_425_ = v___x_402_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
else
{
lean_object* v___x_427_; 
lean_del_object(v___x_402_);
lean_dec(v_k_395_);
v___x_427_ = l_Lean_Json_getStr_x3f(v_v_396_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_a_400_);
lean_dec(v_r_398_);
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_a_436_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_436_);
lean_dec_ref(v___x_427_);
v___x_437_ = lean_box(0);
v___x_438_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_437_, v_a_436_, v_a_400_);
v_init_393_ = v___x_438_;
v_x_394_ = v_r_398_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v_init_393_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(lean_object* v_x_443_){
_start:
{
if (lean_obj_tag(v_x_443_) == 5)
{
lean_object* v_kvPairs_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_kvPairs_444_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_kvPairs_444_);
lean_dec_ref(v_x_443_);
v___x_445_ = lean_box(1);
v___x_446_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(v___x_445_, v_kvPairs_444_);
return v___x_446_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_447_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0));
v___x_448_ = lean_unsigned_to_nat(80u);
v___x_449_ = l_Lean_Json_pretty(v_x_443_, v___x_448_);
v___x_450_ = lean_string_append(v___x_447_, v___x_449_);
lean_dec_ref(v___x_449_);
v___x_451_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
v___x_452_ = lean_string_append(v___x_450_, v___x_451_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap(){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v_a_460_; 
v___x_457_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0));
v___x_458_ = lean_io_getenv(v___x_457_);
if (lean_obj_tag(v___x_458_) == 1)
{
lean_object* v_val_464_; lean_object* v___x_465_; 
v_val_464_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_val_464_);
lean_dec_ref(v___x_458_);
v___x_465_ = l_Lean_Json_parse(v_val_464_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref(v___x_465_);
v_a_460_ = v_a_466_;
goto v___jp_459_;
}
else
{
lean_object* v_a_467_; lean_object* v___x_468_; 
v_a_467_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_467_);
lean_dec_ref(v___x_465_);
v___x_468_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(v_a_467_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v___x_468_);
v_a_460_ = v_a_469_;
goto v___jp_459_;
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
v_a_470_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_468_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_468_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set_tag(v___x_472_, 0);
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v___x_458_);
v___x_478_ = lean_box(1);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
v___jp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1));
v___x_462_ = lean_string_append(v___x_461_, v_a_460_);
lean_dec_ref(v_a_460_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___boxed(lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(lean_object* v_url_482_){
_start:
{
uint32_t v___y_484_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_string_utf8_byte_size(v_url_482_);
lean_inc_ref(v_url_482_);
v___x_495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_495_, 0, v_url_482_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
lean_ctor_set(v___x_495_, 2, v___x_494_);
v___x_496_ = l_String_Slice_Pos_prev_x3f(v___x_495_, v___x_494_);
if (lean_obj_tag(v___x_496_) == 0)
{
uint32_t v___x_497_; 
lean_dec_ref(v___x_495_);
v___x_497_ = 65;
v___y_484_ = v___x_497_;
goto v___jp_483_;
}
else
{
lean_object* v_val_498_; lean_object* v___x_499_; 
v_val_498_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_val_498_);
lean_dec_ref(v___x_496_);
v___x_499_ = l_String_Slice_Pos_get_x3f(v___x_495_, v_val_498_);
lean_dec(v_val_498_);
lean_dec_ref(v___x_495_);
if (lean_obj_tag(v___x_499_) == 0)
{
uint32_t v___x_500_; 
v___x_500_ = 65;
v___y_484_ = v___x_500_;
goto v___jp_483_;
}
else
{
lean_object* v_val_501_; uint32_t v___x_502_; 
v_val_501_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_val_501_);
lean_dec_ref(v___x_499_);
v___x_502_ = lean_unbox_uint32(v_val_501_);
lean_dec(v_val_501_);
v___y_484_ = v___x_502_;
goto v___jp_483_;
}
}
v___jp_483_:
{
uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 47;
v___x_486_ = lean_uint32_dec_eq(v___y_484_, v___x_485_);
if (v___x_486_ == 0)
{
return v_url_482_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = lean_string_utf8_byte_size(v_url_482_);
lean_inc_ref(v_url_482_);
v___x_490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_490_, 0, v_url_482_);
lean_ctor_set(v___x_490_, 1, v___x_488_);
lean_ctor_set(v___x_490_, 2, v___x_489_);
v___x_491_ = l_String_Slice_Pos_prevn(v___x_490_, v___x_489_, v___x_487_);
lean_dec_ref(v___x_490_);
v___x_492_ = lean_string_utf8_extract(v_url_482_, v___x_488_, v___x_491_);
lean_dec(v___x_491_);
lean_dec_ref(v_url_482_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object* v_lake_520_, lean_object* v_lean_521_, lean_object* v_elan_x3f_522_, lean_object* v_noCache_523_){
_start:
{
lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; uint8_t v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; uint8_t v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; uint8_t v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; uint8_t v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; uint8_t v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; uint8_t v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; uint8_t v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; uint8_t v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; uint8_t v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; uint8_t v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; uint8_t v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v_val_691_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; uint8_t v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; uint8_t v___y_734_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v_a_782_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_a_812_; 
v___x_809_ = ((lean_object*)(l_Lake_Env_compute___closed__13));
v___x_810_ = lean_io_getenv(v___x_809_);
if (lean_obj_tag(v___x_810_) == 1)
{
lean_object* v_val_831_; lean_object* v___x_832_; 
v_val_831_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_val_831_);
lean_dec_ref(v___x_810_);
v___x_832_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_831_);
v_a_812_ = v___x_832_;
goto v___jp_811_;
}
else
{
lean_object* v___x_833_; 
lean_dec(v___x_810_);
v___x_833_ = ((lean_object*)(l_Lake_Env_compute___closed__16));
v_a_812_ = v___x_833_;
goto v___jp_811_;
}
v___jp_525_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_inc_ref(v___y_530_);
lean_inc_n(v___y_533_, 2);
lean_inc(v_elan_x3f_522_);
v___x_544_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v___x_544_, 0, v_lake_520_);
lean_ctor_set(v___x_544_, 1, v_lean_521_);
lean_ctor_set(v___x_544_, 2, v_elan_x3f_522_);
lean_ctor_set(v___x_544_, 3, v___y_542_);
lean_ctor_set(v___x_544_, 4, v___y_540_);
lean_ctor_set(v___x_544_, 5, v___y_537_);
lean_ctor_set(v___x_544_, 6, v___y_528_);
lean_ctor_set(v___x_544_, 7, v___y_533_);
lean_ctor_set(v___x_544_, 8, v___y_533_);
lean_ctor_set(v___x_544_, 9, v___y_538_);
lean_ctor_set(v___x_544_, 10, v___y_532_);
lean_ctor_set(v___x_544_, 11, v___y_535_);
lean_ctor_set(v___x_544_, 12, v___y_539_);
lean_ctor_set(v___x_544_, 13, v___y_543_);
lean_ctor_set(v___x_544_, 14, v___y_526_);
lean_ctor_set(v___x_544_, 15, v___y_531_);
lean_ctor_set(v___x_544_, 16, v___y_529_);
lean_ctor_set(v___x_544_, 17, v___y_536_);
lean_ctor_set(v___x_544_, 18, v___y_530_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*19, v___y_541_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*19 + 1, v___y_534_);
v___x_545_ = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(v_elan_x3f_522_, v___y_527_, v___y_530_, v___x_544_);
lean_dec_ref(v___y_530_);
return v___x_545_;
}
v___jp_546_:
{
if (lean_obj_tag(v___y_562_) == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_box(0);
v___y_526_ = v___y_547_;
v___y_527_ = v___y_548_;
v___y_528_ = v___y_549_;
v___y_529_ = v___y_550_;
v___y_530_ = v___y_551_;
v___y_531_ = v___y_552_;
v___y_532_ = v___y_553_;
v___y_533_ = v___y_554_;
v___y_534_ = v___y_555_;
v___y_535_ = v___y_556_;
v___y_536_ = v___y_557_;
v___y_537_ = v___y_558_;
v___y_538_ = v___y_559_;
v___y_539_ = v___y_564_;
v___y_540_ = v___y_560_;
v___y_541_ = v___y_561_;
v___y_542_ = v___y_563_;
v___y_543_ = v___x_565_;
goto v___jp_525_;
}
else
{
lean_object* v_val_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_581_; 
v_val_566_ = lean_ctor_get(v___y_562_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___y_562_);
if (v_isSharedCheck_581_ == 0)
{
v___x_568_ = v___y_562_;
v_isShared_569_ = v_isSharedCheck_581_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_val_566_);
lean_dec(v___y_562_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_581_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v_str_574_; lean_object* v_startInclusive_575_; lean_object* v_endExclusive_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_string_utf8_byte_size(v_val_566_);
v___x_572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_572_, 0, v_val_566_);
lean_ctor_set(v___x_572_, 1, v___x_570_);
lean_ctor_set(v___x_572_, 2, v___x_571_);
v___x_573_ = l_String_Slice_trimAscii(v___x_572_);
v_str_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref(v_str_574_);
v_startInclusive_575_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_startInclusive_575_);
v_endExclusive_576_ = lean_ctor_get(v___x_573_, 2);
lean_inc(v_endExclusive_576_);
lean_dec_ref(v___x_573_);
v___x_577_ = lean_string_utf8_extract(v_str_574_, v_startInclusive_575_, v_endExclusive_576_);
lean_dec(v_endExclusive_576_);
lean_dec(v_startInclusive_575_);
lean_dec_ref(v_str_574_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_577_);
v___x_579_ = v___x_568_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
v___y_526_ = v___y_547_;
v___y_527_ = v___y_548_;
v___y_528_ = v___y_549_;
v___y_529_ = v___y_550_;
v___y_530_ = v___y_551_;
v___y_531_ = v___y_552_;
v___y_532_ = v___y_553_;
v___y_533_ = v___y_554_;
v___y_534_ = v___y_555_;
v___y_535_ = v___y_556_;
v___y_536_ = v___y_557_;
v___y_537_ = v___y_558_;
v___y_538_ = v___y_559_;
v___y_539_ = v___y_564_;
v___y_540_ = v___y_560_;
v___y_541_ = v___y_561_;
v___y_542_ = v___y_563_;
v___y_543_ = v___x_579_;
goto v___jp_525_;
}
}
}
}
v___jp_582_:
{
if (lean_obj_tag(v___y_583_) == 0)
{
v___y_547_ = v___y_584_;
v___y_548_ = v___y_585_;
v___y_549_ = v___y_586_;
v___y_550_ = v___y_587_;
v___y_551_ = v___y_588_;
v___y_552_ = v___y_589_;
v___y_553_ = v___y_590_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_600_;
v___y_557_ = v___y_593_;
v___y_558_ = v___y_594_;
v___y_559_ = v___y_595_;
v___y_560_ = v___y_596_;
v___y_561_ = v___y_597_;
v___y_562_ = v___y_598_;
v___y_563_ = v___y_599_;
v___y_564_ = v___y_583_;
goto v___jp_546_;
}
else
{
lean_object* v_val_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
v_val_601_ = lean_ctor_get(v___y_583_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___y_583_);
if (v_isSharedCheck_609_ == 0)
{
v___x_603_ = v___y_583_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_val_601_);
lean_dec(v___y_583_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_601_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
v___y_547_ = v___y_584_;
v___y_548_ = v___y_585_;
v___y_549_ = v___y_586_;
v___y_550_ = v___y_587_;
v___y_551_ = v___y_588_;
v___y_552_ = v___y_589_;
v___y_553_ = v___y_590_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_600_;
v___y_557_ = v___y_593_;
v___y_558_ = v___y_594_;
v___y_559_ = v___y_595_;
v___y_560_ = v___y_596_;
v___y_561_ = v___y_597_;
v___y_562_ = v___y_598_;
v___y_563_ = v___y_599_;
v___y_564_ = v___x_607_;
goto v___jp_546_;
}
}
}
}
v___jp_610_:
{
if (lean_obj_tag(v___y_620_) == 0)
{
v___y_583_ = v___y_611_;
v___y_584_ = v___y_612_;
v___y_585_ = v___y_613_;
v___y_586_ = v___y_614_;
v___y_587_ = v___y_615_;
v___y_588_ = v___y_616_;
v___y_589_ = v___y_617_;
v___y_590_ = v___y_628_;
v___y_591_ = v___y_618_;
v___y_592_ = v___y_619_;
v___y_593_ = v___y_621_;
v___y_594_ = v___y_622_;
v___y_595_ = v___y_623_;
v___y_596_ = v___y_624_;
v___y_597_ = v___y_625_;
v___y_598_ = v___y_626_;
v___y_599_ = v___y_627_;
v___y_600_ = v___y_620_;
goto v___jp_582_;
}
else
{
lean_object* v_val_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_637_; 
v_val_629_ = lean_ctor_get(v___y_620_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___y_620_);
if (v_isSharedCheck_637_ == 0)
{
v___x_631_ = v___y_620_;
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_val_629_);
lean_dec(v___y_620_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_633_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
v___y_583_ = v___y_611_;
v___y_584_ = v___y_612_;
v___y_585_ = v___y_613_;
v___y_586_ = v___y_614_;
v___y_587_ = v___y_615_;
v___y_588_ = v___y_616_;
v___y_589_ = v___y_617_;
v___y_590_ = v___y_628_;
v___y_591_ = v___y_618_;
v___y_592_ = v___y_619_;
v___y_593_ = v___y_621_;
v___y_594_ = v___y_622_;
v___y_595_ = v___y_623_;
v___y_596_ = v___y_624_;
v___y_597_ = v___y_625_;
v___y_598_ = v___y_626_;
v___y_599_ = v___y_627_;
v___y_600_ = v___x_635_;
goto v___jp_582_;
}
}
}
}
v___jp_638_:
{
if (lean_obj_tag(v___y_654_) == 0)
{
v___y_611_ = v___y_639_;
v___y_612_ = v___y_640_;
v___y_613_ = v___y_641_;
v___y_614_ = v___y_642_;
v___y_615_ = v___y_643_;
v___y_616_ = v___y_644_;
v___y_617_ = v___y_645_;
v___y_618_ = v___y_646_;
v___y_619_ = v___y_647_;
v___y_620_ = v___y_648_;
v___y_621_ = v___y_649_;
v___y_622_ = v___y_650_;
v___y_623_ = v___y_656_;
v___y_624_ = v___y_651_;
v___y_625_ = v___y_652_;
v___y_626_ = v___y_653_;
v___y_627_ = v___y_655_;
v___y_628_ = v___y_654_;
goto v___jp_610_;
}
else
{
lean_object* v_val_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_672_; 
v_val_657_ = lean_ctor_get(v___y_654_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___y_654_);
if (v_isSharedCheck_672_ == 0)
{
v___x_659_ = v___y_654_;
v_isShared_660_ = v_isSharedCheck_672_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_val_657_);
lean_dec(v___y_654_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_672_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v_str_665_; lean_object* v_startInclusive_666_; lean_object* v_endExclusive_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = lean_string_utf8_byte_size(v_val_657_);
v___x_663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_663_, 0, v_val_657_);
lean_ctor_set(v___x_663_, 1, v___x_661_);
lean_ctor_set(v___x_663_, 2, v___x_662_);
v___x_664_ = l_String_Slice_trimAscii(v___x_663_);
v_str_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc_ref(v_str_665_);
v_startInclusive_666_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_startInclusive_666_);
v_endExclusive_667_ = lean_ctor_get(v___x_664_, 2);
lean_inc(v_endExclusive_667_);
lean_dec_ref(v___x_664_);
v___x_668_ = lean_string_utf8_extract(v_str_665_, v_startInclusive_666_, v_endExclusive_667_);
lean_dec(v_endExclusive_667_);
lean_dec(v_startInclusive_666_);
lean_dec_ref(v_str_665_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_668_);
v___x_670_ = v___x_659_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
v___y_611_ = v___y_639_;
v___y_612_ = v___y_640_;
v___y_613_ = v___y_641_;
v___y_614_ = v___y_642_;
v___y_615_ = v___y_643_;
v___y_616_ = v___y_644_;
v___y_617_ = v___y_645_;
v___y_618_ = v___y_646_;
v___y_619_ = v___y_647_;
v___y_620_ = v___y_648_;
v___y_621_ = v___y_649_;
v___y_622_ = v___y_650_;
v___y_623_ = v___y_656_;
v___y_624_ = v___y_651_;
v___y_625_ = v___y_652_;
v___y_626_ = v___y_653_;
v___y_627_ = v___y_655_;
v___y_628_ = v___x_670_;
goto v___jp_610_;
}
}
}
}
v___jp_673_:
{
lean_object* v___x_692_; 
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v_val_691_);
v___y_639_ = v___y_674_;
v___y_640_ = v___y_675_;
v___y_641_ = v___y_676_;
v___y_642_ = v___y_677_;
v___y_643_ = v___y_678_;
v___y_644_ = v___y_679_;
v___y_645_ = v___y_680_;
v___y_646_ = v___y_681_;
v___y_647_ = v___y_682_;
v___y_648_ = v___y_683_;
v___y_649_ = v___y_684_;
v___y_650_ = v___y_685_;
v___y_651_ = v___y_686_;
v___y_652_ = v___y_687_;
v___y_653_ = v___y_688_;
v___y_654_ = v___y_689_;
v___y_655_ = v___y_690_;
v___y_656_ = v___x_692_;
goto v___jp_638_;
}
v___jp_693_:
{
uint8_t v___x_710_; lean_object* v___x_711_; 
v___x_710_ = 0;
v___x_711_ = lean_box(0);
if (lean_obj_tag(v___y_696_) == 0)
{
if (lean_obj_tag(v___y_697_) == 0)
{
v___y_639_ = v___y_694_;
v___y_640_ = v___y_695_;
v___y_641_ = v___y_697_;
v___y_642_ = v___y_709_;
v___y_643_ = v___y_698_;
v___y_644_ = v___y_699_;
v___y_645_ = v___y_700_;
v___y_646_ = v___x_711_;
v___y_647_ = v___x_710_;
v___y_648_ = v___y_701_;
v___y_649_ = v___y_702_;
v___y_650_ = v___y_703_;
v___y_651_ = v___y_704_;
v___y_652_ = v___y_705_;
v___y_653_ = v___y_706_;
v___y_654_ = v___y_707_;
v___y_655_ = v___y_708_;
v___y_656_ = v___y_697_;
goto v___jp_638_;
}
else
{
lean_object* v_val_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_val_712_ = lean_ctor_get(v___y_697_, 0);
v___x_713_ = ((lean_object*)(l_Lake_Env_compute___closed__0));
lean_inc(v_val_712_);
v___x_714_ = l_System_FilePath_join(v_val_712_, v___x_713_);
v___x_715_ = ((lean_object*)(l_Lake_Env_compute___closed__1));
v___x_716_ = l_System_FilePath_join(v___x_714_, v___x_715_);
v___y_674_ = v___y_694_;
v___y_675_ = v___y_695_;
v___y_676_ = v___y_697_;
v___y_677_ = v___y_709_;
v___y_678_ = v___y_698_;
v___y_679_ = v___y_699_;
v___y_680_ = v___y_700_;
v___y_681_ = v___x_711_;
v___y_682_ = v___x_710_;
v___y_683_ = v___y_701_;
v___y_684_ = v___y_702_;
v___y_685_ = v___y_703_;
v___y_686_ = v___y_704_;
v___y_687_ = v___y_705_;
v___y_688_ = v___y_706_;
v___y_689_ = v___y_707_;
v___y_690_ = v___y_708_;
v_val_691_ = v___x_716_;
goto v___jp_673_;
}
}
else
{
lean_object* v_val_717_; 
v_val_717_ = lean_ctor_get(v___y_696_, 0);
lean_inc(v_val_717_);
lean_dec_ref(v___y_696_);
v___y_674_ = v___y_694_;
v___y_675_ = v___y_695_;
v___y_676_ = v___y_697_;
v___y_677_ = v___y_709_;
v___y_678_ = v___y_698_;
v___y_679_ = v___y_699_;
v___y_680_ = v___y_700_;
v___y_681_ = v___x_711_;
v___y_682_ = v___x_710_;
v___y_683_ = v___y_701_;
v___y_684_ = v___y_702_;
v___y_685_ = v___y_703_;
v___y_686_ = v___y_704_;
v___y_687_ = v___y_705_;
v___y_688_ = v___y_706_;
v___y_689_ = v___y_707_;
v___y_690_ = v___y_708_;
v_val_691_ = v_val_717_;
goto v___jp_673_;
}
}
v___jp_718_:
{
if (lean_obj_tag(v___y_726_) == 0)
{
lean_object* v___x_735_; 
v___x_735_ = lean_box(0);
v___y_694_ = v___y_719_;
v___y_695_ = v___y_720_;
v___y_696_ = v___y_721_;
v___y_697_ = v___y_722_;
v___y_698_ = v___y_723_;
v___y_699_ = v___y_724_;
v___y_700_ = v___y_725_;
v___y_701_ = v___y_727_;
v___y_702_ = v___y_728_;
v___y_703_ = v___y_729_;
v___y_704_ = v___y_730_;
v___y_705_ = v___y_734_;
v___y_706_ = v___y_731_;
v___y_707_ = v___y_732_;
v___y_708_ = v___y_733_;
v___y_709_ = v___x_735_;
goto v___jp_693_;
}
else
{
lean_object* v_val_736_; lean_object* v___x_737_; 
v_val_736_ = lean_ctor_get(v___y_726_, 0);
lean_inc(v_val_736_);
lean_dec_ref(v___y_726_);
v___x_737_ = l_Lake_envToBool_x3f(v_val_736_);
v___y_694_ = v___y_719_;
v___y_695_ = v___y_720_;
v___y_696_ = v___y_721_;
v___y_697_ = v___y_722_;
v___y_698_ = v___y_723_;
v___y_699_ = v___y_724_;
v___y_700_ = v___y_725_;
v___y_701_ = v___y_727_;
v___y_702_ = v___y_728_;
v___y_703_ = v___y_729_;
v___y_704_ = v___y_730_;
v___y_705_ = v___y_734_;
v___y_706_ = v___y_731_;
v___y_707_ = v___y_732_;
v___y_708_ = v___y_733_;
v___y_709_ = v___x_737_;
goto v___jp_693_;
}
}
v___jp_738_:
{
uint8_t v___x_754_; 
v___x_754_ = 0;
v___y_719_ = v___y_739_;
v___y_720_ = v___y_740_;
v___y_721_ = v___y_741_;
v___y_722_ = v___y_742_;
v___y_723_ = v___y_743_;
v___y_724_ = v___y_744_;
v___y_725_ = v___y_745_;
v___y_726_ = v___y_746_;
v___y_727_ = v___y_747_;
v___y_728_ = v___y_748_;
v___y_729_ = v___y_749_;
v___y_730_ = v___y_750_;
v___y_731_ = v___y_751_;
v___y_732_ = v___y_752_;
v___y_733_ = v___y_753_;
v___y_734_ = v___x_754_;
goto v___jp_718_;
}
v___jp_755_:
{
if (lean_obj_tag(v_noCache_523_) == 0)
{
if (lean_obj_tag(v___y_763_) == 0)
{
v___y_739_ = v___y_756_;
v___y_740_ = v___y_757_;
v___y_741_ = v___y_758_;
v___y_742_ = v___y_759_;
v___y_743_ = v___y_760_;
v___y_744_ = v___y_761_;
v___y_745_ = v___y_762_;
v___y_746_ = v___y_764_;
v___y_747_ = v___y_765_;
v___y_748_ = v___y_766_;
v___y_749_ = v___y_767_;
v___y_750_ = v___y_771_;
v___y_751_ = v___y_768_;
v___y_752_ = v___y_769_;
v___y_753_ = v___y_770_;
goto v___jp_738_;
}
else
{
lean_object* v_val_772_; lean_object* v___x_773_; 
v_val_772_ = lean_ctor_get(v___y_763_, 0);
lean_inc(v_val_772_);
lean_dec_ref(v___y_763_);
v___x_773_ = l_Lake_envToBool_x3f(v_val_772_);
if (lean_obj_tag(v___x_773_) == 0)
{
v___y_739_ = v___y_756_;
v___y_740_ = v___y_757_;
v___y_741_ = v___y_758_;
v___y_742_ = v___y_759_;
v___y_743_ = v___y_760_;
v___y_744_ = v___y_761_;
v___y_745_ = v___y_762_;
v___y_746_ = v___y_764_;
v___y_747_ = v___y_765_;
v___y_748_ = v___y_766_;
v___y_749_ = v___y_767_;
v___y_750_ = v___y_771_;
v___y_751_ = v___y_768_;
v___y_752_ = v___y_769_;
v___y_753_ = v___y_770_;
goto v___jp_738_;
}
else
{
lean_object* v_val_774_; uint8_t v___x_775_; 
v_val_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_val_774_);
lean_dec_ref(v___x_773_);
v___x_775_ = lean_unbox(v_val_774_);
lean_dec(v_val_774_);
v___y_719_ = v___y_756_;
v___y_720_ = v___y_757_;
v___y_721_ = v___y_758_;
v___y_722_ = v___y_759_;
v___y_723_ = v___y_760_;
v___y_724_ = v___y_761_;
v___y_725_ = v___y_762_;
v___y_726_ = v___y_764_;
v___y_727_ = v___y_765_;
v___y_728_ = v___y_766_;
v___y_729_ = v___y_767_;
v___y_730_ = v___y_771_;
v___y_731_ = v___y_768_;
v___y_732_ = v___y_769_;
v___y_733_ = v___y_770_;
v___y_734_ = v___x_775_;
goto v___jp_718_;
}
}
}
else
{
lean_object* v_val_776_; uint8_t v___x_777_; 
lean_dec(v___y_763_);
v_val_776_ = lean_ctor_get(v_noCache_523_, 0);
v___x_777_ = lean_unbox(v_val_776_);
v___y_719_ = v___y_756_;
v___y_720_ = v___y_757_;
v___y_721_ = v___y_758_;
v___y_722_ = v___y_759_;
v___y_723_ = v___y_760_;
v___y_724_ = v___y_761_;
v___y_725_ = v___y_762_;
v___y_726_ = v___y_764_;
v___y_727_ = v___y_765_;
v___y_728_ = v___y_766_;
v___y_729_ = v___y_767_;
v___y_730_ = v___y_771_;
v___y_731_ = v___y_768_;
v___y_732_ = v___y_769_;
v___y_733_ = v___y_770_;
v___y_734_ = v___x_777_;
goto v___jp_718_;
}
}
v___jp_778_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_783_ = ((lean_object*)(l_Lake_Env_compute___closed__2));
v___x_784_ = lean_io_getenv(v___x_783_);
v___x_785_ = ((lean_object*)(l_Lake_Env_compute___closed__3));
v___x_786_ = lean_io_getenv(v___x_785_);
v___x_787_ = ((lean_object*)(l_Lake_Env_compute___closed__4));
v___x_788_ = lean_io_getenv(v___x_787_);
v___x_789_ = ((lean_object*)(l_Lake_Env_compute___closed__5));
v___x_790_ = lean_io_getenv(v___x_789_);
v___x_791_ = ((lean_object*)(l_Lake_Env_compute___closed__6));
v___x_792_ = lean_io_getenv(v___x_791_);
v___x_793_ = ((lean_object*)(l_Lake_Env_compute___closed__7));
v___x_794_ = lean_io_getenv(v___x_793_);
v___x_795_ = ((lean_object*)(l_Lake_Env_compute___closed__8));
v___x_796_ = lean_io_getenv(v___x_795_);
v___x_797_ = ((lean_object*)(l_Lake_Env_compute___closed__9));
v___x_798_ = lean_io_getenv(v___x_797_);
v___x_799_ = ((lean_object*)(l_Lake_Env_compute___closed__10));
v___x_800_ = l_Lake_getSearchPath(v___x_799_);
v___x_801_ = ((lean_object*)(l_Lake_Env_compute___closed__11));
v___x_802_ = l_Lake_getSearchPath(v___x_801_);
v___x_803_ = l_Lake_sharedLibPathEnvVar;
v___x_804_ = l_Lake_getSearchPath(v___x_803_);
v___x_805_ = ((lean_object*)(l_Lake_Env_compute___closed__12));
v___x_806_ = l_Lake_getSearchPath(v___x_805_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_807_; 
v___x_807_ = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
v___y_756_ = v___x_794_;
v___y_757_ = v___x_800_;
v___y_758_ = v___x_788_;
v___y_759_ = v___y_780_;
v___y_760_ = v___x_804_;
v___y_761_ = v___y_781_;
v___y_762_ = v___x_802_;
v___y_763_ = v___x_784_;
v___y_764_ = v___x_786_;
v___y_765_ = v___x_792_;
v___y_766_ = v___x_806_;
v___y_767_ = v___y_779_;
v___y_768_ = v___x_796_;
v___y_769_ = v___x_790_;
v___y_770_ = v_a_782_;
v___y_771_ = v___x_807_;
goto v___jp_755_;
}
else
{
lean_object* v_val_808_; 
v_val_808_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_val_808_);
lean_dec_ref(v___x_798_);
v___y_756_ = v___x_794_;
v___y_757_ = v___x_800_;
v___y_758_ = v___x_788_;
v___y_759_ = v___y_780_;
v___y_760_ = v___x_804_;
v___y_761_ = v___y_781_;
v___y_762_ = v___x_802_;
v___y_763_ = v___x_784_;
v___y_764_ = v___x_786_;
v___y_765_ = v___x_792_;
v___y_766_ = v___x_806_;
v___y_767_ = v___y_779_;
v___y_768_ = v___x_796_;
v___y_769_ = v___x_790_;
v___y_770_ = v_a_782_;
v___y_771_ = v_val_808_;
goto v___jp_755_;
}
}
v___jp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = l_Lake_Env_computeToolchain();
v___x_814_ = l_Lake_getUserHome_x3f();
v___x_815_ = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref(v___x_815_);
v___x_817_ = ((lean_object*)(l_Lake_Env_compute___closed__14));
v___x_818_ = lean_io_getenv(v___x_817_);
if (lean_obj_tag(v___x_818_) == 1)
{
lean_object* v_val_819_; lean_object* v___x_820_; 
lean_dec_ref(v_a_812_);
v_val_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_val_819_);
lean_dec_ref(v___x_818_);
v___x_820_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_819_);
v___y_779_ = v_a_816_;
v___y_780_ = v___x_814_;
v___y_781_ = v___x_813_;
v_a_782_ = v___x_820_;
goto v___jp_778_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v___x_818_);
v___x_821_ = ((lean_object*)(l_Lake_Env_compute___closed__15));
v___x_822_ = lean_string_append(v_a_812_, v___x_821_);
v___y_779_ = v_a_816_;
v___y_780_ = v___x_814_;
v___y_781_ = v___x_813_;
v_a_782_ = v___x_822_;
goto v___jp_778_;
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v___x_814_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_elan_x3f_522_);
lean_dec_ref(v_lean_521_);
lean_dec_ref(v_lake_520_);
v_a_823_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_815_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_815_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object* v_lake_834_, lean_object* v_lean_835_, lean_object* v_elan_x3f_836_, lean_object* v_noCache_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lake_Env_compute(v_lake_834_, v_lean_835_, v_elan_x3f_836_, v_noCache_837_);
lean_dec(v_noCache_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain(lean_object* v_env_840_){
_start:
{
lean_object* v_toolchain_841_; 
v_toolchain_841_ = lean_ctor_get(v_env_840_, 18);
lean_inc_ref(v_toolchain_841_);
return v_toolchain_841_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain___boxed(lean_object* v_env_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lake_Env_cacheToolchain(v_env_842_);
lean_dec_ref(v_env_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object* v_env_844_){
_start:
{
lean_object* v_lean_845_; lean_object* v_githashOverride_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_lean_845_ = lean_ctor_get(v_env_844_, 1);
v_githashOverride_846_ = lean_ctor_get(v_env_844_, 4);
v___x_847_ = lean_string_utf8_byte_size(v_githashOverride_846_);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_nat_dec_eq(v___x_847_, v___x_848_);
if (v___x_849_ == 0)
{
lean_inc_ref(v_githashOverride_846_);
return v_githashOverride_846_;
}
else
{
lean_object* v_githash_850_; 
v_githash_850_ = lean_ctor_get(v_lean_845_, 1);
lean_inc_ref(v_githash_850_);
return v_githash_850_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object* v_env_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lake_Env_leanGithash(v_env_851_);
lean_dec_ref(v_env_851_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object* v_env_853_){
_start:
{
lean_object* v_lake_854_; lean_object* v_lean_855_; lean_object* v_initPath_856_; lean_object* v_binDir_857_; lean_object* v_binDir_858_; uint8_t v___x_859_; 
v_lake_854_ = lean_ctor_get(v_env_853_, 0);
v_lean_855_ = lean_ctor_get(v_env_853_, 1);
v_initPath_856_ = lean_ctor_get(v_env_853_, 17);
v_binDir_857_ = lean_ctor_get(v_lake_854_, 2);
v_binDir_858_ = lean_ctor_get(v_lean_855_, 6);
v___x_859_ = lean_string_dec_eq(v_binDir_857_, v_binDir_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_inc(v_initPath_856_);
lean_inc_ref(v_binDir_858_);
v___x_860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_860_, 0, v_binDir_858_);
lean_ctor_set(v___x_860_, 1, v_initPath_856_);
lean_inc_ref(v_binDir_857_);
v___x_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_861_, 0, v_binDir_857_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; 
lean_inc(v_initPath_856_);
lean_inc_ref(v_binDir_858_);
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v_binDir_858_);
lean_ctor_set(v___x_862_, 1, v_initPath_856_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object* v_env_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lake_Env_path(v_env_863_);
lean_dec_ref(v_env_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object* v_env_865_){
_start:
{
lean_object* v_lake_866_; lean_object* v_initLeanPath_867_; lean_object* v_libDir_868_; lean_object* v___x_869_; 
v_lake_866_ = lean_ctor_get(v_env_865_, 0);
v_initLeanPath_867_ = lean_ctor_get(v_env_865_, 14);
v_libDir_868_ = lean_ctor_get(v_lake_866_, 3);
lean_inc(v_initLeanPath_867_);
lean_inc_ref(v_libDir_868_);
v___x_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_869_, 0, v_libDir_868_);
lean_ctor_set(v___x_869_, 1, v_initLeanPath_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object* v_env_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lake_Env_leanPath(v_env_870_);
lean_dec_ref(v_env_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object* v_env_872_){
_start:
{
lean_object* v_lake_873_; lean_object* v_initLeanSrcPath_874_; lean_object* v_srcDir_875_; lean_object* v___x_876_; 
v_lake_873_ = lean_ctor_get(v_env_872_, 0);
v_initLeanSrcPath_874_ = lean_ctor_get(v_env_872_, 15);
v_srcDir_875_ = lean_ctor_get(v_lake_873_, 1);
lean_inc(v_initLeanSrcPath_874_);
lean_inc_ref(v_srcDir_875_);
v___x_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_876_, 0, v_srcDir_875_);
lean_ctor_set(v___x_876_, 1, v_initLeanSrcPath_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object* v_env_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lake_Env_leanSrcPath(v_env_877_);
lean_dec_ref(v_env_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object* v_env_879_){
_start:
{
lean_object* v_lean_880_; lean_object* v_initSharedLibPath_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_lean_880_ = lean_ctor_get(v_env_879_, 1);
lean_inc_ref(v_lean_880_);
v_initSharedLibPath_881_ = lean_ctor_get(v_env_879_, 16);
lean_inc(v_initSharedLibPath_881_);
lean_dec_ref(v_env_879_);
v___x_882_ = l_Lake_LeanInstall_sharedLibPath(v_lean_880_);
lean_dec_ref(v_lean_880_);
v___x_883_ = l_List_appendTR___redArg(v___x_882_, v_initSharedLibPath_881_);
return v___x_883_;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__14(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_914_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__0));
v___x_915_ = lean_unsigned_to_nat(9u);
v___x_916_ = lean_mk_empty_array_with_capacity(v___x_915_);
v___x_917_ = lean_array_push(v___x_916_, v___x_914_);
return v___x_917_;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__15(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__2));
v___x_919_ = lean_obj_once(&l_Lake_Env_noToolchainVars___closed__14, &l_Lake_Env_noToolchainVars___closed__14_once, _init_l_Lake_Env_noToolchainVars___closed__14);
v___x_920_ = lean_array_push(v___x_919_, v___x_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars(lean_object* v_env_923_){
_start:
{
uint8_t v_noSystemCache_924_; lean_object* v_lakeSystemCache_x3f_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___y_929_; 
v_noSystemCache_924_ = lean_ctor_get_uint8(v_env_923_, sizeof(void*)*19 + 1);
v_lakeSystemCache_x3f_925_ = lean_ctor_get(v_env_923_, 8);
lean_inc(v_lakeSystemCache_x3f_925_);
lean_dec_ref(v_env_923_);
v___x_926_ = lean_box(0);
v___x_927_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
if (v_noSystemCache_924_ == 0)
{
if (lean_obj_tag(v_lakeSystemCache_x3f_925_) == 0)
{
v___y_929_ = v___x_926_;
goto v___jp_928_;
}
else
{
lean_object* v_val_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v_val_945_ = lean_ctor_get(v_lakeSystemCache_x3f_925_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v_lakeSystemCache_x3f_925_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v_lakeSystemCache_x3f_925_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_val_945_);
lean_dec(v_lakeSystemCache_x3f_925_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_val_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
v___y_929_ = v___x_950_;
goto v___jp_928_;
}
}
}
}
else
{
lean_object* v___x_953_; 
lean_dec(v_lakeSystemCache_x3f_925_);
v___x_953_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_929_ = v___x_953_;
goto v___jp_928_;
}
v___jp_928_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_927_);
lean_ctor_set(v___x_930_, 1, v___y_929_);
v___x_931_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__4));
v___x_932_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__6));
v___x_933_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__8));
v___x_934_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__9));
v___x_935_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__11));
v___x_936_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__13));
v___x_937_ = lean_obj_once(&l_Lake_Env_noToolchainVars___closed__15, &l_Lake_Env_noToolchainVars___closed__15_once, _init_l_Lake_Env_noToolchainVars___closed__15);
v___x_938_ = lean_array_push(v___x_937_, v___x_930_);
v___x_939_ = lean_array_push(v___x_938_, v___x_931_);
v___x_940_ = lean_array_push(v___x_939_, v___x_932_);
v___x_941_ = lean_array_push(v___x_940_, v___x_933_);
v___x_942_ = lean_array_push(v___x_941_, v___x_934_);
v___x_943_ = lean_array_push(v___x_942_, v___x_935_);
v___x_944_ = lean_array_push(v___x_943_, v___x_936_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_box(1);
v___x_956_ = lean_panic_fn_borrowed(v___x_955_, v_msg_954_);
return v___x_956_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_960_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2));
v___x_961_ = lean_unsigned_to_nat(35u);
v___x_962_ = lean_unsigned_to_nat(276u);
v___x_963_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1));
v___x_964_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_965_ = l_mkPanicMessageWithDecl(v___x_964_, v___x_963_, v___x_962_, v___x_961_, v___x_960_);
return v___x_965_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_966_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2));
v___x_967_ = lean_unsigned_to_nat(21u);
v___x_968_ = lean_unsigned_to_nat(277u);
v___x_969_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1));
v___x_970_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_971_ = l_mkPanicMessageWithDecl(v___x_970_, v___x_969_, v___x_968_, v___x_967_, v___x_966_);
return v___x_971_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_974_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6));
v___x_975_ = lean_unsigned_to_nat(35u);
v___x_976_ = lean_unsigned_to_nat(182u);
v___x_977_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5));
v___x_978_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_979_ = l_mkPanicMessageWithDecl(v___x_978_, v___x_977_, v___x_976_, v___x_975_, v___x_974_);
return v___x_979_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_980_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6));
v___x_981_ = lean_unsigned_to_nat(21u);
v___x_982_ = lean_unsigned_to_nat(183u);
v___x_983_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5));
v___x_984_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_985_ = l_mkPanicMessageWithDecl(v___x_984_, v___x_983_, v___x_982_, v___x_981_, v___x_980_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(lean_object* v_k_986_, lean_object* v_v_987_, lean_object* v_t_988_){
_start:
{
if (lean_obj_tag(v_t_988_) == 0)
{
lean_object* v_size_989_; lean_object* v_k_990_; lean_object* v_v_991_; lean_object* v_l_992_; lean_object* v_r_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1350_; 
v_size_989_ = lean_ctor_get(v_t_988_, 0);
v_k_990_ = lean_ctor_get(v_t_988_, 1);
v_v_991_ = lean_ctor_get(v_t_988_, 2);
v_l_992_ = lean_ctor_get(v_t_988_, 3);
v_r_993_ = lean_ctor_get(v_t_988_, 4);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_t_988_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_995_ = v_t_988_;
v_isShared_996_ = v_isSharedCheck_1350_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_r_993_);
lean_inc(v_l_992_);
lean_inc(v_v_991_);
lean_inc(v_k_990_);
lean_inc(v_size_989_);
lean_dec(v_t_988_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1350_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
uint8_t v___x_997_; 
v___x_997_ = lean_string_dec_lt(v_k_986_, v_k_990_);
if (v___x_997_ == 0)
{
uint8_t v___x_998_; 
v___x_998_ = lean_string_dec_eq(v_k_986_, v_k_990_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; 
lean_dec(v_size_989_);
v___x_999_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_986_, v_v_987_, v_r_993_);
if (lean_obj_tag(v_l_992_) == 0)
{
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_size_1000_; lean_object* v_size_1001_; lean_object* v_k_1002_; lean_object* v_v_1003_; lean_object* v_l_1004_; lean_object* v_r_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_size_1000_ = lean_ctor_get(v_l_992_, 0);
v_size_1001_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_size_1001_);
v_k_1002_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_k_1002_);
v_v_1003_ = lean_ctor_get(v___x_999_, 2);
lean_inc(v_v_1003_);
v_l_1004_ = lean_ctor_get(v___x_999_, 3);
lean_inc(v_l_1004_);
v_r_1005_ = lean_ctor_get(v___x_999_, 4);
lean_inc(v_r_1005_);
v___x_1006_ = lean_unsigned_to_nat(3u);
v___x_1007_ = lean_nat_mul(v___x_1006_, v_size_1000_);
v___x_1008_ = lean_nat_dec_lt(v___x_1007_, v_size_1001_);
lean_dec(v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
lean_dec(v_r_1005_);
lean_dec(v_l_1004_);
lean_dec(v_v_1003_);
lean_dec(v_k_1002_);
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_nat_add(v___x_1009_, v_size_1000_);
v___x_1011_ = lean_nat_add(v___x_1010_, v_size_1001_);
lean_dec(v_size_1001_);
lean_dec(v___x_1010_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___x_999_);
lean_ctor_set(v___x_995_, 0, v___x_1011_);
v___x_1013_ = v___x_995_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1014_, 3, v_l_992_);
lean_ctor_set(v_reuseFailAlloc_1014_, 4, v___x_999_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
else
{
lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1084_; 
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; lean_object* v_unused_1086_; lean_object* v_unused_1087_; lean_object* v_unused_1088_; lean_object* v_unused_1089_; 
v_unused_1085_ = lean_ctor_get(v___x_999_, 4);
lean_dec(v_unused_1085_);
v_unused_1086_ = lean_ctor_get(v___x_999_, 3);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v___x_999_, 2);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v___x_999_, 1);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v___x_999_, 0);
lean_dec(v_unused_1089_);
v___x_1016_ = v___x_999_;
v_isShared_1017_ = v_isSharedCheck_1084_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v___x_999_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1084_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
if (lean_obj_tag(v_l_1004_) == 0)
{
if (lean_obj_tag(v_r_1005_) == 0)
{
lean_object* v_size_1018_; lean_object* v_k_1019_; lean_object* v_v_1020_; lean_object* v_l_1021_; lean_object* v_r_1022_; lean_object* v_size_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_size_1018_ = lean_ctor_get(v_l_1004_, 0);
v_k_1019_ = lean_ctor_get(v_l_1004_, 1);
v_v_1020_ = lean_ctor_get(v_l_1004_, 2);
v_l_1021_ = lean_ctor_get(v_l_1004_, 3);
v_r_1022_ = lean_ctor_get(v_l_1004_, 4);
v_size_1023_ = lean_ctor_get(v_r_1005_, 0);
v___x_1024_ = lean_unsigned_to_nat(2u);
v___x_1025_ = lean_nat_mul(v___x_1024_, v_size_1023_);
v___x_1026_ = lean_nat_dec_lt(v_size_1018_, v___x_1025_);
lean_dec(v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1055_; 
lean_inc(v_r_1022_);
lean_inc(v_l_1021_);
lean_inc(v_v_1020_);
lean_inc(v_k_1019_);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_l_1004_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; lean_object* v_unused_1057_; lean_object* v_unused_1058_; lean_object* v_unused_1059_; lean_object* v_unused_1060_; 
v_unused_1056_ = lean_ctor_get(v_l_1004_, 4);
lean_dec(v_unused_1056_);
v_unused_1057_ = lean_ctor_get(v_l_1004_, 3);
lean_dec(v_unused_1057_);
v_unused_1058_ = lean_ctor_get(v_l_1004_, 2);
lean_dec(v_unused_1058_);
v_unused_1059_ = lean_ctor_get(v_l_1004_, 1);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_l_1004_, 0);
lean_dec(v_unused_1060_);
v___x_1028_ = v_l_1004_;
v_isShared_1029_ = v_isSharedCheck_1055_;
goto v_resetjp_1027_;
}
else
{
lean_dec(v_l_1004_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1055_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1045_; 
v___x_1030_ = lean_unsigned_to_nat(1u);
v___x_1031_ = lean_nat_add(v___x_1030_, v_size_1000_);
v___x_1032_ = lean_nat_add(v___x_1031_, v_size_1001_);
lean_dec(v_size_1001_);
if (lean_obj_tag(v_l_1021_) == 0)
{
lean_object* v_size_1053_; 
v_size_1053_ = lean_ctor_get(v_l_1021_, 0);
lean_inc(v_size_1053_);
v___y_1045_ = v_size_1053_;
goto v___jp_1044_;
}
else
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_unsigned_to_nat(0u);
v___y_1045_ = v___x_1054_;
goto v___jp_1044_;
}
v___jp_1033_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_nat_add(v___y_1034_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec(v___y_1034_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 4, v_r_1005_);
lean_ctor_set(v___x_1028_, 3, v_r_1022_);
lean_ctor_set(v___x_1028_, 2, v_v_1003_);
lean_ctor_set(v___x_1028_, 1, v_k_1002_);
lean_ctor_set(v___x_1028_, 0, v___x_1037_);
v___x_1039_ = v___x_1028_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_k_1002_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_v_1003_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_r_1022_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_r_1005_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 4, v___x_1039_);
lean_ctor_set(v___x_1016_, 3, v___y_1035_);
lean_ctor_set(v___x_1016_, 2, v_v_1020_);
lean_ctor_set(v___x_1016_, 1, v_k_1019_);
lean_ctor_set(v___x_1016_, 0, v___x_1032_);
v___x_1041_ = v___x_1016_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_k_1019_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_v_1020_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v___y_1035_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
v___jp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = lean_nat_add(v___x_1031_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec(v___x_1031_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v_l_1021_);
lean_ctor_set(v___x_995_, 0, v___x_1046_);
v___x_1048_ = v___x_995_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v_l_992_);
lean_ctor_set(v_reuseFailAlloc_1052_, 4, v_l_1021_);
v___x_1048_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_nat_add(v___x_1030_, v_size_1023_);
if (lean_obj_tag(v_r_1022_) == 0)
{
lean_object* v_size_1050_; 
v_size_1050_ = lean_ctor_get(v_r_1022_, 0);
lean_inc(v_size_1050_);
v___y_1034_ = v___x_1049_;
v___y_1035_ = v___x_1048_;
v___y_1036_ = v_size_1050_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_unsigned_to_nat(0u);
v___y_1034_ = v___x_1049_;
v___y_1035_ = v___x_1048_;
v___y_1036_ = v___x_1051_;
goto v___jp_1033_;
}
}
}
}
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
lean_del_object(v___x_995_);
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_add(v___x_1061_, v_size_1000_);
v___x_1063_ = lean_nat_add(v___x_1062_, v_size_1001_);
lean_dec(v_size_1001_);
v___x_1064_ = lean_nat_add(v___x_1062_, v_size_1018_);
lean_dec(v___x_1062_);
lean_inc_ref(v_l_992_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 4, v_l_1004_);
lean_ctor_set(v___x_1016_, 3, v_l_992_);
lean_ctor_set(v___x_1016_, 2, v_v_991_);
lean_ctor_set(v___x_1016_, 1, v_k_990_);
lean_ctor_set(v___x_1016_, 0, v___x_1064_);
v___x_1066_ = v___x_1016_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_l_992_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_l_1004_);
v___x_1066_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
v_isSharedCheck_1073_ = !lean_is_exclusive(v_l_992_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; lean_object* v_unused_1077_; lean_object* v_unused_1078_; 
v_unused_1074_ = lean_ctor_get(v_l_992_, 4);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_l_992_, 3);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_l_992_, 2);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_l_992_, 1);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_l_992_, 0);
lean_dec(v_unused_1078_);
v___x_1068_ = v_l_992_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_dec(v_l_992_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 4, v_r_1005_);
lean_ctor_set(v___x_1068_, 3, v___x_1066_);
lean_ctor_set(v___x_1068_, 2, v_v_1003_);
lean_ctor_set(v___x_1068_, 1, v_k_1002_);
lean_ctor_set(v___x_1068_, 0, v___x_1063_);
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_k_1002_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_v_1003_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v_r_1005_);
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
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v_l_1004_);
lean_del_object(v___x_1016_);
lean_dec(v_v_1003_);
lean_dec(v_k_1002_);
lean_dec(v_size_1001_);
lean_dec_ref(v_l_992_);
lean_del_object(v___x_995_);
lean_dec(v_v_991_);
lean_dec(v_k_990_);
v___x_1080_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3);
v___x_1081_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1080_);
return v___x_1081_;
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_del_object(v___x_1016_);
lean_dec(v_r_1005_);
lean_dec(v_v_1003_);
lean_dec(v_k_1002_);
lean_dec(v_size_1001_);
lean_dec_ref(v_l_992_);
lean_del_object(v___x_995_);
lean_dec(v_v_991_);
lean_dec(v_k_990_);
v___x_1082_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4);
v___x_1083_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1082_);
return v___x_1083_;
}
}
}
}
else
{
lean_object* v_size_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v_size_1090_ = lean_ctor_get(v_l_992_, 0);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_nat_add(v___x_1091_, v_size_1090_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___x_999_);
lean_ctor_set(v___x_995_, 0, v___x_1092_);
v___x_1094_ = v___x_995_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_l_992_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v___x_999_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_l_1096_; 
v_l_1096_ = lean_ctor_get(v___x_999_, 3);
lean_inc(v_l_1096_);
if (lean_obj_tag(v_l_1096_) == 0)
{
lean_object* v_r_1097_; 
v_r_1097_ = lean_ctor_get(v___x_999_, 4);
lean_inc(v_r_1097_);
if (lean_obj_tag(v_r_1097_) == 0)
{
lean_object* v_size_1098_; lean_object* v_k_1099_; lean_object* v_v_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1114_; 
v_size_1098_ = lean_ctor_get(v___x_999_, 0);
v_k_1099_ = lean_ctor_get(v___x_999_, 1);
v_v_1100_ = lean_ctor_get(v___x_999_, 2);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; lean_object* v_unused_1116_; 
v_unused_1115_ = lean_ctor_get(v___x_999_, 4);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v___x_999_, 3);
lean_dec(v_unused_1116_);
v___x_1102_ = v___x_999_;
v_isShared_1103_ = v_isSharedCheck_1114_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_v_1100_);
lean_inc(v_k_1099_);
lean_inc(v_size_1098_);
lean_dec(v___x_999_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1114_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_size_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v_size_1104_ = lean_ctor_get(v_l_1096_, 0);
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_nat_add(v___x_1105_, v_size_1098_);
lean_dec(v_size_1098_);
v___x_1107_ = lean_nat_add(v___x_1105_, v_size_1104_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v_l_1096_);
lean_ctor_set(v___x_1102_, 3, v_l_992_);
lean_ctor_set(v___x_1102_, 2, v_v_991_);
lean_ctor_set(v___x_1102_, 1, v_k_990_);
lean_ctor_set(v___x_1102_, 0, v___x_1107_);
v___x_1109_ = v___x_1102_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_l_992_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_l_1096_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v_r_1097_);
lean_ctor_set(v___x_995_, 3, v___x_1109_);
lean_ctor_set(v___x_995_, 2, v_v_1100_);
lean_ctor_set(v___x_995_, 1, v_k_1099_);
lean_ctor_set(v___x_995_, 0, v___x_1106_);
v___x_1111_ = v___x_995_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_k_1099_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_v_1100_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_r_1097_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v_k_1117_; lean_object* v_v_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1142_; 
v_k_1117_ = lean_ctor_get(v___x_999_, 1);
v_v_1118_ = lean_ctor_get(v___x_999_, 2);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1143_ = lean_ctor_get(v___x_999_, 4);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v___x_999_, 3);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v___x_999_, 0);
lean_dec(v_unused_1145_);
v___x_1120_ = v___x_999_;
v_isShared_1121_ = v_isSharedCheck_1142_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_v_1118_);
lean_inc(v_k_1117_);
lean_dec(v___x_999_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1142_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_k_1122_; lean_object* v_v_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1138_; 
v_k_1122_ = lean_ctor_get(v_l_1096_, 1);
v_v_1123_ = lean_ctor_get(v_l_1096_, 2);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_l_1096_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; lean_object* v_unused_1140_; lean_object* v_unused_1141_; 
v_unused_1139_ = lean_ctor_get(v_l_1096_, 4);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_l_1096_, 3);
lean_dec(v_unused_1140_);
v_unused_1141_ = lean_ctor_get(v_l_1096_, 0);
lean_dec(v_unused_1141_);
v___x_1125_ = v_l_1096_;
v_isShared_1126_ = v_isSharedCheck_1138_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_v_1123_);
lean_inc(v_k_1122_);
lean_dec(v_l_1096_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1138_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1127_ = lean_unsigned_to_nat(3u);
v___x_1128_ = lean_unsigned_to_nat(1u);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 4, v_r_1097_);
lean_ctor_set(v___x_1125_, 3, v_r_1097_);
lean_ctor_set(v___x_1125_, 2, v_v_991_);
lean_ctor_set(v___x_1125_, 1, v_k_990_);
lean_ctor_set(v___x_1125_, 0, v___x_1128_);
v___x_1130_ = v___x_1125_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v_r_1097_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_r_1097_);
v___x_1130_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 3, v_r_1097_);
lean_ctor_set(v___x_1120_, 0, v___x_1128_);
v___x_1132_ = v___x_1120_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_k_1117_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_v_1118_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_r_1097_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_r_1097_);
v___x_1132_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___x_1132_);
lean_ctor_set(v___x_995_, 3, v___x_1130_);
lean_ctor_set(v___x_995_, 2, v_v_1123_);
lean_ctor_set(v___x_995_, 1, v_k_1122_);
lean_ctor_set(v___x_995_, 0, v___x_1127_);
v___x_1134_ = v___x_995_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_k_1122_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_v_1123_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1146_; 
v_r_1146_ = lean_ctor_get(v___x_999_, 4);
lean_inc(v_r_1146_);
if (lean_obj_tag(v_r_1146_) == 0)
{
lean_object* v_k_1147_; lean_object* v_v_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1160_; 
v_k_1147_ = lean_ctor_get(v___x_999_, 1);
v_v_1148_ = lean_ctor_get(v___x_999_, 2);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; lean_object* v_unused_1162_; lean_object* v_unused_1163_; 
v_unused_1161_ = lean_ctor_get(v___x_999_, 4);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v___x_999_, 3);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v___x_999_, 0);
lean_dec(v_unused_1163_);
v___x_1150_ = v___x_999_;
v_isShared_1151_ = v_isSharedCheck_1160_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_v_1148_);
lean_inc(v_k_1147_);
lean_dec(v___x_999_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1160_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1152_ = lean_unsigned_to_nat(3u);
v___x_1153_ = lean_unsigned_to_nat(1u);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 4, v_l_1096_);
lean_ctor_set(v___x_1150_, 2, v_v_991_);
lean_ctor_set(v___x_1150_, 1, v_k_990_);
lean_ctor_set(v___x_1150_, 0, v___x_1153_);
v___x_1155_ = v___x_1150_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_l_1096_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_l_1096_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v_r_1146_);
lean_ctor_set(v___x_995_, 3, v___x_1155_);
lean_ctor_set(v___x_995_, 2, v_v_1148_);
lean_ctor_set(v___x_995_, 1, v_k_1147_);
lean_ctor_set(v___x_995_, 0, v___x_1152_);
v___x_1157_ = v___x_995_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_k_1147_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_v_1148_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_r_1146_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = lean_unsigned_to_nat(2u);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___x_999_);
lean_ctor_set(v___x_995_, 3, v_r_1146_);
lean_ctor_set(v___x_995_, 0, v___x_1164_);
v___x_1166_ = v___x_995_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_r_1146_);
lean_ctor_set(v_reuseFailAlloc_1167_, 4, v___x_999_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = lean_unsigned_to_nat(1u);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___x_999_);
lean_ctor_set(v___x_995_, 3, v___x_999_);
lean_ctor_set(v___x_995_, 0, v___x_1168_);
v___x_1170_ = v___x_995_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1171_, 4, v___x_999_);
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
else
{
lean_object* v___x_1173_; 
lean_dec(v_v_991_);
lean_dec(v_k_990_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 2, v_v_987_);
lean_ctor_set(v___x_995_, 1, v_k_986_);
v___x_1173_ = v___x_995_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_size_989_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_k_986_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_v_987_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_l_992_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v_r_993_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
else
{
lean_object* v___x_1175_; 
lean_dec(v_size_989_);
v___x_1175_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_986_, v_v_987_, v_l_992_);
if (lean_obj_tag(v_r_993_) == 0)
{
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_size_1176_; lean_object* v_size_1177_; lean_object* v_k_1178_; lean_object* v_v_1179_; lean_object* v_l_1180_; lean_object* v_r_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_size_1176_ = lean_ctor_get(v_r_993_, 0);
v_size_1177_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_size_1177_);
v_k_1178_ = lean_ctor_get(v___x_1175_, 1);
lean_inc(v_k_1178_);
v_v_1179_ = lean_ctor_get(v___x_1175_, 2);
lean_inc(v_v_1179_);
v_l_1180_ = lean_ctor_get(v___x_1175_, 3);
lean_inc(v_l_1180_);
v_r_1181_ = lean_ctor_get(v___x_1175_, 4);
lean_inc(v_r_1181_);
v___x_1182_ = lean_unsigned_to_nat(3u);
v___x_1183_ = lean_nat_mul(v___x_1182_, v_size_1176_);
v___x_1184_ = lean_nat_dec_lt(v___x_1183_, v_size_1177_);
lean_dec(v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
lean_dec(v_r_1181_);
lean_dec(v_l_1180_);
lean_dec(v_v_1179_);
lean_dec(v_k_1178_);
v___x_1185_ = lean_unsigned_to_nat(1u);
v___x_1186_ = lean_nat_add(v___x_1185_, v_size_1177_);
lean_dec(v_size_1177_);
v___x_1187_ = lean_nat_add(v___x_1186_, v_size_1176_);
lean_dec(v___x_1186_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 3, v___x_1175_);
lean_ctor_set(v___x_995_, 0, v___x_1187_);
v___x_1189_ = v___x_995_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1190_, 4, v_r_993_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
else
{
lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1262_; 
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; lean_object* v_unused_1264_; lean_object* v_unused_1265_; lean_object* v_unused_1266_; lean_object* v_unused_1267_; 
v_unused_1263_ = lean_ctor_get(v___x_1175_, 4);
lean_dec(v_unused_1263_);
v_unused_1264_ = lean_ctor_get(v___x_1175_, 3);
lean_dec(v_unused_1264_);
v_unused_1265_ = lean_ctor_get(v___x_1175_, 2);
lean_dec(v_unused_1265_);
v_unused_1266_ = lean_ctor_get(v___x_1175_, 1);
lean_dec(v_unused_1266_);
v_unused_1267_ = lean_ctor_get(v___x_1175_, 0);
lean_dec(v_unused_1267_);
v___x_1192_ = v___x_1175_;
v_isShared_1193_ = v_isSharedCheck_1262_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v___x_1175_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1262_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
if (lean_obj_tag(v_l_1180_) == 0)
{
if (lean_obj_tag(v_r_1181_) == 0)
{
lean_object* v_size_1194_; lean_object* v_size_1195_; lean_object* v_k_1196_; lean_object* v_v_1197_; lean_object* v_l_1198_; lean_object* v_r_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_size_1194_ = lean_ctor_get(v_l_1180_, 0);
v_size_1195_ = lean_ctor_get(v_r_1181_, 0);
v_k_1196_ = lean_ctor_get(v_r_1181_, 1);
v_v_1197_ = lean_ctor_get(v_r_1181_, 2);
v_l_1198_ = lean_ctor_get(v_r_1181_, 3);
v_r_1199_ = lean_ctor_get(v_r_1181_, 4);
v___x_1200_ = lean_unsigned_to_nat(2u);
v___x_1201_ = lean_nat_mul(v___x_1200_, v_size_1194_);
v___x_1202_ = lean_nat_dec_lt(v_size_1195_, v___x_1201_);
lean_dec(v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1232_; 
lean_inc(v_r_1199_);
lean_inc(v_l_1198_);
lean_inc(v_v_1197_);
lean_inc(v_k_1196_);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_r_1181_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; lean_object* v_unused_1234_; lean_object* v_unused_1235_; lean_object* v_unused_1236_; lean_object* v_unused_1237_; 
v_unused_1233_ = lean_ctor_get(v_r_1181_, 4);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_r_1181_, 3);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_r_1181_, 2);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_r_1181_, 1);
lean_dec(v_unused_1236_);
v_unused_1237_ = lean_ctor_get(v_r_1181_, 0);
lean_dec(v_unused_1237_);
v___x_1204_ = v_r_1181_;
v_isShared_1205_ = v_isSharedCheck_1232_;
goto v_resetjp_1203_;
}
else
{
lean_dec(v_r_1181_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1232_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___x_1220_; lean_object* v___y_1222_; 
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_add(v___x_1206_, v_size_1177_);
lean_dec(v_size_1177_);
v___x_1208_ = lean_nat_add(v___x_1207_, v_size_1176_);
lean_dec(v___x_1207_);
v___x_1220_ = lean_nat_add(v___x_1206_, v_size_1194_);
if (lean_obj_tag(v_l_1198_) == 0)
{
lean_object* v_size_1230_; 
v_size_1230_ = lean_ctor_get(v_l_1198_, 0);
lean_inc(v_size_1230_);
v___y_1222_ = v_size_1230_;
goto v___jp_1221_;
}
else
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_unsigned_to_nat(0u);
v___y_1222_ = v___x_1231_;
goto v___jp_1221_;
}
v___jp_1209_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_nat_add(v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec(v___y_1211_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 4, v_r_993_);
lean_ctor_set(v___x_1204_, 3, v_r_1199_);
lean_ctor_set(v___x_1204_, 2, v_v_991_);
lean_ctor_set(v___x_1204_, 1, v_k_990_);
lean_ctor_set(v___x_1204_, 0, v___x_1213_);
v___x_1215_ = v___x_1204_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_r_1199_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v_r_993_);
v___x_1215_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1217_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 4, v___x_1215_);
lean_ctor_set(v___x_1192_, 3, v___y_1210_);
lean_ctor_set(v___x_1192_, 2, v_v_1197_);
lean_ctor_set(v___x_1192_, 1, v_k_1196_);
lean_ctor_set(v___x_1192_, 0, v___x_1208_);
v___x_1217_ = v___x_1192_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_k_1196_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_v_1197_);
lean_ctor_set(v_reuseFailAlloc_1218_, 3, v___y_1210_);
lean_ctor_set(v_reuseFailAlloc_1218_, 4, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
v___jp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_nat_add(v___x_1220_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec(v___x_1220_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v_l_1198_);
lean_ctor_set(v___x_995_, 3, v_l_1180_);
lean_ctor_set(v___x_995_, 2, v_v_1179_);
lean_ctor_set(v___x_995_, 1, v_k_1178_);
lean_ctor_set(v___x_995_, 0, v___x_1223_);
v___x_1225_ = v___x_995_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_k_1178_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_v_1179_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v_l_1180_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v_l_1198_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_nat_add(v___x_1206_, v_size_1176_);
if (lean_obj_tag(v_r_1199_) == 0)
{
lean_object* v_size_1227_; 
v_size_1227_ = lean_ctor_get(v_r_1199_, 0);
lean_inc(v_size_1227_);
v___y_1210_ = v___x_1225_;
v___y_1211_ = v___x_1226_;
v___y_1212_ = v_size_1227_;
goto v___jp_1209_;
}
else
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_unsigned_to_nat(0u);
v___y_1210_ = v___x_1225_;
v___y_1211_ = v___x_1226_;
v___y_1212_ = v___x_1228_;
goto v___jp_1209_;
}
}
}
}
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
lean_del_object(v___x_995_);
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = lean_nat_add(v___x_1238_, v_size_1177_);
lean_dec(v_size_1177_);
v___x_1240_ = lean_nat_add(v___x_1239_, v_size_1176_);
lean_dec(v___x_1239_);
v___x_1241_ = lean_nat_add(v___x_1238_, v_size_1176_);
v___x_1242_ = lean_nat_add(v___x_1241_, v_size_1195_);
lean_dec(v___x_1241_);
lean_inc_ref(v_r_993_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 4, v_r_993_);
lean_ctor_set(v___x_1192_, 3, v_r_1181_);
lean_ctor_set(v___x_1192_, 2, v_v_991_);
lean_ctor_set(v___x_1192_, 1, v_k_990_);
lean_ctor_set(v___x_1192_, 0, v___x_1242_);
v___x_1244_ = v___x_1192_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_r_1181_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_r_993_);
v___x_1244_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
v_isSharedCheck_1251_ = !lean_is_exclusive(v_r_993_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; lean_object* v_unused_1253_; lean_object* v_unused_1254_; lean_object* v_unused_1255_; lean_object* v_unused_1256_; 
v_unused_1252_ = lean_ctor_get(v_r_993_, 4);
lean_dec(v_unused_1252_);
v_unused_1253_ = lean_ctor_get(v_r_993_, 3);
lean_dec(v_unused_1253_);
v_unused_1254_ = lean_ctor_get(v_r_993_, 2);
lean_dec(v_unused_1254_);
v_unused_1255_ = lean_ctor_get(v_r_993_, 1);
lean_dec(v_unused_1255_);
v_unused_1256_ = lean_ctor_get(v_r_993_, 0);
lean_dec(v_unused_1256_);
v___x_1246_ = v_r_993_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_dec(v_r_993_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 4, v___x_1244_);
lean_ctor_set(v___x_1246_, 3, v_l_1180_);
lean_ctor_set(v___x_1246_, 2, v_v_1179_);
lean_ctor_set(v___x_1246_, 1, v_k_1178_);
lean_ctor_set(v___x_1246_, 0, v___x_1240_);
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_k_1178_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_v_1179_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_l_1180_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v___x_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec_ref(v_l_1180_);
lean_del_object(v___x_1192_);
lean_dec(v_v_1179_);
lean_dec(v_k_1178_);
lean_dec(v_size_1177_);
lean_dec_ref(v_r_993_);
lean_del_object(v___x_995_);
lean_dec(v_v_991_);
lean_dec(v_k_990_);
v___x_1258_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7);
v___x_1259_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1258_);
return v___x_1259_;
}
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_del_object(v___x_1192_);
lean_dec(v_r_1181_);
lean_dec(v_v_1179_);
lean_dec(v_k_1178_);
lean_dec(v_size_1177_);
lean_dec_ref(v_r_993_);
lean_del_object(v___x_995_);
lean_dec(v_v_991_);
lean_dec(v_k_990_);
v___x_1260_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8);
v___x_1261_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1260_);
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_size_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
v_size_1268_ = lean_ctor_get(v_r_993_, 0);
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_nat_add(v___x_1269_, v_size_1268_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 3, v___x_1175_);
lean_ctor_set(v___x_995_, 0, v___x_1270_);
v___x_1272_ = v___x_995_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_r_993_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_l_1274_; 
v_l_1274_ = lean_ctor_get(v___x_1175_, 3);
lean_inc(v_l_1274_);
if (lean_obj_tag(v_l_1274_) == 0)
{
lean_object* v_r_1275_; 
v_r_1275_ = lean_ctor_get(v___x_1175_, 4);
lean_inc(v_r_1275_);
if (lean_obj_tag(v_r_1275_) == 0)
{
lean_object* v_size_1276_; lean_object* v_k_1277_; lean_object* v_v_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1292_; 
v_size_1276_ = lean_ctor_get(v___x_1175_, 0);
v_k_1277_ = lean_ctor_get(v___x_1175_, 1);
v_v_1278_ = lean_ctor_get(v___x_1175_, 2);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; lean_object* v_unused_1294_; 
v_unused_1293_ = lean_ctor_get(v___x_1175_, 4);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v___x_1175_, 3);
lean_dec(v_unused_1294_);
v___x_1280_ = v___x_1175_;
v_isShared_1281_ = v_isSharedCheck_1292_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_v_1278_);
lean_inc(v_k_1277_);
lean_inc(v_size_1276_);
lean_dec(v___x_1175_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1292_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v_size_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v_size_1282_ = lean_ctor_get(v_r_1275_, 0);
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = lean_nat_add(v___x_1283_, v_size_1276_);
lean_dec(v_size_1276_);
v___x_1285_ = lean_nat_add(v___x_1283_, v_size_1282_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 4, v_r_993_);
lean_ctor_set(v___x_1280_, 3, v_r_1275_);
lean_ctor_set(v___x_1280_, 2, v_v_991_);
lean_ctor_set(v___x_1280_, 1, v_k_990_);
lean_ctor_set(v___x_1280_, 0, v___x_1285_);
v___x_1287_ = v___x_1280_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_r_1275_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v_r_993_);
v___x_1287_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1289_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___x_1287_);
lean_ctor_set(v___x_995_, 3, v_l_1274_);
lean_ctor_set(v___x_995_, 2, v_v_1278_);
lean_ctor_set(v___x_995_, 1, v_k_1277_);
lean_ctor_set(v___x_995_, 0, v___x_1284_);
v___x_1289_ = v___x_995_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_k_1277_);
lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_v_1278_);
lean_ctor_set(v_reuseFailAlloc_1290_, 3, v_l_1274_);
lean_ctor_set(v_reuseFailAlloc_1290_, 4, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_k_1295_; lean_object* v_v_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1308_; 
v_k_1295_ = lean_ctor_get(v___x_1175_, 1);
v_v_1296_ = lean_ctor_get(v___x_1175_, 2);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; lean_object* v_unused_1310_; lean_object* v_unused_1311_; 
v_unused_1309_ = lean_ctor_get(v___x_1175_, 4);
lean_dec(v_unused_1309_);
v_unused_1310_ = lean_ctor_get(v___x_1175_, 3);
lean_dec(v_unused_1310_);
v_unused_1311_ = lean_ctor_get(v___x_1175_, 0);
lean_dec(v_unused_1311_);
v___x_1298_ = v___x_1175_;
v_isShared_1299_ = v_isSharedCheck_1308_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_v_1296_);
lean_inc(v_k_1295_);
lean_dec(v___x_1175_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1308_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1300_ = lean_unsigned_to_nat(3u);
v___x_1301_ = lean_unsigned_to_nat(1u);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 3, v_r_1275_);
lean_ctor_set(v___x_1298_, 2, v_v_991_);
lean_ctor_set(v___x_1298_, 1, v_k_990_);
lean_ctor_set(v___x_1298_, 0, v___x_1301_);
v___x_1303_ = v___x_1298_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_r_1275_);
lean_ctor_set(v_reuseFailAlloc_1307_, 4, v_r_1275_);
v___x_1303_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___x_1303_);
lean_ctor_set(v___x_995_, 3, v_l_1274_);
lean_ctor_set(v___x_995_, 2, v_v_1296_);
lean_ctor_set(v___x_995_, 1, v_k_1295_);
lean_ctor_set(v___x_995_, 0, v___x_1300_);
v___x_1305_ = v___x_995_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_k_1295_);
lean_ctor_set(v_reuseFailAlloc_1306_, 2, v_v_1296_);
lean_ctor_set(v_reuseFailAlloc_1306_, 3, v_l_1274_);
lean_ctor_set(v_reuseFailAlloc_1306_, 4, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
else
{
lean_object* v_r_1312_; 
v_r_1312_ = lean_ctor_get(v___x_1175_, 4);
lean_inc(v_r_1312_);
if (lean_obj_tag(v_r_1312_) == 0)
{
lean_object* v_k_1313_; lean_object* v_v_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1338_; 
v_k_1313_ = lean_ctor_get(v___x_1175_, 1);
v_v_1314_ = lean_ctor_get(v___x_1175_, 2);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; lean_object* v_unused_1340_; lean_object* v_unused_1341_; 
v_unused_1339_ = lean_ctor_get(v___x_1175_, 4);
lean_dec(v_unused_1339_);
v_unused_1340_ = lean_ctor_get(v___x_1175_, 3);
lean_dec(v_unused_1340_);
v_unused_1341_ = lean_ctor_get(v___x_1175_, 0);
lean_dec(v_unused_1341_);
v___x_1316_ = v___x_1175_;
v_isShared_1317_ = v_isSharedCheck_1338_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_v_1314_);
lean_inc(v_k_1313_);
lean_dec(v___x_1175_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1338_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v_k_1318_; lean_object* v_v_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1334_; 
v_k_1318_ = lean_ctor_get(v_r_1312_, 1);
v_v_1319_ = lean_ctor_get(v_r_1312_, 2);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_r_1312_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; lean_object* v_unused_1336_; lean_object* v_unused_1337_; 
v_unused_1335_ = lean_ctor_get(v_r_1312_, 4);
lean_dec(v_unused_1335_);
v_unused_1336_ = lean_ctor_get(v_r_1312_, 3);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_r_1312_, 0);
lean_dec(v_unused_1337_);
v___x_1321_ = v_r_1312_;
v_isShared_1322_ = v_isSharedCheck_1334_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_v_1319_);
lean_inc(v_k_1318_);
lean_dec(v_r_1312_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1334_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1323_ = lean_unsigned_to_nat(3u);
v___x_1324_ = lean_unsigned_to_nat(1u);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 4, v_l_1274_);
lean_ctor_set(v___x_1321_, 3, v_l_1274_);
lean_ctor_set(v___x_1321_, 2, v_v_1314_);
lean_ctor_set(v___x_1321_, 1, v_k_1313_);
lean_ctor_set(v___x_1321_, 0, v___x_1324_);
v___x_1326_ = v___x_1321_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_k_1313_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_v_1314_);
lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_l_1274_);
lean_ctor_set(v_reuseFailAlloc_1333_, 4, v_l_1274_);
v___x_1326_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v_l_1274_);
lean_ctor_set(v___x_1316_, 2, v_v_991_);
lean_ctor_set(v___x_1316_, 1, v_k_990_);
lean_ctor_set(v___x_1316_, 0, v___x_1324_);
v___x_1328_ = v___x_1316_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_l_1274_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v_l_1274_);
v___x_1328_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1330_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___x_1328_);
lean_ctor_set(v___x_995_, 3, v___x_1326_);
lean_ctor_set(v___x_995_, 2, v_v_1319_);
lean_ctor_set(v___x_995_, 1, v_k_1318_);
lean_ctor_set(v___x_995_, 0, v___x_1323_);
v___x_1330_ = v___x_995_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1342_ = lean_unsigned_to_nat(2u);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v_r_1312_);
lean_ctor_set(v___x_995_, 3, v___x_1175_);
lean_ctor_set(v___x_995_, 0, v___x_1342_);
v___x_1344_ = v___x_995_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v_r_1312_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_unsigned_to_nat(1u);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___x_1175_);
lean_ctor_set(v___x_995_, 3, v___x_1175_);
lean_ctor_set(v___x_995_, 0, v___x_1346_);
v___x_1348_ = v___x_995_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v___x_1175_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_unsigned_to_nat(1u);
v___x_1352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v_k_986_);
lean_ctor_set(v___x_1352_, 2, v_v_987_);
lean_ctor_set(v___x_1352_, 3, v_t_988_);
lean_ctor_set(v___x_1352_, 4, v_t_988_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(lean_object* v_init_1353_, lean_object* v_x_1354_){
_start:
{
if (lean_obj_tag(v_x_1354_) == 0)
{
lean_object* v_k_1355_; lean_object* v_v_1356_; lean_object* v_l_1357_; lean_object* v_r_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_k_1355_ = lean_ctor_get(v_x_1354_, 1);
lean_inc(v_k_1355_);
v_v_1356_ = lean_ctor_get(v_x_1354_, 2);
lean_inc(v_v_1356_);
v_l_1357_ = lean_ctor_get(v_x_1354_, 3);
lean_inc(v_l_1357_);
v_r_1358_ = lean_ctor_get(v_x_1354_, 4);
lean_inc(v_r_1358_);
lean_dec_ref(v_x_1354_);
v___x_1359_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v_init_1353_, v_l_1357_);
v___x_1360_ = 1;
v___x_1361_ = l_Lean_Name_toString(v_k_1355_, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_v_1356_);
v___x_1363_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v___x_1361_, v___x_1362_, v___x_1359_);
v_init_1353_ = v___x_1363_;
v_x_1354_ = v_r_1358_;
goto _start;
}
else
{
return v_init_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(lean_object* v_m_1365_){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = lean_box(1);
v___x_1367_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v___x_1366_, v_m_1365_);
v___x_1368_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object* v_env_1374_){
_start:
{
lean_object* v_lake_1375_; lean_object* v_lean_1376_; lean_object* v_elan_x3f_1377_; lean_object* v_pkgUrlMap_1378_; uint8_t v_noCache_1379_; lean_object* v_lakeConfig_x3f_1380_; lean_object* v_cacheKey_x3f_1381_; lean_object* v_cacheArtifactEndpoint_x3f_1382_; lean_object* v_cacheRevisionEndpoint_x3f_1383_; lean_object* v_cacheService_x3f_1384_; lean_object* v_toolchain_1385_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___x_1514_; lean_object* v___y_1516_; 
v_lake_1375_ = lean_ctor_get(v_env_1374_, 0);
lean_inc_ref(v_lake_1375_);
v_lean_1376_ = lean_ctor_get(v_env_1374_, 1);
lean_inc_ref(v_lean_1376_);
v_elan_x3f_1377_ = lean_ctor_get(v_env_1374_, 2);
lean_inc(v_elan_x3f_1377_);
v_pkgUrlMap_1378_ = lean_ctor_get(v_env_1374_, 5);
lean_inc(v_pkgUrlMap_1378_);
v_noCache_1379_ = lean_ctor_get_uint8(v_env_1374_, sizeof(void*)*19);
v_lakeConfig_x3f_1380_ = lean_ctor_get(v_env_1374_, 9);
lean_inc(v_lakeConfig_x3f_1380_);
v_cacheKey_x3f_1381_ = lean_ctor_get(v_env_1374_, 10);
lean_inc(v_cacheKey_x3f_1381_);
v_cacheArtifactEndpoint_x3f_1382_ = lean_ctor_get(v_env_1374_, 11);
lean_inc(v_cacheArtifactEndpoint_x3f_1382_);
v_cacheRevisionEndpoint_x3f_1383_ = lean_ctor_get(v_env_1374_, 12);
lean_inc(v_cacheRevisionEndpoint_x3f_1383_);
v_cacheService_x3f_1384_ = lean_ctor_get(v_env_1374_, 13);
lean_inc(v_cacheService_x3f_1384_);
v_toolchain_1385_ = lean_ctor_get(v_env_1374_, 18);
lean_inc_ref(v_toolchain_1385_);
lean_dec_ref(v_env_1374_);
v___x_1514_ = ((lean_object*)(l_Lake_Env_baseVars___closed__3));
if (lean_obj_tag(v_elan_x3f_1377_) == 0)
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_box(0);
v___y_1516_ = v___x_1529_;
goto v___jp_1515_;
}
else
{
lean_object* v_val_1530_; lean_object* v_elan_1531_; lean_object* v___x_1532_; 
v_val_1530_ = lean_ctor_get(v_elan_x3f_1377_, 0);
v_elan_1531_ = lean_ctor_get(v_val_1530_, 1);
lean_inc_ref(v_elan_1531_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_elan_1531_);
v___y_1516_ = v___x_1532_;
goto v___jp_1515_;
}
v___jp_1386_:
{
lean_object* v_sysroot_1400_; lean_object* v_lean_1401_; lean_object* v_ar_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_sysroot_1400_ = lean_ctor_get(v_lean_1376_, 0);
v_lean_1401_ = lean_ctor_get(v_lean_1376_, 7);
v_ar_1402_ = lean_ctor_get(v_lean_1376_, 13);
lean_inc_ref(v___y_1387_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___y_1387_);
lean_ctor_set(v___x_1403_, 1, v___y_1399_);
v___x_1404_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__7));
lean_inc_ref(v_lean_1401_);
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v_lean_1401_);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__10));
lean_inc_ref(v_sysroot_1400_);
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v_sysroot_1400_);
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__12));
lean_inc_ref(v_ar_1402_);
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_ar_1402_);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = ((lean_object*)(l_Lake_Env_baseVars___closed__0));
v___x_1414_ = l_Lake_LeanInstall_leanCc_x3f(v_lean_1376_);
lean_dec_ref(v_lean_1376_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = lean_unsigned_to_nat(16u);
v___x_1417_ = lean_mk_empty_array_with_capacity(v___x_1416_);
v___x_1418_ = lean_array_push(v___x_1417_, v___y_1393_);
v___x_1419_ = lean_array_push(v___x_1418_, v___y_1392_);
v___x_1420_ = lean_array_push(v___x_1419_, v___y_1390_);
v___x_1421_ = lean_array_push(v___x_1420_, v___y_1388_);
v___x_1422_ = lean_array_push(v___x_1421_, v___y_1396_);
v___x_1423_ = lean_array_push(v___x_1422_, v___y_1394_);
v___x_1424_ = lean_array_push(v___x_1423_, v___y_1389_);
v___x_1425_ = lean_array_push(v___x_1424_, v___y_1395_);
v___x_1426_ = lean_array_push(v___x_1425_, v___y_1398_);
v___x_1427_ = lean_array_push(v___x_1426_, v___y_1391_);
v___x_1428_ = lean_array_push(v___x_1427_, v___y_1397_);
v___x_1429_ = lean_array_push(v___x_1428_, v___x_1403_);
v___x_1430_ = lean_array_push(v___x_1429_, v___x_1406_);
v___x_1431_ = lean_array_push(v___x_1430_, v___x_1409_);
v___x_1432_ = lean_array_push(v___x_1431_, v___x_1412_);
v___x_1433_ = lean_array_push(v___x_1432_, v___x_1415_);
return v___x_1433_;
}
v___jp_1434_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_inc_ref(v___y_1443_);
v___x_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___y_1443_);
lean_inc_ref(v___y_1438_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___y_1438_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = ((lean_object*)(l_Lake_Env_compute___closed__5));
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
lean_ctor_set(v___x_1447_, 1, v_cacheKey_x3f_1381_);
v___x_1448_ = ((lean_object*)(l_Lake_Env_compute___closed__6));
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
lean_ctor_set(v___x_1449_, 1, v_cacheArtifactEndpoint_x3f_1382_);
v___x_1450_ = ((lean_object*)(l_Lake_Env_compute___closed__7));
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
lean_ctor_set(v___x_1451_, 1, v_cacheRevisionEndpoint_x3f_1383_);
v___x_1452_ = ((lean_object*)(l_Lake_Env_compute___closed__8));
if (lean_obj_tag(v_cacheService_x3f_1384_) == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_box(0);
v___y_1387_ = v___x_1452_;
v___y_1388_ = v___y_1435_;
v___y_1389_ = v___y_1437_;
v___y_1390_ = v___y_1436_;
v___y_1391_ = v___x_1449_;
v___y_1392_ = v___y_1440_;
v___y_1393_ = v___y_1439_;
v___y_1394_ = v___y_1441_;
v___y_1395_ = v___x_1445_;
v___y_1396_ = v___y_1442_;
v___y_1397_ = v___x_1451_;
v___y_1398_ = v___x_1447_;
v___y_1399_ = v___x_1453_;
goto v___jp_1386_;
}
else
{
lean_object* v_val_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_val_1454_ = lean_ctor_get(v_cacheService_x3f_1384_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_cacheService_x3f_1384_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v_cacheService_x3f_1384_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_val_1454_);
lean_dec(v_cacheService_x3f_1384_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_val_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
v___y_1387_ = v___x_1452_;
v___y_1388_ = v___y_1435_;
v___y_1389_ = v___y_1437_;
v___y_1390_ = v___y_1436_;
v___y_1391_ = v___x_1449_;
v___y_1392_ = v___y_1440_;
v___y_1393_ = v___y_1439_;
v___y_1394_ = v___y_1441_;
v___y_1395_ = v___x_1445_;
v___y_1396_ = v___y_1442_;
v___y_1397_ = v___x_1451_;
v___y_1398_ = v___x_1447_;
v___y_1399_ = v___x_1459_;
goto v___jp_1386_;
}
}
}
}
v___jp_1462_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_inc_ref(v___y_1468_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___y_1468_);
lean_ctor_set(v___x_1470_, 1, v___y_1469_);
v___x_1471_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0));
v___x_1472_ = l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(v_pkgUrlMap_1378_);
v___x_1473_ = l_Lean_Json_compress(v___x_1472_);
v___x_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1471_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = ((lean_object*)(l_Lake_Env_compute___closed__2));
if (v_noCache_1379_ == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = ((lean_object*)(l_Lake_Env_baseVars___closed__1));
v___y_1435_ = v___y_1463_;
v___y_1436_ = v___y_1464_;
v___y_1437_ = v___x_1475_;
v___y_1438_ = v___x_1476_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1465_;
v___y_1441_ = v___x_1470_;
v___y_1442_ = v___y_1467_;
v___y_1443_ = v___x_1477_;
goto v___jp_1434_;
}
else
{
lean_object* v___x_1478_; 
v___x_1478_ = ((lean_object*)(l_Lake_Env_baseVars___closed__2));
v___y_1435_ = v___y_1463_;
v___y_1436_ = v___y_1464_;
v___y_1437_ = v___x_1475_;
v___y_1438_ = v___x_1476_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1465_;
v___y_1441_ = v___x_1470_;
v___y_1442_ = v___y_1467_;
v___y_1443_ = v___x_1478_;
goto v___jp_1434_;
}
}
v___jp_1479_:
{
lean_object* v_home_1484_; lean_object* v_lake_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v_home_1484_ = lean_ctor_get(v_lake_1375_, 0);
lean_inc_ref(v_home_1484_);
v_lake_1485_ = lean_ctor_get(v_lake_1375_, 5);
lean_inc_ref(v_lake_1485_);
lean_dec_ref(v_lake_1375_);
lean_inc_ref(v___y_1482_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___y_1482_);
lean_ctor_set(v___x_1486_, 1, v___y_1483_);
v___x_1487_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__1));
v___x_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1488_, 0, v_lake_1485_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__5));
v___x_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_home_1484_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
v___x_1493_ = ((lean_object*)(l_Lake_Env_compute___closed__4));
if (lean_obj_tag(v_lakeConfig_x3f_1380_) == 1)
{
lean_object* v_val_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
v_val_1494_ = lean_ctor_get(v_lakeConfig_x3f_1380_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_lakeConfig_x3f_1380_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v_lakeConfig_x3f_1380_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_val_1494_);
lean_dec(v_lakeConfig_x3f_1380_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_val_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
v___y_1463_ = v___x_1489_;
v___y_1464_ = v___x_1486_;
v___y_1465_ = v___y_1481_;
v___y_1466_ = v___y_1480_;
v___y_1467_ = v___x_1492_;
v___y_1468_ = v___x_1493_;
v___y_1469_ = v___x_1499_;
goto v___jp_1462_;
}
}
}
else
{
lean_object* v___x_1502_; 
lean_dec(v_lakeConfig_x3f_1380_);
v___x_1502_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_1463_ = v___x_1489_;
v___y_1464_ = v___x_1486_;
v___y_1465_ = v___y_1481_;
v___y_1466_ = v___y_1480_;
v___y_1467_ = v___x_1492_;
v___y_1468_ = v___x_1493_;
v___y_1469_ = v___x_1502_;
goto v___jp_1462_;
}
}
v___jp_1503_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
lean_inc_ref(v___y_1505_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___y_1505_);
lean_ctor_set(v___x_1507_, 1, v___y_1506_);
v___x_1508_ = ((lean_object*)(l_Lake_Env_computeToolchain___closed__0));
v___x_1509_ = lean_string_utf8_byte_size(v_toolchain_1385_);
v___x_1510_ = lean_unsigned_to_nat(0u);
v___x_1511_ = lean_nat_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_toolchain_1385_);
v___y_1480_ = v___y_1504_;
v___y_1481_ = v___x_1507_;
v___y_1482_ = v___x_1508_;
v___y_1483_ = v___x_1512_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1513_; 
lean_dec_ref(v_toolchain_1385_);
v___x_1513_ = lean_box(0);
v___y_1480_ = v___y_1504_;
v___y_1481_ = v___x_1507_;
v___y_1482_ = v___x_1508_;
v___y_1483_ = v___x_1513_;
goto v___jp_1479_;
}
}
v___jp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1514_);
lean_ctor_set(v___x_1517_, 1, v___y_1516_);
v___x_1518_ = ((lean_object*)(l_Lake_Env_baseVars___closed__4));
if (lean_obj_tag(v_elan_x3f_1377_) == 0)
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_box(0);
v___y_1504_ = v___x_1517_;
v___y_1505_ = v___x_1518_;
v___y_1506_ = v___x_1519_;
goto v___jp_1503_;
}
else
{
lean_object* v_val_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1528_; 
v_val_1520_ = lean_ctor_get(v_elan_x3f_1377_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_elan_x3f_1377_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1522_ = v_elan_x3f_1377_;
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_val_1520_);
lean_dec(v_elan_x3f_1377_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_home_1524_; lean_object* v___x_1526_; 
v_home_1524_ = lean_ctor_get(v_val_1520_, 0);
lean_inc_ref(v_home_1524_);
lean_dec(v_val_1520_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v_home_1524_);
v___x_1526_ = v___x_1522_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_home_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
v___y_1504_ = v___x_1517_;
v___y_1505_ = v___x_1518_;
v___y_1506_ = v___x_1526_;
goto v___jp_1503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1533_, lean_object* v_msg_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v_msg_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(lean_object* v_00_u03b2_1536_, lean_object* v_k_1537_, lean_object* v_v_1538_, lean_object* v_t_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_1537_, v_v_1538_, v_t_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(lean_object* v_init_1541_, lean_object* v_t_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v_init_1541_, v_t_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object* v_env_1548_){
_start:
{
lean_object* v_enableArtifactCache_x3f_1549_; lean_object* v_lakeCache_x3f_1550_; lean_object* v___x_1551_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___x_1592_; lean_object* v___y_1594_; 
v_enableArtifactCache_x3f_1549_ = lean_ctor_get(v_env_1548_, 6);
v_lakeCache_x3f_1550_ = lean_ctor_get(v_env_1548_, 7);
lean_inc(v_lakeCache_x3f_1550_);
lean_inc_ref(v_env_1548_);
v___x_1551_ = l_Lake_Env_baseVars(v_env_1548_);
v___x_1592_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
if (lean_obj_tag(v_lakeCache_x3f_1550_) == 1)
{
lean_object* v_val_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_val_1602_ = lean_ctor_get(v_lakeCache_x3f_1550_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_lakeCache_x3f_1550_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v_lakeCache_x3f_1550_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_val_1602_);
lean_dec(v_lakeCache_x3f_1550_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_val_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
v___y_1594_ = v___x_1607_;
goto v___jp_1593_;
}
}
}
else
{
lean_object* v___x_1610_; 
lean_dec(v_lakeCache_x3f_1550_);
v___x_1610_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_1594_ = v___x_1610_;
goto v___jp_1593_;
}
v___jp_1552_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v_vars_1584_; uint8_t v___x_1585_; 
lean_inc(v___y_1555_);
lean_inc_ref(v___y_1554_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___y_1554_);
lean_ctor_set(v___x_1556_, 1, v___y_1555_);
v___x_1557_ = ((lean_object*)(l_Lake_Env_compute___closed__10));
v___x_1558_ = l_Lake_Env_leanPath(v_env_1548_);
v___x_1559_ = l_System_SearchPath_toString(v___x_1558_);
v___x_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1557_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = ((lean_object*)(l_Lake_Env_compute___closed__11));
v___x_1563_ = l_Lake_Env_leanSrcPath(v_env_1548_);
v___x_1564_ = l_System_SearchPath_toString(v___x_1563_);
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1562_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = ((lean_object*)(l_Lake_Env_compute___closed__9));
v___x_1568_ = l_Lake_Env_leanGithash(v_env_1548_);
v___x_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1567_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = ((lean_object*)(l_Lake_Env_compute___closed__12));
v___x_1572_ = l_Lake_Env_path(v_env_1548_);
v___x_1573_ = l_System_SearchPath_toString(v___x_1572_);
v___x_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1571_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_unsigned_to_nat(6u);
v___x_1577_ = lean_mk_empty_array_with_capacity(v___x_1576_);
v___x_1578_ = lean_array_push(v___x_1577_, v___y_1553_);
v___x_1579_ = lean_array_push(v___x_1578_, v___x_1556_);
v___x_1580_ = lean_array_push(v___x_1579_, v___x_1561_);
v___x_1581_ = lean_array_push(v___x_1580_, v___x_1566_);
v___x_1582_ = lean_array_push(v___x_1581_, v___x_1570_);
v___x_1583_ = lean_array_push(v___x_1582_, v___x_1575_);
v_vars_1584_ = l_Array_append___redArg(v___x_1551_, v___x_1583_);
lean_dec_ref(v___x_1583_);
v___x_1585_ = l_System_Platform_isWindows;
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1586_ = l_Lake_sharedLibPathEnvVar;
v___x_1587_ = l_Lake_Env_sharedLibPath(v_env_1548_);
v___x_1588_ = l_System_SearchPath_toString(v___x_1587_);
v___x_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1586_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_array_push(v_vars_1584_, v___x_1590_);
return v___x_1591_;
}
else
{
lean_dec_ref(v_env_1548_);
return v_vars_1584_;
}
}
v___jp_1593_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1592_);
lean_ctor_set(v___x_1595_, 1, v___y_1594_);
v___x_1596_ = ((lean_object*)(l_Lake_Env_compute___closed__3));
if (lean_obj_tag(v_enableArtifactCache_x3f_1549_) == 1)
{
lean_object* v_val_1597_; uint8_t v___x_1598_; 
v_val_1597_ = lean_ctor_get(v_enableArtifactCache_x3f_1549_, 0);
v___x_1598_ = lean_unbox(v_val_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; 
v___x_1599_ = ((lean_object*)(l_Lake_Env_vars___closed__0));
v___y_1553_ = v___x_1595_;
v___y_1554_ = v___x_1596_;
v___y_1555_ = v___x_1599_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1600_; 
v___x_1600_ = ((lean_object*)(l_Lake_Env_vars___closed__1));
v___y_1553_ = v___x_1595_;
v___y_1554_ = v___x_1596_;
v___y_1555_ = v___x_1600_;
goto v___jp_1552_;
}
}
else
{
lean_object* v___x_1601_; 
v___x_1601_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_1553_ = v___x_1595_;
v___y_1554_ = v___x_1596_;
v___y_1555_ = v___x_1601_;
goto v___jp_1552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object* v_env_1611_){
_start:
{
lean_object* v_lake_1612_; lean_object* v_lean_1613_; lean_object* v_libDir_1614_; lean_object* v_leanLibDir_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_lake_1612_ = lean_ctor_get(v_env_1611_, 0);
v_lean_1613_ = lean_ctor_get(v_env_1611_, 1);
v_libDir_1614_ = lean_ctor_get(v_lake_1612_, 3);
v_leanLibDir_1615_ = lean_ctor_get(v_lean_1613_, 3);
v___x_1616_ = l_Lake_Env_leanPath(v_env_1611_);
lean_inc_ref(v_leanLibDir_1615_);
v___x_1617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_leanLibDir_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
lean_inc_ref(v_libDir_1614_);
v___x_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_libDir_1614_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object* v_env_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lake_Env_leanSearchPath(v_env_1619_);
lean_dec_ref(v_env_1619_);
return v_res_1620_;
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
res = runtime_initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
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
res = initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Env(builtin);
}
#ifdef __cplusplus
}
#endif
