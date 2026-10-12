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
uint8_t lean_string_compare(lean_object*, lean_object*);
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_Env_compute___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "LAKE_RESTORE_ARTIFACTS"};
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
static const lean_string_object l_Lake_Env_compute___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "RESERVOIR_API_BASE_URL"};
static const lean_object* l_Lake_Env_compute___closed__16 = (const lean_object*)&l_Lake_Env_compute___closed__16_value;
static const lean_string_object l_Lake_Env_compute___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "https://reservoir.lean-lang.org/api"};
static const lean_object* l_Lake_Env_compute___closed__17 = (const lean_object*)&l_Lake_Env_compute___closed__17_value;
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
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
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
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__0___boxed(lean_object*);
static const lean_ctor_object l_Lake_Env_vars___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Env_baseVars___closed__1_value)}};
static const lean_object* l_Lake_Env_vars___lam__1___closed__0 = (const lean_object*)&l_Lake_Env_vars___lam__1___closed__0_value;
static const lean_ctor_object l_Lake_Env_vars___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Env_baseVars___closed__2_value)}};
static const lean_object* l_Lake_Env_vars___lam__1___closed__1 = (const lean_object*)&l_Lake_Env_vars___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__1(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__1___boxed(lean_object*);
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
v___x_9_ = lean_alloc_ctor(0, 20, 2);
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
lean_ctor_set(v___x_9_, 14, v___x_6_);
lean_ctor_set(v___x_9_, 15, v___x_2_);
lean_ctor_set(v___x_9_, 16, v___x_2_);
lean_ctor_set(v___x_9_, 17, v___x_2_);
lean_ctor_set(v___x_9_, 18, v___x_2_);
lean_ctor_set(v___x_9_, 19, v___x_5_);
lean_ctor_set_uint8(v___x_9_, sizeof(void*)*20, v___x_3_);
lean_ctor_set_uint8(v___x_9_, sizeof(void*)*20 + 1, v___x_3_);
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
lean_object* l_Lake_getUserHome_x3f(){
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
lean_dec_ref_known(v___x_29_, 1);
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
LEAN_EXPORT void l_Lake_getUserHome_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_44_;
v_res_44_ = l_Lake_getUserHome_x3f();
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f___boxed(lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lake_getUserHome_x3f();
return v_res_46_;
}
}
lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(lean_object* v_userHome_x3f_49_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0));
v___x_52_ = lean_io_getenv(v___x_51_);
if (lean_obj_tag(v___x_52_) == 1)
{
lean_object* v_val_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
lean_dec(v_userHome_x3f_49_);
v_val_53_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_52_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_val_53_);
lean_dec(v___x_52_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_val_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
else
{
lean_dec(v___x_52_);
if (lean_obj_tag(v_userHome_x3f_49_) == 1)
{
lean_object* v_val_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_70_; 
v_val_61_ = lean_ctor_get(v_userHome_x3f_49_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v_userHome_x3f_49_);
if (v_isSharedCheck_70_ == 0)
{
v___x_63_ = v_userHome_x3f_49_;
v_isShared_64_ = v_isSharedCheck_70_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_val_61_);
lean_dec(v_userHome_x3f_49_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_70_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_65_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
v___x_66_ = l_System_FilePath_join(v_val_61_, v___x_65_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_66_);
v___x_68_ = v___x_63_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
else
{
lean_object* v___x_71_; 
lean_dec(v_userHome_x3f_49_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_userHome_x3f_49_ = stack[0].m_obj;
lean_object* v_res_72_;
v_res_72_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_49_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___boxed(lean_object* v_userHome_x3f_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_73_);
return v_res_75_;
}
}
lean_object* l_Lake_getSystemCacheHome_x3f(){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0));
v___x_78_ = lean_io_getenv(v___x_77_);
if (lean_obj_tag(v___x_78_) == 1)
{
lean_object* v_val_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_val_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_val_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_val_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
else
{
lean_object* v___x_87_; 
lean_dec(v___x_78_);
v___x_87_ = l_Lake_getUserHome_x3f();
if (lean_obj_tag(v___x_87_) == 1)
{
lean_object* v_val_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_97_; 
v_val_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_97_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_97_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_val_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_97_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_92_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
v___x_93_ = l_System_FilePath_join(v_val_88_, v___x_92_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_93_);
v___x_95_ = v___x_90_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
else
{
lean_object* v___x_98_; 
lean_dec(v___x_87_);
v___x_98_ = lean_box(0);
return v___x_98_;
}
}
}
}
LEAN_EXPORT void l_Lake_getSystemCacheHome_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_99_;
v_res_99_ = l_Lake_getSystemCacheHome_x3f();
stack->m_obj
 = v_res_99_;
}
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f___boxed(lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lake_getSystemCacheHome_x3f();
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(lean_object* v_elan_104_, lean_object* v_toolchain_105_){
_start:
{
lean_object* v_toolchainsDir_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_toolchainsDir_106_ = lean_ctor_get(v_elan_104_, 3);
lean_inc_ref(v_toolchainsDir_106_);
lean_dec_ref(v_elan_104_);
v___x_107_ = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_105_, v___x_107_, v___x_108_);
v___x_110_ = l_System_FilePath_join(v_toolchainsDir_106_, v___x_109_);
v___x_111_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_112_ = l_System_FilePath_join(v___x_110_, v___x_111_);
v___x_113_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1));
v___x_114_ = l_System_FilePath_join(v___x_112_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___boxed(lean_object* v_elan_115_, lean_object* v_toolchain_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_elan_115_, v_toolchain_116_);
lean_dec_ref(v_toolchain_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(lean_object* v_elan_118_, lean_object* v_toolchain_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_string_utf8_byte_size(v_toolchain_119_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_elan_118_, v_toolchain_119_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; 
lean_dec_ref(v_elan_118_);
v___x_125_ = lean_box(0);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f___boxed(lean_object* v_elan_126_, lean_object* v_toolchain_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(v_elan_126_, v_toolchain_127_);
lean_dec_ref(v_toolchain_127_);
return v_res_128_;
}
}
lean_object* l_Lake_Env_computeToolchain(){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lake_Env_computeToolchain___closed__0));
v___x_132_ = lean_io_getenv(v___x_131_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_toolchain;
return v___x_133_;
}
else
{
lean_object* v_val_134_; 
v_val_134_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_134_);
lean_dec_ref_known(v___x_132_, 1);
return v_val_134_;
}
}
}
LEAN_EXPORT void l_Lake_Env_computeToolchain_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_135_;
v_res_135_ = l_Lake_Env_computeToolchain();
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain___boxed(lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lake_Env_computeToolchain();
return v_res_137_;
}
}
lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f(){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
v___x_141_ = lean_io_getenv(v___x_140_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_box(0);
return v___x_142_;
}
else
{
lean_object* v_val_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_154_; 
v_val_143_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_154_ == 0)
{
v___x_145_ = v___x_141_;
v_isShared_146_ = v_isSharedCheck_154_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_val_143_);
lean_dec(v___x_141_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_154_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_147_ = lean_string_utf8_byte_size(v_val_143_);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_nat_dec_eq(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
lean_del_object(v___x_145_);
lean_dec(v_val_143_);
v___x_150_ = lean_box(0);
return v___x_150_;
}
else
{
lean_object* v___x_152_; 
if (v_isShared_146_ == 0)
{
v___x_152_ = v___x_145_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_val_143_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_155_;
v_res_155_ = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f();
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___boxed(lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f();
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfSystem_x3f(lean_object* v_cacheHome_x3f_158_){
_start:
{
if (lean_obj_tag(v_cacheHome_x3f_158_) == 0)
{
lean_object* v___x_159_; 
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v_val_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_169_; 
v_val_160_ = lean_ctor_get(v_cacheHome_x3f_158_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v_cacheHome_x3f_158_);
if (v_isSharedCheck_169_ == 0)
{
v___x_162_ = v_cacheHome_x3f_158_;
v_isShared_163_ = v_isSharedCheck_169_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_val_160_);
lean_dec(v_cacheHome_x3f_158_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_169_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_164_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_165_ = l_System_FilePath_join(v_val_160_, v___x_164_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_165_);
v___x_167_ = v___x_162_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(lean_object* v_elan_x3f_170_, lean_object* v_toolchain_171_){
_start:
{
if (lean_obj_tag(v_elan_x3f_170_) == 0)
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
else
{
lean_object* v_val_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_185_; 
v_val_173_ = lean_ctor_get(v_elan_x3f_170_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_elan_x3f_170_);
if (v_isSharedCheck_185_ == 0)
{
v___x_175_ = v_elan_x3f_170_;
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_val_173_);
lean_dec(v_elan_x3f_170_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_177_ = lean_string_utf8_byte_size(v_toolchain_171_);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_nat_dec_eq(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_180_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_173_, v_toolchain_171_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_180_);
v___x_182_ = v___x_175_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
else
{
lean_object* v___x_184_; 
lean_del_object(v___x_175_);
lean_dec(v_val_173_);
v___x_184_ = lean_box(0);
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f___boxed(lean_object* v_elan_x3f_186_, lean_object* v_toolchain_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(v_elan_x3f_186_, v_toolchain_187_);
lean_dec_ref(v_toolchain_187_);
return v_res_188_;
}
}
lean_object* l_Lake_Env_computeCache_x3f(lean_object* v_elan_x3f_189_, lean_object* v_toolchain_190_){
_start:
{
lean_object* v_cache_193_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
v___x_208_ = lean_io_getenv(v___x_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
goto v___jp_201_;
}
else
{
lean_object* v_val_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_val_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_val_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = lean_string_utf8_byte_size(v_val_209_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_nat_dec_eq(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec(v_val_209_);
goto v___jp_201_;
}
else
{
lean_dec(v_elan_x3f_189_);
v_cache_193_ = v_val_209_;
goto v___jp_192_;
}
}
v___jp_192_:
{
lean_object* v___x_194_; 
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_cache_193_);
return v___x_194_;
}
v___jp_195_:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lake_getSystemCacheHome_x3f();
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v___x_197_; 
v___x_197_ = lean_box(0);
return v___x_197_;
}
else
{
lean_object* v_val_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_val_198_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_val_198_);
lean_dec_ref_known(v___x_196_, 1);
v___x_199_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_200_ = l_System_FilePath_join(v_val_198_, v___x_199_);
v_cache_193_ = v___x_200_;
goto v___jp_192_;
}
}
v___jp_201_:
{
if (lean_obj_tag(v_elan_x3f_189_) == 0)
{
goto v___jp_195_;
}
else
{
lean_object* v_val_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_val_202_ = lean_ctor_get(v_elan_x3f_189_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v_elan_x3f_189_, 1);
v___x_203_ = lean_string_utf8_byte_size(v_toolchain_190_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_nat_dec_eq(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
v___x_206_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_202_, v_toolchain_190_);
v_cache_193_ = v___x_206_;
goto v___jp_192_;
}
else
{
lean_dec(v_val_202_);
goto v___jp_195_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Env_computeCache_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_elan_x3f_189_ = stack[0].m_obj;
lean_object* v_toolchain_190_ = stack[1].m_obj;
lean_object* v_res_213_;
v_res_213_ = l_Lake_Env_computeCache_x3f(v_elan_x3f_189_, v_toolchain_190_);
stack->m_obj
 = v_res_213_;
}
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f___boxed(lean_object* v_elan_x3f_214_, lean_object* v_toolchain_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lake_Env_computeCache_x3f(v_elan_x3f_214_, v_toolchain_215_);
lean_dec_ref(v_toolchain_215_);
return v_res_217_;
}
}
lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(lean_object* v_elan_x3f_218_, lean_object* v_userHome_x3f_219_, lean_object* v_toolchain_220_, lean_object* v_env_221_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
v___x_224_ = lean_io_getenv(v___x_223_);
if (lean_obj_tag(v___x_224_) == 1)
{
lean_object* v_val_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_337_; 
lean_dec(v_userHome_x3f_219_);
lean_dec(v_elan_x3f_218_);
v_val_268_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_337_ == 0)
{
v___x_270_ = v___x_224_;
v_isShared_271_ = v_isSharedCheck_337_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_val_268_);
lean_dec(v___x_224_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_337_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_272_ = lean_string_utf8_byte_size(v_val_268_);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_nat_dec_eq(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v_lake_275_; lean_object* v_lean_276_; lean_object* v_elan_x3f_277_; lean_object* v_reservoirApiUrl_278_; lean_object* v_githashOverride_279_; lean_object* v_pkgUrlMap_280_; uint8_t v_noCache_281_; lean_object* v_enableArtifactCache_x3f_282_; lean_object* v_restoreAllArtifacts_x3f_283_; uint8_t v_noSystemCache_284_; lean_object* v_lakeConfig_x3f_285_; lean_object* v_cacheKey_x3f_286_; lean_object* v_cacheArtifactEndpoint_x3f_287_; lean_object* v_cacheRevisionEndpoint_x3f_288_; lean_object* v_cacheService_x3f_289_; lean_object* v_initLeanPath_290_; lean_object* v_initLeanSrcPath_291_; lean_object* v_initSharedLibPath_292_; lean_object* v_initPath_293_; lean_object* v_toolchain_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_305_; 
v_lake_275_ = lean_ctor_get(v_env_221_, 0);
v_lean_276_ = lean_ctor_get(v_env_221_, 1);
v_elan_x3f_277_ = lean_ctor_get(v_env_221_, 2);
v_reservoirApiUrl_278_ = lean_ctor_get(v_env_221_, 3);
v_githashOverride_279_ = lean_ctor_get(v_env_221_, 4);
v_pkgUrlMap_280_ = lean_ctor_get(v_env_221_, 5);
v_noCache_281_ = lean_ctor_get_uint8(v_env_221_, sizeof(void*)*20);
v_enableArtifactCache_x3f_282_ = lean_ctor_get(v_env_221_, 6);
v_restoreAllArtifacts_x3f_283_ = lean_ctor_get(v_env_221_, 7);
v_noSystemCache_284_ = lean_ctor_get_uint8(v_env_221_, sizeof(void*)*20 + 1);
v_lakeConfig_x3f_285_ = lean_ctor_get(v_env_221_, 10);
v_cacheKey_x3f_286_ = lean_ctor_get(v_env_221_, 11);
v_cacheArtifactEndpoint_x3f_287_ = lean_ctor_get(v_env_221_, 12);
v_cacheRevisionEndpoint_x3f_288_ = lean_ctor_get(v_env_221_, 13);
v_cacheService_x3f_289_ = lean_ctor_get(v_env_221_, 14);
v_initLeanPath_290_ = lean_ctor_get(v_env_221_, 15);
v_initLeanSrcPath_291_ = lean_ctor_get(v_env_221_, 16);
v_initSharedLibPath_292_ = lean_ctor_get(v_env_221_, 17);
v_initPath_293_ = lean_ctor_get(v_env_221_, 18);
v_toolchain_294_ = lean_ctor_get(v_env_221_, 19);
v_isSharedCheck_305_ = !lean_is_exclusive(v_env_221_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; lean_object* v_unused_307_; 
v_unused_306_ = lean_ctor_get(v_env_221_, 9);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_env_221_, 8);
lean_dec(v_unused_307_);
v___x_296_ = v_env_221_;
v_isShared_297_ = v_isSharedCheck_305_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_toolchain_294_);
lean_inc(v_initPath_293_);
lean_inc(v_initSharedLibPath_292_);
lean_inc(v_initLeanSrcPath_291_);
lean_inc(v_initLeanPath_290_);
lean_inc(v_cacheService_x3f_289_);
lean_inc(v_cacheRevisionEndpoint_x3f_288_);
lean_inc(v_cacheArtifactEndpoint_x3f_287_);
lean_inc(v_cacheKey_x3f_286_);
lean_inc(v_lakeConfig_x3f_285_);
lean_inc(v_restoreAllArtifacts_x3f_283_);
lean_inc(v_enableArtifactCache_x3f_282_);
lean_inc(v_pkgUrlMap_280_);
lean_inc(v_githashOverride_279_);
lean_inc(v_reservoirApiUrl_278_);
lean_inc(v_elan_x3f_277_);
lean_inc(v_lean_276_);
lean_inc(v_lake_275_);
lean_dec(v_env_221_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_305_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_271_ == 0)
{
v___x_299_ = v___x_270_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_val_268_);
v___x_299_ = v_reuseFailAlloc_304_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
lean_inc_ref(v___x_299_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 9, v___x_299_);
lean_ctor_set(v___x_296_, 8, v___x_299_);
v___x_301_ = v___x_296_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_lake_275_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_lean_276_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_elan_x3f_277_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_reservoirApiUrl_278_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_githashOverride_279_);
lean_ctor_set(v_reuseFailAlloc_303_, 5, v_pkgUrlMap_280_);
lean_ctor_set(v_reuseFailAlloc_303_, 6, v_enableArtifactCache_x3f_282_);
lean_ctor_set(v_reuseFailAlloc_303_, 7, v_restoreAllArtifacts_x3f_283_);
lean_ctor_set(v_reuseFailAlloc_303_, 8, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_303_, 9, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_303_, 10, v_lakeConfig_x3f_285_);
lean_ctor_set(v_reuseFailAlloc_303_, 11, v_cacheKey_x3f_286_);
lean_ctor_set(v_reuseFailAlloc_303_, 12, v_cacheArtifactEndpoint_x3f_287_);
lean_ctor_set(v_reuseFailAlloc_303_, 13, v_cacheRevisionEndpoint_x3f_288_);
lean_ctor_set(v_reuseFailAlloc_303_, 14, v_cacheService_x3f_289_);
lean_ctor_set(v_reuseFailAlloc_303_, 15, v_initLeanPath_290_);
lean_ctor_set(v_reuseFailAlloc_303_, 16, v_initLeanSrcPath_291_);
lean_ctor_set(v_reuseFailAlloc_303_, 17, v_initSharedLibPath_292_);
lean_ctor_set(v_reuseFailAlloc_303_, 18, v_initPath_293_);
lean_ctor_set(v_reuseFailAlloc_303_, 19, v_toolchain_294_);
lean_ctor_set_uint8(v_reuseFailAlloc_303_, sizeof(void*)*20, v_noCache_281_);
lean_ctor_set_uint8(v_reuseFailAlloc_303_, sizeof(void*)*20 + 1, v_noSystemCache_284_);
v___x_301_ = v_reuseFailAlloc_303_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; 
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
}
else
{
lean_object* v_lake_308_; lean_object* v_lean_309_; lean_object* v_elan_x3f_310_; lean_object* v_reservoirApiUrl_311_; lean_object* v_githashOverride_312_; lean_object* v_pkgUrlMap_313_; uint8_t v_noCache_314_; lean_object* v_enableArtifactCache_x3f_315_; lean_object* v_restoreAllArtifacts_x3f_316_; lean_object* v_lakeCache_x3f_317_; lean_object* v_lakeSystemCache_x3f_318_; lean_object* v_lakeConfig_x3f_319_; lean_object* v_cacheKey_x3f_320_; lean_object* v_cacheArtifactEndpoint_x3f_321_; lean_object* v_cacheRevisionEndpoint_x3f_322_; lean_object* v_cacheService_x3f_323_; lean_object* v_initLeanPath_324_; lean_object* v_initLeanSrcPath_325_; lean_object* v_initSharedLibPath_326_; lean_object* v_initPath_327_; lean_object* v_toolchain_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
lean_del_object(v___x_270_);
lean_dec(v_val_268_);
v_lake_308_ = lean_ctor_get(v_env_221_, 0);
v_lean_309_ = lean_ctor_get(v_env_221_, 1);
v_elan_x3f_310_ = lean_ctor_get(v_env_221_, 2);
v_reservoirApiUrl_311_ = lean_ctor_get(v_env_221_, 3);
v_githashOverride_312_ = lean_ctor_get(v_env_221_, 4);
v_pkgUrlMap_313_ = lean_ctor_get(v_env_221_, 5);
v_noCache_314_ = lean_ctor_get_uint8(v_env_221_, sizeof(void*)*20);
v_enableArtifactCache_x3f_315_ = lean_ctor_get(v_env_221_, 6);
v_restoreAllArtifacts_x3f_316_ = lean_ctor_get(v_env_221_, 7);
v_lakeCache_x3f_317_ = lean_ctor_get(v_env_221_, 8);
v_lakeSystemCache_x3f_318_ = lean_ctor_get(v_env_221_, 9);
v_lakeConfig_x3f_319_ = lean_ctor_get(v_env_221_, 10);
v_cacheKey_x3f_320_ = lean_ctor_get(v_env_221_, 11);
v_cacheArtifactEndpoint_x3f_321_ = lean_ctor_get(v_env_221_, 12);
v_cacheRevisionEndpoint_x3f_322_ = lean_ctor_get(v_env_221_, 13);
v_cacheService_x3f_323_ = lean_ctor_get(v_env_221_, 14);
v_initLeanPath_324_ = lean_ctor_get(v_env_221_, 15);
v_initLeanSrcPath_325_ = lean_ctor_get(v_env_221_, 16);
v_initSharedLibPath_326_ = lean_ctor_get(v_env_221_, 17);
v_initPath_327_ = lean_ctor_get(v_env_221_, 18);
v_toolchain_328_ = lean_ctor_get(v_env_221_, 19);
v_isSharedCheck_336_ = !lean_is_exclusive(v_env_221_);
if (v_isSharedCheck_336_ == 0)
{
v___x_330_ = v_env_221_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_toolchain_328_);
lean_inc(v_initPath_327_);
lean_inc(v_initSharedLibPath_326_);
lean_inc(v_initLeanSrcPath_325_);
lean_inc(v_initLeanPath_324_);
lean_inc(v_cacheService_x3f_323_);
lean_inc(v_cacheRevisionEndpoint_x3f_322_);
lean_inc(v_cacheArtifactEndpoint_x3f_321_);
lean_inc(v_cacheKey_x3f_320_);
lean_inc(v_lakeConfig_x3f_319_);
lean_inc(v_lakeSystemCache_x3f_318_);
lean_inc(v_lakeCache_x3f_317_);
lean_inc(v_restoreAllArtifacts_x3f_316_);
lean_inc(v_enableArtifactCache_x3f_315_);
lean_inc(v_pkgUrlMap_313_);
lean_inc(v_githashOverride_312_);
lean_inc(v_reservoirApiUrl_311_);
lean_inc(v_elan_x3f_310_);
lean_inc(v_lean_309_);
lean_inc(v_lake_308_);
lean_dec(v_env_221_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_lake_308_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_lean_309_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_elan_x3f_310_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v_reservoirApiUrl_311_);
lean_ctor_set(v_reuseFailAlloc_335_, 4, v_githashOverride_312_);
lean_ctor_set(v_reuseFailAlloc_335_, 5, v_pkgUrlMap_313_);
lean_ctor_set(v_reuseFailAlloc_335_, 6, v_enableArtifactCache_x3f_315_);
lean_ctor_set(v_reuseFailAlloc_335_, 7, v_restoreAllArtifacts_x3f_316_);
lean_ctor_set(v_reuseFailAlloc_335_, 8, v_lakeCache_x3f_317_);
lean_ctor_set(v_reuseFailAlloc_335_, 9, v_lakeSystemCache_x3f_318_);
lean_ctor_set(v_reuseFailAlloc_335_, 10, v_lakeConfig_x3f_319_);
lean_ctor_set(v_reuseFailAlloc_335_, 11, v_cacheKey_x3f_320_);
lean_ctor_set(v_reuseFailAlloc_335_, 12, v_cacheArtifactEndpoint_x3f_321_);
lean_ctor_set(v_reuseFailAlloc_335_, 13, v_cacheRevisionEndpoint_x3f_322_);
lean_ctor_set(v_reuseFailAlloc_335_, 14, v_cacheService_x3f_323_);
lean_ctor_set(v_reuseFailAlloc_335_, 15, v_initLeanPath_324_);
lean_ctor_set(v_reuseFailAlloc_335_, 16, v_initLeanSrcPath_325_);
lean_ctor_set(v_reuseFailAlloc_335_, 17, v_initSharedLibPath_326_);
lean_ctor_set(v_reuseFailAlloc_335_, 18, v_initPath_327_);
lean_ctor_set(v_reuseFailAlloc_335_, 19, v_toolchain_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_335_, sizeof(void*)*20, v_noCache_314_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*20 + 1, v___x_274_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
}
}
}
else
{
lean_dec(v___x_224_);
if (lean_obj_tag(v_elan_x3f_218_) == 0)
{
goto v___jp_225_;
}
else
{
lean_object* v_val_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_393_; 
v_val_338_ = lean_ctor_get(v_elan_x3f_218_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v_elan_x3f_218_);
if (v_isSharedCheck_393_ == 0)
{
v___x_340_ = v_elan_x3f_218_;
v_isShared_341_ = v_isSharedCheck_393_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_val_338_);
lean_dec(v_elan_x3f_218_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_393_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = lean_string_utf8_byte_size(v_toolchain_220_);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_nat_dec_eq(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_338_, v_toolchain_220_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_345_);
v___x_347_ = v___x_340_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_392_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_348_; lean_object* v___y_350_; 
v___x_348_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_219_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v___x_381_; 
v___x_381_ = lean_box(0);
v___y_350_ = v___x_381_;
goto v___jp_349_;
}
else
{
lean_object* v_val_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_391_; 
v_val_382_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_391_ == 0)
{
v___x_384_ = v___x_348_;
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_val_382_);
lean_dec(v___x_348_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_386_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_387_ = l_System_FilePath_join(v_val_382_, v___x_386_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_387_);
v___x_389_ = v___x_384_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
v___y_350_ = v___x_389_;
goto v___jp_349_;
}
}
}
v___jp_349_:
{
lean_object* v_lake_351_; lean_object* v_lean_352_; lean_object* v_elan_x3f_353_; lean_object* v_reservoirApiUrl_354_; lean_object* v_githashOverride_355_; lean_object* v_pkgUrlMap_356_; uint8_t v_noCache_357_; lean_object* v_enableArtifactCache_x3f_358_; lean_object* v_restoreAllArtifacts_x3f_359_; uint8_t v_noSystemCache_360_; lean_object* v_lakeConfig_x3f_361_; lean_object* v_cacheKey_x3f_362_; lean_object* v_cacheArtifactEndpoint_x3f_363_; lean_object* v_cacheRevisionEndpoint_x3f_364_; lean_object* v_cacheService_x3f_365_; lean_object* v_initLeanPath_366_; lean_object* v_initLeanSrcPath_367_; lean_object* v_initSharedLibPath_368_; lean_object* v_initPath_369_; lean_object* v_toolchain_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
v_lake_351_ = lean_ctor_get(v_env_221_, 0);
v_lean_352_ = lean_ctor_get(v_env_221_, 1);
v_elan_x3f_353_ = lean_ctor_get(v_env_221_, 2);
v_reservoirApiUrl_354_ = lean_ctor_get(v_env_221_, 3);
v_githashOverride_355_ = lean_ctor_get(v_env_221_, 4);
v_pkgUrlMap_356_ = lean_ctor_get(v_env_221_, 5);
v_noCache_357_ = lean_ctor_get_uint8(v_env_221_, sizeof(void*)*20);
v_enableArtifactCache_x3f_358_ = lean_ctor_get(v_env_221_, 6);
v_restoreAllArtifacts_x3f_359_ = lean_ctor_get(v_env_221_, 7);
v_noSystemCache_360_ = lean_ctor_get_uint8(v_env_221_, sizeof(void*)*20 + 1);
v_lakeConfig_x3f_361_ = lean_ctor_get(v_env_221_, 10);
v_cacheKey_x3f_362_ = lean_ctor_get(v_env_221_, 11);
v_cacheArtifactEndpoint_x3f_363_ = lean_ctor_get(v_env_221_, 12);
v_cacheRevisionEndpoint_x3f_364_ = lean_ctor_get(v_env_221_, 13);
v_cacheService_x3f_365_ = lean_ctor_get(v_env_221_, 14);
v_initLeanPath_366_ = lean_ctor_get(v_env_221_, 15);
v_initLeanSrcPath_367_ = lean_ctor_get(v_env_221_, 16);
v_initSharedLibPath_368_ = lean_ctor_get(v_env_221_, 17);
v_initPath_369_ = lean_ctor_get(v_env_221_, 18);
v_toolchain_370_ = lean_ctor_get(v_env_221_, 19);
v_isSharedCheck_378_ = !lean_is_exclusive(v_env_221_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; lean_object* v_unused_380_; 
v_unused_379_ = lean_ctor_get(v_env_221_, 9);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_env_221_, 8);
lean_dec(v_unused_380_);
v___x_372_ = v_env_221_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_toolchain_370_);
lean_inc(v_initPath_369_);
lean_inc(v_initSharedLibPath_368_);
lean_inc(v_initLeanSrcPath_367_);
lean_inc(v_initLeanPath_366_);
lean_inc(v_cacheService_x3f_365_);
lean_inc(v_cacheRevisionEndpoint_x3f_364_);
lean_inc(v_cacheArtifactEndpoint_x3f_363_);
lean_inc(v_cacheKey_x3f_362_);
lean_inc(v_lakeConfig_x3f_361_);
lean_inc(v_restoreAllArtifacts_x3f_359_);
lean_inc(v_enableArtifactCache_x3f_358_);
lean_inc(v_pkgUrlMap_356_);
lean_inc(v_githashOverride_355_);
lean_inc(v_reservoirApiUrl_354_);
lean_inc(v_elan_x3f_353_);
lean_inc(v_lean_352_);
lean_inc(v_lake_351_);
lean_dec(v_env_221_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 9, v___y_350_);
lean_ctor_set(v___x_372_, 8, v___x_347_);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_lake_351_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_lean_352_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_elan_x3f_353_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v_reservoirApiUrl_354_);
lean_ctor_set(v_reuseFailAlloc_377_, 4, v_githashOverride_355_);
lean_ctor_set(v_reuseFailAlloc_377_, 5, v_pkgUrlMap_356_);
lean_ctor_set(v_reuseFailAlloc_377_, 6, v_enableArtifactCache_x3f_358_);
lean_ctor_set(v_reuseFailAlloc_377_, 7, v_restoreAllArtifacts_x3f_359_);
lean_ctor_set(v_reuseFailAlloc_377_, 8, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_377_, 9, v___y_350_);
lean_ctor_set(v_reuseFailAlloc_377_, 10, v_lakeConfig_x3f_361_);
lean_ctor_set(v_reuseFailAlloc_377_, 11, v_cacheKey_x3f_362_);
lean_ctor_set(v_reuseFailAlloc_377_, 12, v_cacheArtifactEndpoint_x3f_363_);
lean_ctor_set(v_reuseFailAlloc_377_, 13, v_cacheRevisionEndpoint_x3f_364_);
lean_ctor_set(v_reuseFailAlloc_377_, 14, v_cacheService_x3f_365_);
lean_ctor_set(v_reuseFailAlloc_377_, 15, v_initLeanPath_366_);
lean_ctor_set(v_reuseFailAlloc_377_, 16, v_initLeanSrcPath_367_);
lean_ctor_set(v_reuseFailAlloc_377_, 17, v_initSharedLibPath_368_);
lean_ctor_set(v_reuseFailAlloc_377_, 18, v_initPath_369_);
lean_ctor_set(v_reuseFailAlloc_377_, 19, v_toolchain_370_);
lean_ctor_set_uint8(v_reuseFailAlloc_377_, sizeof(void*)*20, v_noCache_357_);
lean_ctor_set_uint8(v_reuseFailAlloc_377_, sizeof(void*)*20 + 1, v_noSystemCache_360_);
v___x_375_ = v_reuseFailAlloc_377_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
}
}
}
else
{
lean_del_object(v___x_340_);
lean_dec(v_val_338_);
goto v___jp_225_;
}
}
}
}
v___jp_225_:
{
lean_object* v___x_226_; 
v___x_226_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_219_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v_env_221_);
return v___x_227_;
}
else
{
lean_object* v_val_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_267_; 
v_val_228_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_267_ == 0)
{
v___x_230_ = v___x_226_;
v_isShared_231_ = v_isSharedCheck_267_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_val_228_);
lean_dec(v___x_226_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_267_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_lake_232_; lean_object* v_lean_233_; lean_object* v_elan_x3f_234_; lean_object* v_reservoirApiUrl_235_; lean_object* v_githashOverride_236_; lean_object* v_pkgUrlMap_237_; uint8_t v_noCache_238_; lean_object* v_enableArtifactCache_x3f_239_; lean_object* v_restoreAllArtifacts_x3f_240_; uint8_t v_noSystemCache_241_; lean_object* v_lakeConfig_x3f_242_; lean_object* v_cacheKey_x3f_243_; lean_object* v_cacheArtifactEndpoint_x3f_244_; lean_object* v_cacheRevisionEndpoint_x3f_245_; lean_object* v_cacheService_x3f_246_; lean_object* v_initLeanPath_247_; lean_object* v_initLeanSrcPath_248_; lean_object* v_initSharedLibPath_249_; lean_object* v_initPath_250_; lean_object* v_toolchain_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_264_; 
v_lake_232_ = lean_ctor_get(v_env_221_, 0);
v_lean_233_ = lean_ctor_get(v_env_221_, 1);
v_elan_x3f_234_ = lean_ctor_get(v_env_221_, 2);
v_reservoirApiUrl_235_ = lean_ctor_get(v_env_221_, 3);
v_githashOverride_236_ = lean_ctor_get(v_env_221_, 4);
v_pkgUrlMap_237_ = lean_ctor_get(v_env_221_, 5);
v_noCache_238_ = lean_ctor_get_uint8(v_env_221_, sizeof(void*)*20);
v_enableArtifactCache_x3f_239_ = lean_ctor_get(v_env_221_, 6);
v_restoreAllArtifacts_x3f_240_ = lean_ctor_get(v_env_221_, 7);
v_noSystemCache_241_ = lean_ctor_get_uint8(v_env_221_, sizeof(void*)*20 + 1);
v_lakeConfig_x3f_242_ = lean_ctor_get(v_env_221_, 10);
v_cacheKey_x3f_243_ = lean_ctor_get(v_env_221_, 11);
v_cacheArtifactEndpoint_x3f_244_ = lean_ctor_get(v_env_221_, 12);
v_cacheRevisionEndpoint_x3f_245_ = lean_ctor_get(v_env_221_, 13);
v_cacheService_x3f_246_ = lean_ctor_get(v_env_221_, 14);
v_initLeanPath_247_ = lean_ctor_get(v_env_221_, 15);
v_initLeanSrcPath_248_ = lean_ctor_get(v_env_221_, 16);
v_initSharedLibPath_249_ = lean_ctor_get(v_env_221_, 17);
v_initPath_250_ = lean_ctor_get(v_env_221_, 18);
v_toolchain_251_ = lean_ctor_get(v_env_221_, 19);
v_isSharedCheck_264_ = !lean_is_exclusive(v_env_221_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; lean_object* v_unused_266_; 
v_unused_265_ = lean_ctor_get(v_env_221_, 9);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_env_221_, 8);
lean_dec(v_unused_266_);
v___x_253_ = v_env_221_;
v_isShared_254_ = v_isSharedCheck_264_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_toolchain_251_);
lean_inc(v_initPath_250_);
lean_inc(v_initSharedLibPath_249_);
lean_inc(v_initLeanSrcPath_248_);
lean_inc(v_initLeanPath_247_);
lean_inc(v_cacheService_x3f_246_);
lean_inc(v_cacheRevisionEndpoint_x3f_245_);
lean_inc(v_cacheArtifactEndpoint_x3f_244_);
lean_inc(v_cacheKey_x3f_243_);
lean_inc(v_lakeConfig_x3f_242_);
lean_inc(v_restoreAllArtifacts_x3f_240_);
lean_inc(v_enableArtifactCache_x3f_239_);
lean_inc(v_pkgUrlMap_237_);
lean_inc(v_githashOverride_236_);
lean_inc(v_reservoirApiUrl_235_);
lean_inc(v_elan_x3f_234_);
lean_inc(v_lean_233_);
lean_inc(v_lake_232_);
lean_dec(v_env_221_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_264_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_255_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_256_ = l_System_FilePath_join(v_val_228_, v___x_255_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_256_);
v___x_258_ = v___x_230_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_263_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
lean_inc_ref(v___x_258_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 9, v___x_258_);
lean_ctor_set(v___x_253_, 8, v___x_258_);
v___x_260_ = v___x_253_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_lake_232_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_lean_233_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_elan_x3f_234_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_reservoirApiUrl_235_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_githashOverride_236_);
lean_ctor_set(v_reuseFailAlloc_262_, 5, v_pkgUrlMap_237_);
lean_ctor_set(v_reuseFailAlloc_262_, 6, v_enableArtifactCache_x3f_239_);
lean_ctor_set(v_reuseFailAlloc_262_, 7, v_restoreAllArtifacts_x3f_240_);
lean_ctor_set(v_reuseFailAlloc_262_, 8, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_262_, 9, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_262_, 10, v_lakeConfig_x3f_242_);
lean_ctor_set(v_reuseFailAlloc_262_, 11, v_cacheKey_x3f_243_);
lean_ctor_set(v_reuseFailAlloc_262_, 12, v_cacheArtifactEndpoint_x3f_244_);
lean_ctor_set(v_reuseFailAlloc_262_, 13, v_cacheRevisionEndpoint_x3f_245_);
lean_ctor_set(v_reuseFailAlloc_262_, 14, v_cacheService_x3f_246_);
lean_ctor_set(v_reuseFailAlloc_262_, 15, v_initLeanPath_247_);
lean_ctor_set(v_reuseFailAlloc_262_, 16, v_initLeanSrcPath_248_);
lean_ctor_set(v_reuseFailAlloc_262_, 17, v_initSharedLibPath_249_);
lean_ctor_set(v_reuseFailAlloc_262_, 18, v_initPath_250_);
lean_ctor_set(v_reuseFailAlloc_262_, 19, v_toolchain_251_);
lean_ctor_set_uint8(v_reuseFailAlloc_262_, sizeof(void*)*20, v_noCache_238_);
lean_ctor_set_uint8(v_reuseFailAlloc_262_, sizeof(void*)*20 + 1, v_noSystemCache_241_);
v___x_260_ = v_reuseFailAlloc_262_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; 
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs_0interp(lean_interpreter_value* stack)
{
lean_object* v_elan_x3f_218_ = stack[0].m_obj;
lean_object* v_userHome_x3f_219_ = stack[1].m_obj;
lean_object* v_toolchain_220_ = stack[2].m_obj;
lean_object* v_env_221_ = stack[3].m_obj;
lean_object* v_res_394_;
v_res_394_ = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(v_elan_x3f_218_, v_userHome_x3f_219_, v_toolchain_220_, v_env_221_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs___boxed(lean_object* v_elan_x3f_395_, lean_object* v_userHome_x3f_396_, lean_object* v_toolchain_397_, lean_object* v_env_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(v_elan_x3f_395_, v_userHome_x3f_396_, v_toolchain_397_, v_env_398_);
lean_dec_ref(v_toolchain_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(lean_object* v_init_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_object* v_k_406_; lean_object* v_v_407_; lean_object* v_l_408_; lean_object* v_r_409_; lean_object* v___x_410_; 
v_k_406_ = lean_ctor_get(v_x_405_, 1);
lean_inc(v_k_406_);
v_v_407_ = lean_ctor_get(v_x_405_, 2);
lean_inc(v_v_407_);
v_l_408_ = lean_ctor_get(v_x_405_, 3);
lean_inc(v_l_408_);
v_r_409_ = lean_ctor_get(v_x_405_, 4);
lean_inc(v_r_409_);
lean_dec_ref_known(v_x_405_, 5);
v___x_410_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(v_init_404_, v_l_408_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_dec(v_r_409_);
lean_dec(v_v_407_);
lean_dec(v_k_406_);
return v___x_410_;
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_451_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_451_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_451_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_451_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0));
v___x_416_ = lean_string_dec_eq(v_k_406_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v_n_417_; uint8_t v___x_418_; 
lean_inc(v_k_406_);
v_n_417_ = l_String_toName(v_k_406_);
v___x_418_ = l_Lean_Name_isAnonymous(v_n_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_del_object(v___x_413_);
lean_dec(v_k_406_);
v___x_419_ = l_Lean_Json_getStr_x3f(v_v_407_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v_n_417_);
lean_dec(v_a_411_);
lean_dec(v_r_409_);
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
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
lean_object* v_a_428_; lean_object* v___x_429_; 
v_a_428_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_419_, 1);
v___x_429_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_417_, v_a_428_, v_a_411_);
v_init_404_ = v___x_429_;
v_x_405_ = v_r_409_;
goto _start;
}
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
lean_dec(v_n_417_);
lean_dec(v_a_411_);
lean_dec(v_r_409_);
lean_dec(v_v_407_);
v___x_431_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1));
v___x_432_ = lean_string_append(v___x_431_, v_k_406_);
lean_dec(v_k_406_);
v___x_433_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
v___x_434_ = lean_string_append(v___x_432_, v___x_433_);
if (v_isShared_414_ == 0)
{
lean_ctor_set_tag(v___x_413_, 0);
lean_ctor_set(v___x_413_, 0, v___x_434_);
v___x_436_ = v___x_413_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_object* v___x_438_; 
lean_del_object(v___x_413_);
lean_dec(v_k_406_);
v___x_438_ = l_Lean_Json_getStr_x3f(v_v_407_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_a_411_);
lean_dec(v_r_409_);
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_a_447_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_438_, 1);
v___x_448_ = lean_box(0);
v___x_449_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_448_, v_a_447_, v_a_411_);
v_init_404_ = v___x_449_;
v_x_405_ = v_r_409_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_452_; 
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v_init_404_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_454_) == 5)
{
lean_object* v_kvPairs_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_kvPairs_455_ = lean_ctor_get(v_x_454_, 0);
lean_inc(v_kvPairs_455_);
lean_dec_ref_known(v_x_454_, 1);
v___x_456_ = lean_box(1);
v___x_457_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(v___x_456_, v_kvPairs_455_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_458_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0));
v___x_459_ = lean_unsigned_to_nat(80u);
v___x_460_ = l_Lean_Json_pretty(v_x_454_, v___x_459_);
v___x_461_ = lean_string_append(v___x_458_, v___x_460_);
lean_dec_ref(v___x_460_);
v___x_462_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
v___x_463_ = lean_string_append(v___x_461_, v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
}
lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap(){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_a_471_; 
v___x_468_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0));
v___x_469_ = lean_io_getenv(v___x_468_);
if (lean_obj_tag(v___x_469_) == 1)
{
lean_object* v_val_475_; lean_object* v___x_476_; 
v_val_475_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v___x_469_, 1);
v___x_476_ = l_Lean_Json_parse(v_val_475_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 1);
v_a_471_ = v_a_477_;
goto v___jp_470_;
}
else
{
lean_object* v_a_478_; lean_object* v___x_479_; 
v_a_478_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_476_, 1);
v___x_479_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(v_a_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v_a_471_ = v_a_480_;
goto v___jp_470_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
v_a_481_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_479_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 0);
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v___x_469_);
v___x_489_ = lean_box(1);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
v___jp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1));
v___x_473_ = lean_string_append(v___x_472_, v_a_471_);
lean_dec_ref(v_a_471_);
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
}
LEAN_EXPORT void l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_491_;
v_res_491_ = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___boxed(lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(lean_object* v_url_494_){
_start:
{
uint32_t v___y_496_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_string_utf8_byte_size(v_url_494_);
lean_inc_ref(v_url_494_);
v___x_509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_509_, 0, v_url_494_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
lean_ctor_set(v___x_509_, 2, v___x_508_);
v___x_510_ = l_String_Slice_Pos_prev_x3f(v___x_509_, v___x_508_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_dec_ref_known(v___x_509_, 3);
goto v___jp_505_;
}
else
{
lean_object* v_val_511_; lean_object* v___x_512_; 
v_val_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = l_String_Slice_Pos_get_x3f(v___x_509_, v_val_511_);
lean_dec(v_val_511_);
lean_dec_ref_known(v___x_509_, 3);
if (lean_obj_tag(v___x_512_) == 0)
{
goto v___jp_505_;
}
else
{
lean_object* v_val_513_; uint32_t v___x_514_; 
v_val_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v___x_512_, 1);
v___x_514_ = lean_unbox_uint32(v_val_513_);
lean_dec(v_val_513_);
v___y_496_ = v___x_514_;
goto v___jp_495_;
}
}
v___jp_495_:
{
uint32_t v___x_497_; uint8_t v___x_498_; 
v___x_497_ = 47;
v___x_498_ = lean_uint32_dec_eq(v___y_496_, v___x_497_);
if (v___x_498_ == 0)
{
return v_url_494_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_string_utf8_byte_size(v_url_494_);
lean_inc_ref(v_url_494_);
v___x_502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_502_, 0, v_url_494_);
lean_ctor_set(v___x_502_, 1, v___x_500_);
lean_ctor_set(v___x_502_, 2, v___x_501_);
v___x_503_ = l_String_Slice_Pos_prevn(v___x_502_, v___x_501_, v___x_499_);
lean_dec_ref_known(v___x_502_, 3);
v___x_504_ = lean_string_utf8_extract_fast(v_url_494_, v___x_500_, v___x_503_);
lean_dec(v___x_503_);
lean_dec_ref(v_url_494_);
return v___x_504_;
}
}
v___jp_505_:
{
uint32_t v___x_506_; 
v___x_506_ = 65;
v___y_496_ = v___x_506_;
goto v___jp_495_;
}
}
}
lean_object* l_Lake_Env_compute(lean_object* v_lake_533_, lean_object* v_lean_534_, lean_object* v_elan_x3f_535_, lean_object* v_noCache_536_){
_start:
{
lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; uint8_t v___y_552_; lean_object* v___y_553_; uint8_t v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; uint8_t v___y_574_; lean_object* v___y_575_; uint8_t v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; uint8_t v___y_612_; lean_object* v___y_613_; uint8_t v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; uint8_t v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; uint8_t v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; uint8_t v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; uint8_t v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; uint8_t v___y_708_; lean_object* v___y_709_; lean_object* v_val_710_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; uint8_t v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; uint8_t v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; uint8_t v___y_776_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v_a_826_; lean_object* v_a_856_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lake_Env_compute___closed__16));
v___x_876_ = lean_io_getenv(v___x_875_);
if (lean_obj_tag(v___x_876_) == 1)
{
lean_object* v_val_877_; lean_object* v___x_878_; 
v_val_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_val_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_877_);
v_a_856_ = v___x_878_;
goto v___jp_855_;
}
else
{
lean_object* v___x_879_; 
lean_dec(v___x_876_);
v___x_879_ = ((lean_object*)(l_Lake_Env_compute___closed__17));
v_a_856_ = v___x_879_;
goto v___jp_855_;
}
v___jp_538_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_inc_ref(v___y_549_);
lean_inc_n(v___y_553_, 2);
lean_inc(v_elan_x3f_535_);
v___x_558_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v___x_558_, 0, v_lake_533_);
lean_ctor_set(v___x_558_, 1, v_lean_534_);
lean_ctor_set(v___x_558_, 2, v_elan_x3f_535_);
lean_ctor_set(v___x_558_, 3, v___y_547_);
lean_ctor_set(v___x_558_, 4, v___y_542_);
lean_ctor_set(v___x_558_, 5, v___y_539_);
lean_ctor_set(v___x_558_, 6, v___y_541_);
lean_ctor_set(v___x_558_, 7, v___y_540_);
lean_ctor_set(v___x_558_, 8, v___y_553_);
lean_ctor_set(v___x_558_, 9, v___y_553_);
lean_ctor_set(v___x_558_, 10, v___y_545_);
lean_ctor_set(v___x_558_, 11, v___y_548_);
lean_ctor_set(v___x_558_, 12, v___y_555_);
lean_ctor_set(v___x_558_, 13, v___y_543_);
lean_ctor_set(v___x_558_, 14, v___y_557_);
lean_ctor_set(v___x_558_, 15, v___y_550_);
lean_ctor_set(v___x_558_, 16, v___y_551_);
lean_ctor_set(v___x_558_, 17, v___y_556_);
lean_ctor_set(v___x_558_, 18, v___y_544_);
lean_ctor_set(v___x_558_, 19, v___y_549_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*20, v___y_554_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*20 + 1, v___y_552_);
v___x_559_ = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(v_elan_x3f_535_, v___y_546_, v___y_549_, v___x_558_);
lean_dec_ref(v___y_549_);
return v___x_559_;
}
v___jp_560_:
{
if (lean_obj_tag(v___y_565_) == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_box(0);
v___y_539_ = v___y_561_;
v___y_540_ = v___y_562_;
v___y_541_ = v___y_563_;
v___y_542_ = v___y_564_;
v___y_543_ = v___y_579_;
v___y_544_ = v___y_566_;
v___y_545_ = v___y_567_;
v___y_546_ = v___y_568_;
v___y_547_ = v___y_569_;
v___y_548_ = v___y_570_;
v___y_549_ = v___y_571_;
v___y_550_ = v___y_572_;
v___y_551_ = v___y_573_;
v___y_552_ = v___y_574_;
v___y_553_ = v___y_575_;
v___y_554_ = v___y_576_;
v___y_555_ = v___y_577_;
v___y_556_ = v___y_578_;
v___y_557_ = v___x_580_;
goto v___jp_538_;
}
else
{
lean_object* v_val_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_596_; 
v_val_581_ = lean_ctor_get(v___y_565_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___y_565_);
if (v_isSharedCheck_596_ == 0)
{
v___x_583_ = v___y_565_;
v_isShared_584_ = v_isSharedCheck_596_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_val_581_);
lean_dec(v___y_565_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_596_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_str_589_; lean_object* v_startInclusive_590_; lean_object* v_endExclusive_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_string_utf8_byte_size(v_val_581_);
v___x_587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_587_, 0, v_val_581_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
lean_ctor_set(v___x_587_, 2, v___x_586_);
v___x_588_ = l_String_Slice_trimAscii(v___x_587_);
v_str_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc_ref(v_str_589_);
v_startInclusive_590_ = lean_ctor_get(v___x_588_, 1);
lean_inc(v_startInclusive_590_);
v_endExclusive_591_ = lean_ctor_get(v___x_588_, 2);
lean_inc(v_endExclusive_591_);
lean_dec_ref(v___x_588_);
v___x_592_ = lean_string_utf8_extract_fast(v_str_589_, v_startInclusive_590_, v_endExclusive_591_);
lean_dec(v_endExclusive_591_);
lean_dec(v_startInclusive_590_);
lean_dec_ref(v_str_589_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_592_);
v___x_594_ = v___x_583_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
v___y_539_ = v___y_561_;
v___y_540_ = v___y_562_;
v___y_541_ = v___y_563_;
v___y_542_ = v___y_564_;
v___y_543_ = v___y_579_;
v___y_544_ = v___y_566_;
v___y_545_ = v___y_567_;
v___y_546_ = v___y_568_;
v___y_547_ = v___y_569_;
v___y_548_ = v___y_570_;
v___y_549_ = v___y_571_;
v___y_550_ = v___y_572_;
v___y_551_ = v___y_573_;
v___y_552_ = v___y_574_;
v___y_553_ = v___y_575_;
v___y_554_ = v___y_576_;
v___y_555_ = v___y_577_;
v___y_556_ = v___y_578_;
v___y_557_ = v___x_594_;
goto v___jp_538_;
}
}
}
}
v___jp_597_:
{
if (lean_obj_tag(v___y_603_) == 0)
{
v___y_561_ = v___y_598_;
v___y_562_ = v___y_599_;
v___y_563_ = v___y_600_;
v___y_564_ = v___y_601_;
v___y_565_ = v___y_602_;
v___y_566_ = v___y_604_;
v___y_567_ = v___y_605_;
v___y_568_ = v___y_606_;
v___y_569_ = v___y_607_;
v___y_570_ = v___y_608_;
v___y_571_ = v___y_609_;
v___y_572_ = v___y_610_;
v___y_573_ = v___y_611_;
v___y_574_ = v___y_612_;
v___y_575_ = v___y_613_;
v___y_576_ = v___y_614_;
v___y_577_ = v___y_616_;
v___y_578_ = v___y_615_;
v___y_579_ = v___y_603_;
goto v___jp_560_;
}
else
{
lean_object* v_val_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_625_; 
v_val_617_ = lean_ctor_get(v___y_603_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___y_603_);
if (v_isSharedCheck_625_ == 0)
{
v___x_619_ = v___y_603_;
v_isShared_620_ = v_isSharedCheck_625_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_val_617_);
lean_dec(v___y_603_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_625_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_621_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_617_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_621_);
v___x_623_ = v___x_619_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
v___y_561_ = v___y_598_;
v___y_562_ = v___y_599_;
v___y_563_ = v___y_600_;
v___y_564_ = v___y_601_;
v___y_565_ = v___y_602_;
v___y_566_ = v___y_604_;
v___y_567_ = v___y_605_;
v___y_568_ = v___y_606_;
v___y_569_ = v___y_607_;
v___y_570_ = v___y_608_;
v___y_571_ = v___y_609_;
v___y_572_ = v___y_610_;
v___y_573_ = v___y_611_;
v___y_574_ = v___y_612_;
v___y_575_ = v___y_613_;
v___y_576_ = v___y_614_;
v___y_577_ = v___y_616_;
v___y_578_ = v___y_615_;
v___y_579_ = v___x_623_;
goto v___jp_560_;
}
}
}
}
v___jp_626_:
{
if (lean_obj_tag(v___y_641_) == 0)
{
v___y_598_ = v___y_627_;
v___y_599_ = v___y_628_;
v___y_600_ = v___y_629_;
v___y_601_ = v___y_630_;
v___y_602_ = v___y_631_;
v___y_603_ = v___y_632_;
v___y_604_ = v___y_633_;
v___y_605_ = v___y_634_;
v___y_606_ = v___y_635_;
v___y_607_ = v___y_636_;
v___y_608_ = v___y_645_;
v___y_609_ = v___y_637_;
v___y_610_ = v___y_638_;
v___y_611_ = v___y_639_;
v___y_612_ = v___y_640_;
v___y_613_ = v___y_642_;
v___y_614_ = v___y_643_;
v___y_615_ = v___y_644_;
v___y_616_ = v___y_641_;
goto v___jp_597_;
}
else
{
lean_object* v_val_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_val_646_ = lean_ctor_get(v___y_641_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___y_641_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v___y_641_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_val_646_);
lean_dec(v___y_641_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
v___y_598_ = v___y_627_;
v___y_599_ = v___y_628_;
v___y_600_ = v___y_629_;
v___y_601_ = v___y_630_;
v___y_602_ = v___y_631_;
v___y_603_ = v___y_632_;
v___y_604_ = v___y_633_;
v___y_605_ = v___y_634_;
v___y_606_ = v___y_635_;
v___y_607_ = v___y_636_;
v___y_608_ = v___y_645_;
v___y_609_ = v___y_637_;
v___y_610_ = v___y_638_;
v___y_611_ = v___y_639_;
v___y_612_ = v___y_640_;
v___y_613_ = v___y_642_;
v___y_614_ = v___y_643_;
v___y_615_ = v___y_644_;
v___y_616_ = v___x_652_;
goto v___jp_597_;
}
}
}
}
v___jp_655_:
{
if (lean_obj_tag(v___y_657_) == 0)
{
v___y_627_ = v___y_656_;
v___y_628_ = v___y_658_;
v___y_629_ = v___y_659_;
v___y_630_ = v___y_660_;
v___y_631_ = v___y_661_;
v___y_632_ = v___y_662_;
v___y_633_ = v___y_663_;
v___y_634_ = v___y_674_;
v___y_635_ = v___y_664_;
v___y_636_ = v___y_665_;
v___y_637_ = v___y_666_;
v___y_638_ = v___y_667_;
v___y_639_ = v___y_668_;
v___y_640_ = v___y_669_;
v___y_641_ = v___y_670_;
v___y_642_ = v___y_671_;
v___y_643_ = v___y_672_;
v___y_644_ = v___y_673_;
v___y_645_ = v___y_657_;
goto v___jp_626_;
}
else
{
lean_object* v_val_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_690_; 
v_val_675_ = lean_ctor_get(v___y_657_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___y_657_);
if (v_isSharedCheck_690_ == 0)
{
v___x_677_ = v___y_657_;
v_isShared_678_ = v_isSharedCheck_690_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_val_675_);
lean_dec(v___y_657_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_690_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_str_683_; lean_object* v_startInclusive_684_; lean_object* v_endExclusive_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_string_utf8_byte_size(v_val_675_);
v___x_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_681_, 0, v_val_675_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
lean_ctor_set(v___x_681_, 2, v___x_680_);
v___x_682_ = l_String_Slice_trimAscii(v___x_681_);
v_str_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc_ref(v_str_683_);
v_startInclusive_684_ = lean_ctor_get(v___x_682_, 1);
lean_inc(v_startInclusive_684_);
v_endExclusive_685_ = lean_ctor_get(v___x_682_, 2);
lean_inc(v_endExclusive_685_);
lean_dec_ref(v___x_682_);
v___x_686_ = lean_string_utf8_extract_fast(v_str_683_, v_startInclusive_684_, v_endExclusive_685_);
lean_dec(v_endExclusive_685_);
lean_dec(v_startInclusive_684_);
lean_dec_ref(v_str_683_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_686_);
v___x_688_ = v___x_677_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v___y_627_ = v___y_656_;
v___y_628_ = v___y_658_;
v___y_629_ = v___y_659_;
v___y_630_ = v___y_660_;
v___y_631_ = v___y_661_;
v___y_632_ = v___y_662_;
v___y_633_ = v___y_663_;
v___y_634_ = v___y_674_;
v___y_635_ = v___y_664_;
v___y_636_ = v___y_665_;
v___y_637_ = v___y_666_;
v___y_638_ = v___y_667_;
v___y_639_ = v___y_668_;
v___y_640_ = v___y_669_;
v___y_641_ = v___y_670_;
v___y_642_ = v___y_671_;
v___y_643_ = v___y_672_;
v___y_644_ = v___y_673_;
v___y_645_ = v___x_688_;
goto v___jp_626_;
}
}
}
}
v___jp_691_:
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v_val_710_);
v___y_656_ = v___y_692_;
v___y_657_ = v___y_693_;
v___y_658_ = v___y_694_;
v___y_659_ = v___y_695_;
v___y_660_ = v___y_696_;
v___y_661_ = v___y_697_;
v___y_662_ = v___y_698_;
v___y_663_ = v___y_699_;
v___y_664_ = v___y_700_;
v___y_665_ = v___y_701_;
v___y_666_ = v___y_702_;
v___y_667_ = v___y_703_;
v___y_668_ = v___y_704_;
v___y_669_ = v___y_705_;
v___y_670_ = v___y_706_;
v___y_671_ = v___y_707_;
v___y_672_ = v___y_708_;
v___y_673_ = v___y_709_;
v___y_674_ = v___x_711_;
goto v___jp_655_;
}
v___jp_712_:
{
uint8_t v___x_730_; lean_object* v___x_731_; 
v___x_730_ = 0;
v___x_731_ = lean_box(0);
if (lean_obj_tag(v___y_725_) == 0)
{
if (lean_obj_tag(v___y_720_) == 0)
{
v___y_656_ = v___y_713_;
v___y_657_ = v___y_714_;
v___y_658_ = v___y_729_;
v___y_659_ = v___y_715_;
v___y_660_ = v___y_716_;
v___y_661_ = v___y_717_;
v___y_662_ = v___y_718_;
v___y_663_ = v___y_719_;
v___y_664_ = v___y_720_;
v___y_665_ = v___y_721_;
v___y_666_ = v___y_722_;
v___y_667_ = v___y_723_;
v___y_668_ = v___y_724_;
v___y_669_ = v___x_730_;
v___y_670_ = v___y_726_;
v___y_671_ = v___x_731_;
v___y_672_ = v___y_727_;
v___y_673_ = v___y_728_;
v___y_674_ = v___y_720_;
goto v___jp_655_;
}
else
{
lean_object* v_val_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_val_732_ = lean_ctor_get(v___y_720_, 0);
v___x_733_ = ((lean_object*)(l_Lake_Env_compute___closed__0));
lean_inc(v_val_732_);
v___x_734_ = l_System_FilePath_join(v_val_732_, v___x_733_);
v___x_735_ = ((lean_object*)(l_Lake_Env_compute___closed__1));
v___x_736_ = l_System_FilePath_join(v___x_734_, v___x_735_);
v___y_692_ = v___y_713_;
v___y_693_ = v___y_714_;
v___y_694_ = v___y_729_;
v___y_695_ = v___y_715_;
v___y_696_ = v___y_716_;
v___y_697_ = v___y_717_;
v___y_698_ = v___y_718_;
v___y_699_ = v___y_719_;
v___y_700_ = v___y_720_;
v___y_701_ = v___y_721_;
v___y_702_ = v___y_722_;
v___y_703_ = v___y_723_;
v___y_704_ = v___y_724_;
v___y_705_ = v___x_730_;
v___y_706_ = v___y_726_;
v___y_707_ = v___x_731_;
v___y_708_ = v___y_727_;
v___y_709_ = v___y_728_;
v_val_710_ = v___x_736_;
goto v___jp_691_;
}
}
else
{
lean_object* v_val_737_; 
v_val_737_ = lean_ctor_get(v___y_725_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v___y_725_, 1);
v___y_692_ = v___y_713_;
v___y_693_ = v___y_714_;
v___y_694_ = v___y_729_;
v___y_695_ = v___y_715_;
v___y_696_ = v___y_716_;
v___y_697_ = v___y_717_;
v___y_698_ = v___y_718_;
v___y_699_ = v___y_719_;
v___y_700_ = v___y_720_;
v___y_701_ = v___y_721_;
v___y_702_ = v___y_722_;
v___y_703_ = v___y_723_;
v___y_704_ = v___y_724_;
v___y_705_ = v___x_730_;
v___y_706_ = v___y_726_;
v___y_707_ = v___x_731_;
v___y_708_ = v___y_727_;
v___y_709_ = v___y_728_;
v_val_710_ = v_val_737_;
goto v___jp_691_;
}
}
v___jp_738_:
{
if (lean_obj_tag(v___y_745_) == 0)
{
lean_object* v___x_756_; 
v___x_756_ = lean_box(0);
v___y_713_ = v___y_739_;
v___y_714_ = v___y_740_;
v___y_715_ = v___y_755_;
v___y_716_ = v___y_741_;
v___y_717_ = v___y_742_;
v___y_718_ = v___y_743_;
v___y_719_ = v___y_744_;
v___y_720_ = v___y_746_;
v___y_721_ = v___y_747_;
v___y_722_ = v___y_748_;
v___y_723_ = v___y_749_;
v___y_724_ = v___y_750_;
v___y_725_ = v___y_752_;
v___y_726_ = v___y_751_;
v___y_727_ = v___y_753_;
v___y_728_ = v___y_754_;
v___y_729_ = v___x_756_;
goto v___jp_712_;
}
else
{
lean_object* v_val_757_; lean_object* v___x_758_; 
v_val_757_ = lean_ctor_get(v___y_745_, 0);
lean_inc(v_val_757_);
lean_dec_ref_known(v___y_745_, 1);
v___x_758_ = l_Lake_envToBool_x3f(v_val_757_);
v___y_713_ = v___y_739_;
v___y_714_ = v___y_740_;
v___y_715_ = v___y_755_;
v___y_716_ = v___y_741_;
v___y_717_ = v___y_742_;
v___y_718_ = v___y_743_;
v___y_719_ = v___y_744_;
v___y_720_ = v___y_746_;
v___y_721_ = v___y_747_;
v___y_722_ = v___y_748_;
v___y_723_ = v___y_749_;
v___y_724_ = v___y_750_;
v___y_725_ = v___y_752_;
v___y_726_ = v___y_751_;
v___y_727_ = v___y_753_;
v___y_728_ = v___y_754_;
v___y_729_ = v___x_758_;
goto v___jp_712_;
}
}
v___jp_759_:
{
if (lean_obj_tag(v___y_769_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = lean_box(0);
v___y_739_ = v___y_760_;
v___y_740_ = v___y_761_;
v___y_741_ = v___y_762_;
v___y_742_ = v___y_763_;
v___y_743_ = v___y_764_;
v___y_744_ = v___y_765_;
v___y_745_ = v___y_766_;
v___y_746_ = v___y_767_;
v___y_747_ = v___y_768_;
v___y_748_ = v___y_770_;
v___y_749_ = v___y_771_;
v___y_750_ = v___y_772_;
v___y_751_ = v___y_774_;
v___y_752_ = v___y_773_;
v___y_753_ = v___y_776_;
v___y_754_ = v___y_775_;
v___y_755_ = v___x_777_;
goto v___jp_738_;
}
else
{
lean_object* v_val_778_; lean_object* v___x_779_; 
v_val_778_ = lean_ctor_get(v___y_769_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v___y_769_, 1);
v___x_779_ = l_Lake_envToBool_x3f(v_val_778_);
v___y_739_ = v___y_760_;
v___y_740_ = v___y_761_;
v___y_741_ = v___y_762_;
v___y_742_ = v___y_763_;
v___y_743_ = v___y_764_;
v___y_744_ = v___y_765_;
v___y_745_ = v___y_766_;
v___y_746_ = v___y_767_;
v___y_747_ = v___y_768_;
v___y_748_ = v___y_770_;
v___y_749_ = v___y_771_;
v___y_750_ = v___y_772_;
v___y_751_ = v___y_774_;
v___y_752_ = v___y_773_;
v___y_753_ = v___y_776_;
v___y_754_ = v___y_775_;
v___y_755_ = v___x_779_;
goto v___jp_738_;
}
}
v___jp_780_:
{
uint8_t v___x_797_; 
v___x_797_ = 0;
v___y_760_ = v___y_781_;
v___y_761_ = v___y_782_;
v___y_762_ = v___y_783_;
v___y_763_ = v___y_784_;
v___y_764_ = v___y_785_;
v___y_765_ = v___y_786_;
v___y_766_ = v___y_787_;
v___y_767_ = v___y_788_;
v___y_768_ = v___y_789_;
v___y_769_ = v___y_790_;
v___y_770_ = v___y_791_;
v___y_771_ = v___y_792_;
v___y_772_ = v___y_793_;
v___y_773_ = v___y_795_;
v___y_774_ = v___y_794_;
v___y_775_ = v___y_796_;
v___y_776_ = v___x_797_;
goto v___jp_759_;
}
v___jp_798_:
{
if (lean_obj_tag(v_noCache_536_) == 0)
{
if (lean_obj_tag(v___y_811_) == 0)
{
v___y_781_ = v___y_799_;
v___y_782_ = v___y_800_;
v___y_783_ = v___y_815_;
v___y_784_ = v___y_801_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_804_;
v___y_788_ = v___y_805_;
v___y_789_ = v___y_806_;
v___y_790_ = v___y_807_;
v___y_791_ = v___y_808_;
v___y_792_ = v___y_809_;
v___y_793_ = v___y_810_;
v___y_794_ = v___y_812_;
v___y_795_ = v___y_813_;
v___y_796_ = v___y_814_;
goto v___jp_780_;
}
else
{
lean_object* v_val_816_; lean_object* v___x_817_; 
v_val_816_ = lean_ctor_get(v___y_811_, 0);
lean_inc(v_val_816_);
lean_dec_ref_known(v___y_811_, 1);
v___x_817_ = l_Lake_envToBool_x3f(v_val_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
v___y_781_ = v___y_799_;
v___y_782_ = v___y_800_;
v___y_783_ = v___y_815_;
v___y_784_ = v___y_801_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_804_;
v___y_788_ = v___y_805_;
v___y_789_ = v___y_806_;
v___y_790_ = v___y_807_;
v___y_791_ = v___y_808_;
v___y_792_ = v___y_809_;
v___y_793_ = v___y_810_;
v___y_794_ = v___y_812_;
v___y_795_ = v___y_813_;
v___y_796_ = v___y_814_;
goto v___jp_780_;
}
else
{
lean_object* v_val_818_; uint8_t v___x_819_; 
v_val_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_val_818_);
lean_dec_ref_known(v___x_817_, 1);
v___x_819_ = lean_unbox(v_val_818_);
lean_dec(v_val_818_);
v___y_760_ = v___y_799_;
v___y_761_ = v___y_800_;
v___y_762_ = v___y_815_;
v___y_763_ = v___y_801_;
v___y_764_ = v___y_802_;
v___y_765_ = v___y_803_;
v___y_766_ = v___y_804_;
v___y_767_ = v___y_805_;
v___y_768_ = v___y_806_;
v___y_769_ = v___y_807_;
v___y_770_ = v___y_808_;
v___y_771_ = v___y_809_;
v___y_772_ = v___y_810_;
v___y_773_ = v___y_813_;
v___y_774_ = v___y_812_;
v___y_775_ = v___y_814_;
v___y_776_ = v___x_819_;
goto v___jp_759_;
}
}
}
else
{
lean_object* v_val_820_; uint8_t v___x_821_; 
lean_dec(v___y_811_);
v_val_820_ = lean_ctor_get(v_noCache_536_, 0);
v___x_821_ = lean_unbox(v_val_820_);
v___y_760_ = v___y_799_;
v___y_761_ = v___y_800_;
v___y_762_ = v___y_815_;
v___y_763_ = v___y_801_;
v___y_764_ = v___y_802_;
v___y_765_ = v___y_803_;
v___y_766_ = v___y_804_;
v___y_767_ = v___y_805_;
v___y_768_ = v___y_806_;
v___y_769_ = v___y_807_;
v___y_770_ = v___y_808_;
v___y_771_ = v___y_809_;
v___y_772_ = v___y_810_;
v___y_773_ = v___y_813_;
v___y_774_ = v___y_812_;
v___y_775_ = v___y_814_;
v___y_776_ = v___x_821_;
goto v___jp_759_;
}
}
v___jp_822_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_827_ = ((lean_object*)(l_Lake_Env_compute___closed__2));
v___x_828_ = lean_io_getenv(v___x_827_);
v___x_829_ = ((lean_object*)(l_Lake_Env_compute___closed__3));
v___x_830_ = lean_io_getenv(v___x_829_);
v___x_831_ = ((lean_object*)(l_Lake_Env_compute___closed__4));
v___x_832_ = lean_io_getenv(v___x_831_);
v___x_833_ = ((lean_object*)(l_Lake_Env_compute___closed__5));
v___x_834_ = lean_io_getenv(v___x_833_);
v___x_835_ = ((lean_object*)(l_Lake_Env_compute___closed__6));
v___x_836_ = lean_io_getenv(v___x_835_);
v___x_837_ = ((lean_object*)(l_Lake_Env_compute___closed__7));
v___x_838_ = lean_io_getenv(v___x_837_);
v___x_839_ = ((lean_object*)(l_Lake_Env_compute___closed__8));
v___x_840_ = lean_io_getenv(v___x_839_);
v___x_841_ = ((lean_object*)(l_Lake_Env_compute___closed__9));
v___x_842_ = lean_io_getenv(v___x_841_);
v___x_843_ = ((lean_object*)(l_Lake_Env_compute___closed__10));
v___x_844_ = lean_io_getenv(v___x_843_);
v___x_845_ = ((lean_object*)(l_Lake_Env_compute___closed__11));
v___x_846_ = l_Lake_getSearchPath(v___x_845_);
v___x_847_ = ((lean_object*)(l_Lake_Env_compute___closed__12));
v___x_848_ = l_Lake_getSearchPath(v___x_847_);
v___x_849_ = l_Lake_sharedLibPathEnvVar;
v___x_850_ = l_Lake_getSearchPath(v___x_849_);
v___x_851_ = ((lean_object*)(l_Lake_Env_compute___closed__13));
v___x_852_ = l_Lake_getSearchPath(v___x_851_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_853_; 
v___x_853_ = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
v___y_799_ = v___y_823_;
v___y_800_ = v___x_836_;
v___y_801_ = v___x_842_;
v___y_802_ = v___x_840_;
v___y_803_ = v___x_852_;
v___y_804_ = v___x_832_;
v___y_805_ = v___y_825_;
v___y_806_ = v_a_826_;
v___y_807_ = v___x_830_;
v___y_808_ = v___y_824_;
v___y_809_ = v___x_846_;
v___y_810_ = v___x_848_;
v___y_811_ = v___x_828_;
v___y_812_ = v___x_838_;
v___y_813_ = v___x_834_;
v___y_814_ = v___x_850_;
v___y_815_ = v___x_853_;
goto v___jp_798_;
}
else
{
lean_object* v_val_854_; 
v_val_854_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_val_854_);
lean_dec_ref_known(v___x_844_, 1);
v___y_799_ = v___y_823_;
v___y_800_ = v___x_836_;
v___y_801_ = v___x_842_;
v___y_802_ = v___x_840_;
v___y_803_ = v___x_852_;
v___y_804_ = v___x_832_;
v___y_805_ = v___y_825_;
v___y_806_ = v_a_826_;
v___y_807_ = v___x_830_;
v___y_808_ = v___y_824_;
v___y_809_ = v___x_846_;
v___y_810_ = v___x_848_;
v___y_811_ = v___x_828_;
v___y_812_ = v___x_838_;
v___y_813_ = v___x_834_;
v___y_814_ = v___x_850_;
v___y_815_ = v_val_854_;
goto v___jp_798_;
}
}
v___jp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = l_Lake_Env_computeToolchain();
v___x_858_ = l_Lake_getUserHome_x3f();
v___x_859_ = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = ((lean_object*)(l_Lake_Env_compute___closed__14));
v___x_862_ = lean_io_getenv(v___x_861_);
if (lean_obj_tag(v___x_862_) == 1)
{
lean_object* v_val_863_; lean_object* v___x_864_; 
lean_dec_ref(v_a_856_);
v_val_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_863_);
v___y_823_ = v_a_860_;
v___y_824_ = v___x_857_;
v___y_825_ = v___x_858_;
v_a_826_ = v___x_864_;
goto v___jp_822_;
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec(v___x_862_);
v___x_865_ = ((lean_object*)(l_Lake_Env_compute___closed__15));
v___x_866_ = lean_string_append(v_a_856_, v___x_865_);
v___y_823_ = v_a_860_;
v___y_824_ = v___x_857_;
v___y_825_ = v___x_858_;
v_a_826_ = v___x_866_;
goto v___jp_822_;
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec(v___x_858_);
lean_dec_ref(v___x_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_elan_x3f_535_);
lean_dec_ref(v_lean_534_);
lean_dec_ref(v_lake_533_);
v_a_867_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_859_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_859_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_Env_compute_0interp(lean_interpreter_value* stack)
{
lean_object* v_lake_533_ = stack[0].m_obj;
lean_object* v_lean_534_ = stack[1].m_obj;
lean_object* v_elan_x3f_535_ = stack[2].m_obj;
lean_object* v_noCache_536_ = stack[3].m_obj;
lean_object* v_res_880_;
v_res_880_ = l_Lake_Env_compute(v_lake_533_, v_lean_534_, v_elan_x3f_535_, v_noCache_536_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object* v_lake_881_, lean_object* v_lean_882_, lean_object* v_elan_x3f_883_, lean_object* v_noCache_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lake_Env_compute(v_lake_881_, v_lean_882_, v_elan_x3f_883_, v_noCache_884_);
lean_dec(v_noCache_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain(lean_object* v_env_887_){
_start:
{
lean_object* v_toolchain_888_; 
v_toolchain_888_ = lean_ctor_get(v_env_887_, 19);
lean_inc_ref(v_toolchain_888_);
return v_toolchain_888_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain___boxed(lean_object* v_env_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lake_Env_cacheToolchain(v_env_889_);
lean_dec_ref(v_env_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object* v_env_891_){
_start:
{
lean_object* v_lean_892_; lean_object* v_githashOverride_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_lean_892_ = lean_ctor_get(v_env_891_, 1);
v_githashOverride_893_ = lean_ctor_get(v_env_891_, 4);
v___x_894_ = lean_string_utf8_byte_size(v_githashOverride_893_);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_nat_dec_eq(v___x_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_inc_ref(v_githashOverride_893_);
return v_githashOverride_893_;
}
else
{
lean_object* v_githash_897_; 
v_githash_897_ = lean_ctor_get(v_lean_892_, 1);
lean_inc_ref(v_githash_897_);
return v_githash_897_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object* v_env_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lake_Env_leanGithash(v_env_898_);
lean_dec_ref(v_env_898_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object* v_env_900_){
_start:
{
lean_object* v_lake_901_; lean_object* v_lean_902_; lean_object* v_initPath_903_; lean_object* v_binDir_904_; lean_object* v_binDir_905_; uint8_t v___x_906_; 
v_lake_901_ = lean_ctor_get(v_env_900_, 0);
v_lean_902_ = lean_ctor_get(v_env_900_, 1);
v_initPath_903_ = lean_ctor_get(v_env_900_, 18);
v_binDir_904_ = lean_ctor_get(v_lake_901_, 2);
v_binDir_905_ = lean_ctor_get(v_lean_902_, 6);
v___x_906_ = lean_string_dec_eq(v_binDir_904_, v_binDir_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_inc(v_initPath_903_);
lean_inc_ref(v_binDir_905_);
v___x_907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_907_, 0, v_binDir_905_);
lean_ctor_set(v___x_907_, 1, v_initPath_903_);
lean_inc_ref(v_binDir_904_);
v___x_908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_908_, 0, v_binDir_904_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
return v___x_908_;
}
else
{
lean_object* v___x_909_; 
lean_inc(v_initPath_903_);
lean_inc_ref(v_binDir_905_);
v___x_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_909_, 0, v_binDir_905_);
lean_ctor_set(v___x_909_, 1, v_initPath_903_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object* v_env_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lake_Env_path(v_env_910_);
lean_dec_ref(v_env_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object* v_env_912_){
_start:
{
lean_object* v_lake_913_; lean_object* v_initLeanPath_914_; lean_object* v_libDir_915_; lean_object* v___x_916_; 
v_lake_913_ = lean_ctor_get(v_env_912_, 0);
v_initLeanPath_914_ = lean_ctor_get(v_env_912_, 15);
v_libDir_915_ = lean_ctor_get(v_lake_913_, 3);
lean_inc(v_initLeanPath_914_);
lean_inc_ref(v_libDir_915_);
v___x_916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_916_, 0, v_libDir_915_);
lean_ctor_set(v___x_916_, 1, v_initLeanPath_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object* v_env_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lake_Env_leanPath(v_env_917_);
lean_dec_ref(v_env_917_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object* v_env_919_){
_start:
{
lean_object* v_lake_920_; lean_object* v_initLeanSrcPath_921_; lean_object* v_srcDir_922_; lean_object* v___x_923_; 
v_lake_920_ = lean_ctor_get(v_env_919_, 0);
v_initLeanSrcPath_921_ = lean_ctor_get(v_env_919_, 16);
v_srcDir_922_ = lean_ctor_get(v_lake_920_, 1);
lean_inc(v_initLeanSrcPath_921_);
lean_inc_ref(v_srcDir_922_);
v___x_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_923_, 0, v_srcDir_922_);
lean_ctor_set(v___x_923_, 1, v_initLeanSrcPath_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object* v_env_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lake_Env_leanSrcPath(v_env_924_);
lean_dec_ref(v_env_924_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object* v_env_926_){
_start:
{
lean_object* v_lean_927_; lean_object* v_initSharedLibPath_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_lean_927_ = lean_ctor_get(v_env_926_, 1);
lean_inc_ref(v_lean_927_);
v_initSharedLibPath_928_ = lean_ctor_get(v_env_926_, 17);
lean_inc(v_initSharedLibPath_928_);
lean_dec_ref(v_env_926_);
v___x_929_ = l_Lake_LeanInstall_sharedLibPath(v_lean_927_);
lean_dec_ref(v_lean_927_);
v___x_930_ = l_List_appendTR___redArg(v___x_929_, v_initSharedLibPath_928_);
return v___x_930_;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__14(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_961_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__0));
v___x_962_ = lean_unsigned_to_nat(9u);
v___x_963_ = lean_mk_empty_array_with_capacity(v___x_962_);
v___x_964_ = lean_array_push(v___x_963_, v___x_961_);
return v___x_964_;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__15(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__2));
v___x_966_ = lean_obj_once(&l_Lake_Env_noToolchainVars___closed__14, &l_Lake_Env_noToolchainVars___closed__14_once, _init_l_Lake_Env_noToolchainVars___closed__14);
v___x_967_ = lean_array_push(v___x_966_, v___x_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars(lean_object* v_env_970_){
_start:
{
uint8_t v_noSystemCache_971_; lean_object* v_lakeSystemCache_x3f_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___y_976_; 
v_noSystemCache_971_ = lean_ctor_get_uint8(v_env_970_, sizeof(void*)*20 + 1);
v_lakeSystemCache_x3f_972_ = lean_ctor_get(v_env_970_, 9);
lean_inc(v_lakeSystemCache_x3f_972_);
lean_dec_ref(v_env_970_);
v___x_973_ = lean_box(0);
v___x_974_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
if (v_noSystemCache_971_ == 0)
{
if (lean_obj_tag(v_lakeSystemCache_x3f_972_) == 0)
{
v___y_976_ = v___x_973_;
goto v___jp_975_;
}
else
{
lean_object* v_val_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
v_val_992_ = lean_ctor_get(v_lakeSystemCache_x3f_972_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v_lakeSystemCache_x3f_972_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v_lakeSystemCache_x3f_972_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_val_992_);
lean_dec(v_lakeSystemCache_x3f_972_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_val_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
v___y_976_ = v___x_997_;
goto v___jp_975_;
}
}
}
}
else
{
lean_object* v___x_1000_; 
lean_dec(v_lakeSystemCache_x3f_972_);
v___x_1000_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_976_ = v___x_1000_;
goto v___jp_975_;
}
v___jp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_974_);
lean_ctor_set(v___x_977_, 1, v___y_976_);
v___x_978_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__4));
v___x_979_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__6));
v___x_980_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__8));
v___x_981_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__9));
v___x_982_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__11));
v___x_983_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__13));
v___x_984_ = lean_obj_once(&l_Lake_Env_noToolchainVars___closed__15, &l_Lake_Env_noToolchainVars___closed__15_once, _init_l_Lake_Env_noToolchainVars___closed__15);
v___x_985_ = lean_array_push(v___x_984_, v___x_977_);
v___x_986_ = lean_array_push(v___x_985_, v___x_978_);
v___x_987_ = lean_array_push(v___x_986_, v___x_979_);
v___x_988_ = lean_array_push(v___x_987_, v___x_980_);
v___x_989_ = lean_array_push(v___x_988_, v___x_981_);
v___x_990_ = lean_array_push(v___x_989_, v___x_982_);
v___x_991_ = lean_array_push(v___x_990_, v___x_983_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1001_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_box(1);
v___x_1003_ = lean_panic_fn_borrowed(v___x_1002_, v_msg_1001_);
return v___x_1003_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1007_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2));
v___x_1008_ = lean_unsigned_to_nat(35u);
v___x_1009_ = lean_unsigned_to_nat(182u);
v___x_1010_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1));
v___x_1011_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1012_ = l_mkPanicMessageWithDecl(v___x_1011_, v___x_1010_, v___x_1009_, v___x_1008_, v___x_1007_);
return v___x_1012_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1013_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2));
v___x_1014_ = lean_unsigned_to_nat(21u);
v___x_1015_ = lean_unsigned_to_nat(183u);
v___x_1016_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1));
v___x_1017_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1018_ = l_mkPanicMessageWithDecl(v___x_1017_, v___x_1016_, v___x_1015_, v___x_1014_, v___x_1013_);
return v___x_1018_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1021_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6));
v___x_1022_ = lean_unsigned_to_nat(35u);
v___x_1023_ = lean_unsigned_to_nat(276u);
v___x_1024_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5));
v___x_1025_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1026_ = l_mkPanicMessageWithDecl(v___x_1025_, v___x_1024_, v___x_1023_, v___x_1022_, v___x_1021_);
return v___x_1026_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1027_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6));
v___x_1028_ = lean_unsigned_to_nat(21u);
v___x_1029_ = lean_unsigned_to_nat(277u);
v___x_1030_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5));
v___x_1031_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1032_ = l_mkPanicMessageWithDecl(v___x_1031_, v___x_1030_, v___x_1029_, v___x_1028_, v___x_1027_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(lean_object* v_k_1033_, lean_object* v_v_1034_, lean_object* v_t_1035_){
_start:
{
if (lean_obj_tag(v_t_1035_) == 0)
{
lean_object* v_size_1036_; lean_object* v_k_1037_; lean_object* v_v_1038_; lean_object* v_l_1039_; lean_object* v_r_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1396_; 
v_size_1036_ = lean_ctor_get(v_t_1035_, 0);
v_k_1037_ = lean_ctor_get(v_t_1035_, 1);
v_v_1038_ = lean_ctor_get(v_t_1035_, 2);
v_l_1039_ = lean_ctor_get(v_t_1035_, 3);
v_r_1040_ = lean_ctor_get(v_t_1035_, 4);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_t_1035_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1042_ = v_t_1035_;
v_isShared_1043_ = v_isSharedCheck_1396_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_r_1040_);
lean_inc(v_l_1039_);
lean_inc(v_v_1038_);
lean_inc(v_k_1037_);
lean_inc(v_size_1036_);
lean_dec(v_t_1035_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1396_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
uint8_t v___x_1044_; 
v___x_1044_ = lean_string_compare(v_k_1033_, v_k_1037_);
switch(v___x_1044_)
{
case 0:
{
lean_object* v___x_1045_; 
lean_dec(v_size_1036_);
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_1033_, v_v_1034_, v_l_1039_);
if (lean_obj_tag(v_r_1040_) == 0)
{
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_size_1046_; lean_object* v_size_1047_; lean_object* v_k_1048_; lean_object* v_v_1049_; lean_object* v_l_1050_; lean_object* v_r_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_size_1046_ = lean_ctor_get(v_r_1040_, 0);
v_size_1047_ = lean_ctor_get(v___x_1045_, 0);
v_k_1048_ = lean_ctor_get(v___x_1045_, 1);
v_v_1049_ = lean_ctor_get(v___x_1045_, 2);
v_l_1050_ = lean_ctor_get(v___x_1045_, 3);
v_r_1051_ = lean_ctor_get(v___x_1045_, 4);
lean_inc(v_r_1051_);
v___x_1052_ = lean_unsigned_to_nat(3u);
v___x_1053_ = lean_nat_mul(v___x_1052_, v_size_1046_);
v___x_1054_ = lean_nat_dec_lt(v___x_1053_, v_size_1047_);
lean_dec(v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
lean_dec(v_r_1051_);
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_add(v___x_1055_, v_size_1047_);
v___x_1057_ = lean_nat_add(v___x_1056_, v_size_1046_);
lean_dec(v___x_1056_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 3, v___x_1045_);
lean_ctor_set(v___x_1042_, 0, v___x_1057_);
v___x_1059_ = v___x_1042_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v_r_1040_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
else
{
lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1132_; 
lean_inc(v_l_1050_);
lean_inc(v_v_1049_);
lean_inc(v_k_1048_);
lean_inc(v_size_1047_);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; lean_object* v_unused_1134_; lean_object* v_unused_1135_; lean_object* v_unused_1136_; lean_object* v_unused_1137_; 
v_unused_1133_ = lean_ctor_get(v___x_1045_, 4);
lean_dec(v_unused_1133_);
v_unused_1134_ = lean_ctor_get(v___x_1045_, 3);
lean_dec(v_unused_1134_);
v_unused_1135_ = lean_ctor_get(v___x_1045_, 2);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v___x_1045_, 1);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v___x_1045_, 0);
lean_dec(v_unused_1137_);
v___x_1062_ = v___x_1045_;
v_isShared_1063_ = v_isSharedCheck_1132_;
goto v_resetjp_1061_;
}
else
{
lean_dec(v___x_1045_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1132_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
if (lean_obj_tag(v_l_1050_) == 0)
{
if (lean_obj_tag(v_r_1051_) == 0)
{
lean_object* v_size_1064_; lean_object* v_size_1065_; lean_object* v_k_1066_; lean_object* v_v_1067_; lean_object* v_l_1068_; lean_object* v_r_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_size_1064_ = lean_ctor_get(v_l_1050_, 0);
v_size_1065_ = lean_ctor_get(v_r_1051_, 0);
v_k_1066_ = lean_ctor_get(v_r_1051_, 1);
v_v_1067_ = lean_ctor_get(v_r_1051_, 2);
v_l_1068_ = lean_ctor_get(v_r_1051_, 3);
v_r_1069_ = lean_ctor_get(v_r_1051_, 4);
v___x_1070_ = lean_unsigned_to_nat(2u);
v___x_1071_ = lean_nat_mul(v___x_1070_, v_size_1064_);
v___x_1072_ = lean_nat_dec_lt(v_size_1065_, v___x_1071_);
lean_dec(v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1102_; 
lean_inc(v_r_1069_);
lean_inc(v_l_1068_);
lean_inc(v_v_1067_);
lean_inc(v_k_1066_);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_r_1051_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; lean_object* v_unused_1104_; lean_object* v_unused_1105_; lean_object* v_unused_1106_; lean_object* v_unused_1107_; 
v_unused_1103_ = lean_ctor_get(v_r_1051_, 4);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_r_1051_, 3);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_r_1051_, 2);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v_r_1051_, 1);
lean_dec(v_unused_1106_);
v_unused_1107_ = lean_ctor_get(v_r_1051_, 0);
lean_dec(v_unused_1107_);
v___x_1074_ = v_r_1051_;
v_isShared_1075_ = v_isSharedCheck_1102_;
goto v_resetjp_1073_;
}
else
{
lean_dec(v_r_1051_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1102_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___x_1090_; lean_object* v___y_1092_; 
v___x_1076_ = lean_unsigned_to_nat(1u);
v___x_1077_ = lean_nat_add(v___x_1076_, v_size_1047_);
lean_dec(v_size_1047_);
v___x_1078_ = lean_nat_add(v___x_1077_, v_size_1046_);
lean_dec(v___x_1077_);
v___x_1090_ = lean_nat_add(v___x_1076_, v_size_1064_);
if (lean_obj_tag(v_l_1068_) == 0)
{
lean_object* v_size_1100_; 
v_size_1100_ = lean_ctor_get(v_l_1068_, 0);
lean_inc(v_size_1100_);
v___y_1092_ = v_size_1100_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_unsigned_to_nat(0u);
v___y_1092_ = v___x_1101_;
goto v___jp_1091_;
}
v___jp_1079_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = lean_nat_add(v___y_1080_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec(v___y_1080_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 4, v_r_1040_);
lean_ctor_set(v___x_1074_, 3, v_r_1069_);
lean_ctor_set(v___x_1074_, 2, v_v_1038_);
lean_ctor_set(v___x_1074_, 1, v_k_1037_);
lean_ctor_set(v___x_1074_, 0, v___x_1083_);
v___x_1085_ = v___x_1074_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_r_1069_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_r_1040_);
v___x_1085_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1087_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v___x_1085_);
lean_ctor_set(v___x_1062_, 3, v___y_1081_);
lean_ctor_set(v___x_1062_, 2, v_v_1067_);
lean_ctor_set(v___x_1062_, 1, v_k_1066_);
lean_ctor_set(v___x_1062_, 0, v___x_1078_);
v___x_1087_ = v___x_1062_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v___y_1081_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
v___jp_1091_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = lean_nat_add(v___x_1090_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec(v___x_1090_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v_l_1068_);
lean_ctor_set(v___x_1042_, 3, v_l_1050_);
lean_ctor_set(v___x_1042_, 2, v_v_1049_);
lean_ctor_set(v___x_1042_, 1, v_k_1048_);
lean_ctor_set(v___x_1042_, 0, v___x_1093_);
v___x_1095_ = v___x_1042_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_k_1048_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v_v_1049_);
lean_ctor_set(v_reuseFailAlloc_1099_, 3, v_l_1050_);
lean_ctor_set(v_reuseFailAlloc_1099_, 4, v_l_1068_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_nat_add(v___x_1076_, v_size_1046_);
if (lean_obj_tag(v_r_1069_) == 0)
{
lean_object* v_size_1097_; 
v_size_1097_ = lean_ctor_get(v_r_1069_, 0);
lean_inc(v_size_1097_);
v___y_1080_ = v___x_1096_;
v___y_1081_ = v___x_1095_;
v___y_1082_ = v_size_1097_;
goto v___jp_1079_;
}
else
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_unsigned_to_nat(0u);
v___y_1080_ = v___x_1096_;
v___y_1081_ = v___x_1095_;
v___y_1082_ = v___x_1098_;
goto v___jp_1079_;
}
}
}
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
lean_del_object(v___x_1042_);
v___x_1108_ = lean_unsigned_to_nat(1u);
v___x_1109_ = lean_nat_add(v___x_1108_, v_size_1047_);
lean_dec(v_size_1047_);
v___x_1110_ = lean_nat_add(v___x_1109_, v_size_1046_);
lean_dec(v___x_1109_);
v___x_1111_ = lean_nat_add(v___x_1108_, v_size_1046_);
v___x_1112_ = lean_nat_add(v___x_1111_, v_size_1065_);
lean_dec(v___x_1111_);
lean_inc_ref(v_r_1040_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v_r_1040_);
lean_ctor_set(v___x_1062_, 3, v_r_1051_);
lean_ctor_set(v___x_1062_, 2, v_v_1038_);
lean_ctor_set(v___x_1062_, 1, v_k_1037_);
lean_ctor_set(v___x_1062_, 0, v___x_1112_);
v___x_1114_ = v___x_1062_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1127_, 3, v_r_1051_);
lean_ctor_set(v_reuseFailAlloc_1127_, 4, v_r_1040_);
v___x_1114_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_isSharedCheck_1121_ = !lean_is_exclusive(v_r_1040_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; lean_object* v_unused_1123_; lean_object* v_unused_1124_; lean_object* v_unused_1125_; lean_object* v_unused_1126_; 
v_unused_1122_ = lean_ctor_get(v_r_1040_, 4);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_r_1040_, 3);
lean_dec(v_unused_1123_);
v_unused_1124_ = lean_ctor_get(v_r_1040_, 2);
lean_dec(v_unused_1124_);
v_unused_1125_ = lean_ctor_get(v_r_1040_, 1);
lean_dec(v_unused_1125_);
v_unused_1126_ = lean_ctor_get(v_r_1040_, 0);
lean_dec(v_unused_1126_);
v___x_1116_ = v_r_1040_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_dec(v_r_1040_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 4, v___x_1114_);
lean_ctor_set(v___x_1116_, 3, v_l_1050_);
lean_ctor_set(v___x_1116_, 2, v_v_1049_);
lean_ctor_set(v___x_1116_, 1, v_k_1048_);
lean_ctor_set(v___x_1116_, 0, v___x_1110_);
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_k_1048_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_v_1049_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_l_1050_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v___x_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec_ref_known(v_l_1050_, 5);
lean_del_object(v___x_1062_);
lean_dec(v_v_1049_);
lean_dec(v_k_1048_);
lean_dec(v_size_1047_);
lean_dec_ref_known(v_r_1040_, 5);
lean_del_object(v___x_1042_);
lean_dec(v_v_1038_);
lean_dec(v_k_1037_);
v___x_1128_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3);
v___x_1129_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1128_);
return v___x_1129_;
}
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_del_object(v___x_1062_);
lean_dec(v_r_1051_);
lean_dec(v_v_1049_);
lean_dec(v_k_1048_);
lean_dec(v_size_1047_);
lean_dec_ref_known(v_r_1040_, 5);
lean_del_object(v___x_1042_);
lean_dec(v_v_1038_);
lean_dec(v_k_1037_);
v___x_1130_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4);
v___x_1131_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1130_);
return v___x_1131_;
}
}
}
}
else
{
lean_object* v_size_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v_size_1138_ = lean_ctor_get(v_r_1040_, 0);
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_nat_add(v___x_1139_, v_size_1138_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 3, v___x_1045_);
lean_ctor_set(v___x_1042_, 0, v___x_1140_);
v___x_1142_ = v___x_1042_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_r_1040_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_l_1144_; 
v_l_1144_ = lean_ctor_get(v___x_1045_, 3);
if (lean_obj_tag(v_l_1144_) == 0)
{
lean_object* v_r_1145_; 
lean_inc_ref(v_l_1144_);
v_r_1145_ = lean_ctor_get(v___x_1045_, 4);
lean_inc(v_r_1145_);
if (lean_obj_tag(v_r_1145_) == 0)
{
lean_object* v_size_1146_; lean_object* v_k_1147_; lean_object* v_v_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1162_; 
v_size_1146_ = lean_ctor_get(v___x_1045_, 0);
v_k_1147_ = lean_ctor_get(v___x_1045_, 1);
v_v_1148_ = lean_ctor_get(v___x_1045_, 2);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; lean_object* v_unused_1164_; 
v_unused_1163_ = lean_ctor_get(v___x_1045_, 4);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v___x_1045_, 3);
lean_dec(v_unused_1164_);
v___x_1150_ = v___x_1045_;
v_isShared_1151_ = v_isSharedCheck_1162_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_v_1148_);
lean_inc(v_k_1147_);
lean_inc(v_size_1146_);
lean_dec(v___x_1045_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1162_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_size_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v_size_1152_ = lean_ctor_get(v_r_1145_, 0);
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_add(v___x_1153_, v_size_1146_);
lean_dec(v_size_1146_);
v___x_1155_ = lean_nat_add(v___x_1153_, v_size_1152_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 4, v_r_1040_);
lean_ctor_set(v___x_1150_, 3, v_r_1145_);
lean_ctor_set(v___x_1150_, 2, v_v_1038_);
lean_ctor_set(v___x_1150_, 1, v_k_1037_);
lean_ctor_set(v___x_1150_, 0, v___x_1155_);
v___x_1157_ = v___x_1150_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_r_1145_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_r_1040_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1157_);
lean_ctor_set(v___x_1042_, 3, v_l_1144_);
lean_ctor_set(v___x_1042_, 2, v_v_1148_);
lean_ctor_set(v___x_1042_, 1, v_k_1147_);
lean_ctor_set(v___x_1042_, 0, v___x_1154_);
v___x_1159_ = v___x_1042_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_1147_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_1148_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v_l_1144_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v_k_1165_; lean_object* v_v_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1178_; 
v_k_1165_ = lean_ctor_get(v___x_1045_, 1);
v_v_1166_ = lean_ctor_get(v___x_1045_, 2);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; 
v_unused_1179_ = lean_ctor_get(v___x_1045_, 4);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v___x_1045_, 3);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v___x_1045_, 0);
lean_dec(v_unused_1181_);
v___x_1168_ = v___x_1045_;
v_isShared_1169_ = v_isSharedCheck_1178_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_v_1166_);
lean_inc(v_k_1165_);
lean_dec(v___x_1045_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1178_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1170_ = lean_unsigned_to_nat(3u);
v___x_1171_ = lean_unsigned_to_nat(1u);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 3, v_r_1145_);
lean_ctor_set(v___x_1168_, 2, v_v_1038_);
lean_ctor_set(v___x_1168_, 1, v_k_1037_);
lean_ctor_set(v___x_1168_, 0, v___x_1171_);
v___x_1173_ = v___x_1168_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_r_1145_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_r_1145_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1175_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1173_);
lean_ctor_set(v___x_1042_, 3, v_l_1144_);
lean_ctor_set(v___x_1042_, 2, v_v_1166_);
lean_ctor_set(v___x_1042_, 1, v_k_1165_);
lean_ctor_set(v___x_1042_, 0, v___x_1170_);
v___x_1175_ = v___x_1042_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_k_1165_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_v_1166_);
lean_ctor_set(v_reuseFailAlloc_1176_, 3, v_l_1144_);
lean_ctor_set(v_reuseFailAlloc_1176_, 4, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
else
{
lean_object* v_r_1182_; 
v_r_1182_ = lean_ctor_get(v___x_1045_, 4);
lean_inc(v_r_1182_);
if (lean_obj_tag(v_r_1182_) == 0)
{
lean_object* v_k_1183_; lean_object* v_v_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1208_; 
lean_inc(v_l_1144_);
v_k_1183_ = lean_ctor_get(v___x_1045_, 1);
v_v_1184_ = lean_ctor_get(v___x_1045_, 2);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; lean_object* v_unused_1210_; lean_object* v_unused_1211_; 
v_unused_1209_ = lean_ctor_get(v___x_1045_, 4);
lean_dec(v_unused_1209_);
v_unused_1210_ = lean_ctor_get(v___x_1045_, 3);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v___x_1045_, 0);
lean_dec(v_unused_1211_);
v___x_1186_ = v___x_1045_;
v_isShared_1187_ = v_isSharedCheck_1208_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_v_1184_);
lean_inc(v_k_1183_);
lean_dec(v___x_1045_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1208_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_k_1188_; lean_object* v_v_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1204_; 
v_k_1188_ = lean_ctor_get(v_r_1182_, 1);
v_v_1189_ = lean_ctor_get(v_r_1182_, 2);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_r_1182_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; lean_object* v_unused_1206_; lean_object* v_unused_1207_; 
v_unused_1205_ = lean_ctor_get(v_r_1182_, 4);
lean_dec(v_unused_1205_);
v_unused_1206_ = lean_ctor_get(v_r_1182_, 3);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_r_1182_, 0);
lean_dec(v_unused_1207_);
v___x_1191_ = v_r_1182_;
v_isShared_1192_ = v_isSharedCheck_1204_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_v_1189_);
lean_inc(v_k_1188_);
lean_dec(v_r_1182_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1204_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1193_ = lean_unsigned_to_nat(3u);
v___x_1194_ = lean_unsigned_to_nat(1u);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 4, v_l_1144_);
lean_ctor_set(v___x_1191_, 3, v_l_1144_);
lean_ctor_set(v___x_1191_, 2, v_v_1184_);
lean_ctor_set(v___x_1191_, 1, v_k_1183_);
lean_ctor_set(v___x_1191_, 0, v___x_1194_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_k_1183_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_v_1184_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_l_1144_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_l_1144_);
v___x_1196_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 4, v_l_1144_);
lean_ctor_set(v___x_1186_, 2, v_v_1038_);
lean_ctor_set(v___x_1186_, 1, v_k_1037_);
lean_ctor_set(v___x_1186_, 0, v___x_1194_);
v___x_1198_ = v___x_1186_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_l_1144_);
lean_ctor_set(v_reuseFailAlloc_1202_, 4, v_l_1144_);
v___x_1198_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1198_);
lean_ctor_set(v___x_1042_, 3, v___x_1196_);
lean_ctor_set(v___x_1042_, 2, v_v_1189_);
lean_ctor_set(v___x_1042_, 1, v_k_1188_);
lean_ctor_set(v___x_1042_, 0, v___x_1193_);
v___x_1200_ = v___x_1042_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_k_1188_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_v_1189_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = lean_unsigned_to_nat(2u);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v_r_1182_);
lean_ctor_set(v___x_1042_, 3, v___x_1045_);
lean_ctor_set(v___x_1042_, 0, v___x_1212_);
v___x_1214_ = v___x_1042_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_r_1182_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_unsigned_to_nat(1u);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1045_);
lean_ctor_set(v___x_1042_, 3, v___x_1045_);
lean_ctor_set(v___x_1042_, 0, v___x_1216_);
v___x_1218_ = v___x_1042_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v___x_1045_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
case 1:
{
lean_object* v___x_1221_; 
lean_dec(v_v_1038_);
lean_dec(v_k_1037_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 2, v_v_1034_);
lean_ctor_set(v___x_1042_, 1, v_k_1033_);
v___x_1221_ = v___x_1042_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_size_1036_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_k_1033_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_v_1034_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_l_1039_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_r_1040_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
default: 
{
lean_object* v___x_1223_; 
lean_dec(v_size_1036_);
v___x_1223_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_1033_, v_v_1034_, v_r_1040_);
if (lean_obj_tag(v_l_1039_) == 0)
{
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_size_1224_; lean_object* v_size_1225_; lean_object* v_k_1226_; lean_object* v_v_1227_; lean_object* v_l_1228_; lean_object* v_r_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_size_1224_ = lean_ctor_get(v_l_1039_, 0);
v_size_1225_ = lean_ctor_get(v___x_1223_, 0);
v_k_1226_ = lean_ctor_get(v___x_1223_, 1);
v_v_1227_ = lean_ctor_get(v___x_1223_, 2);
v_l_1228_ = lean_ctor_get(v___x_1223_, 3);
lean_inc(v_l_1228_);
v_r_1229_ = lean_ctor_get(v___x_1223_, 4);
v___x_1230_ = lean_unsigned_to_nat(3u);
v___x_1231_ = lean_nat_mul(v___x_1230_, v_size_1224_);
v___x_1232_ = lean_nat_dec_lt(v___x_1231_, v_size_1225_);
lean_dec(v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
lean_dec(v_l_1228_);
v___x_1233_ = lean_unsigned_to_nat(1u);
v___x_1234_ = lean_nat_add(v___x_1233_, v_size_1224_);
v___x_1235_ = lean_nat_add(v___x_1234_, v_size_1225_);
lean_dec(v___x_1234_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1223_);
lean_ctor_set(v___x_1042_, 0, v___x_1235_);
v___x_1237_ = v___x_1042_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1238_, 3, v_l_1039_);
lean_ctor_set(v_reuseFailAlloc_1238_, 4, v___x_1223_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
else
{
lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1308_; 
lean_inc(v_r_1229_);
lean_inc(v_v_1227_);
lean_inc(v_k_1226_);
lean_inc(v_size_1225_);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; lean_object* v_unused_1310_; lean_object* v_unused_1311_; lean_object* v_unused_1312_; lean_object* v_unused_1313_; 
v_unused_1309_ = lean_ctor_get(v___x_1223_, 4);
lean_dec(v_unused_1309_);
v_unused_1310_ = lean_ctor_get(v___x_1223_, 3);
lean_dec(v_unused_1310_);
v_unused_1311_ = lean_ctor_get(v___x_1223_, 2);
lean_dec(v_unused_1311_);
v_unused_1312_ = lean_ctor_get(v___x_1223_, 1);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v___x_1223_, 0);
lean_dec(v_unused_1313_);
v___x_1240_ = v___x_1223_;
v_isShared_1241_ = v_isSharedCheck_1308_;
goto v_resetjp_1239_;
}
else
{
lean_dec(v___x_1223_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1308_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
if (lean_obj_tag(v_l_1228_) == 0)
{
if (lean_obj_tag(v_r_1229_) == 0)
{
lean_object* v_size_1242_; lean_object* v_k_1243_; lean_object* v_v_1244_; lean_object* v_l_1245_; lean_object* v_r_1246_; lean_object* v_size_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_size_1242_ = lean_ctor_get(v_l_1228_, 0);
v_k_1243_ = lean_ctor_get(v_l_1228_, 1);
v_v_1244_ = lean_ctor_get(v_l_1228_, 2);
v_l_1245_ = lean_ctor_get(v_l_1228_, 3);
v_r_1246_ = lean_ctor_get(v_l_1228_, 4);
v_size_1247_ = lean_ctor_get(v_r_1229_, 0);
v___x_1248_ = lean_unsigned_to_nat(2u);
v___x_1249_ = lean_nat_mul(v___x_1248_, v_size_1247_);
v___x_1250_ = lean_nat_dec_lt(v_size_1242_, v___x_1249_);
lean_dec(v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1279_; 
lean_inc(v_r_1246_);
lean_inc(v_l_1245_);
lean_inc(v_v_1244_);
lean_inc(v_k_1243_);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_l_1228_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; lean_object* v_unused_1281_; lean_object* v_unused_1282_; lean_object* v_unused_1283_; lean_object* v_unused_1284_; 
v_unused_1280_ = lean_ctor_get(v_l_1228_, 4);
lean_dec(v_unused_1280_);
v_unused_1281_ = lean_ctor_get(v_l_1228_, 3);
lean_dec(v_unused_1281_);
v_unused_1282_ = lean_ctor_get(v_l_1228_, 2);
lean_dec(v_unused_1282_);
v_unused_1283_ = lean_ctor_get(v_l_1228_, 1);
lean_dec(v_unused_1283_);
v_unused_1284_ = lean_ctor_get(v_l_1228_, 0);
lean_dec(v_unused_1284_);
v___x_1252_ = v_l_1228_;
v_isShared_1253_ = v_isSharedCheck_1279_;
goto v_resetjp_1251_;
}
else
{
lean_dec(v_l_1228_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1279_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1269_; 
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = lean_nat_add(v___x_1254_, v_size_1224_);
v___x_1256_ = lean_nat_add(v___x_1255_, v_size_1225_);
lean_dec(v_size_1225_);
if (lean_obj_tag(v_l_1245_) == 0)
{
lean_object* v_size_1277_; 
v_size_1277_ = lean_ctor_get(v_l_1245_, 0);
lean_inc(v_size_1277_);
v___y_1269_ = v_size_1277_;
goto v___jp_1268_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_unsigned_to_nat(0u);
v___y_1269_ = v___x_1278_;
goto v___jp_1268_;
}
v___jp_1257_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_nat_add(v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec(v___y_1259_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 4, v_r_1229_);
lean_ctor_set(v___x_1252_, 3, v_r_1246_);
lean_ctor_set(v___x_1252_, 2, v_v_1227_);
lean_ctor_set(v___x_1252_, 1, v_k_1226_);
lean_ctor_set(v___x_1252_, 0, v___x_1261_);
v___x_1263_ = v___x_1252_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_r_1246_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_r_1229_);
v___x_1263_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1265_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 4, v___x_1263_);
lean_ctor_set(v___x_1240_, 3, v___y_1258_);
lean_ctor_set(v___x_1240_, 2, v_v_1244_);
lean_ctor_set(v___x_1240_, 1, v_k_1243_);
lean_ctor_set(v___x_1240_, 0, v___x_1256_);
v___x_1265_ = v___x_1240_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_k_1243_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v_v_1244_);
lean_ctor_set(v_reuseFailAlloc_1266_, 3, v___y_1258_);
lean_ctor_set(v_reuseFailAlloc_1266_, 4, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
v___jp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_nat_add(v___x_1255_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec(v___x_1255_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v_l_1245_);
lean_ctor_set(v___x_1042_, 0, v___x_1270_);
v___x_1272_ = v___x_1042_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_l_1039_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v_l_1245_);
v___x_1272_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_nat_add(v___x_1254_, v_size_1247_);
if (lean_obj_tag(v_r_1246_) == 0)
{
lean_object* v_size_1274_; 
v_size_1274_ = lean_ctor_get(v_r_1246_, 0);
lean_inc(v_size_1274_);
v___y_1258_ = v___x_1272_;
v___y_1259_ = v___x_1273_;
v___y_1260_ = v_size_1274_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_unsigned_to_nat(0u);
v___y_1258_ = v___x_1272_;
v___y_1259_ = v___x_1273_;
v___y_1260_ = v___x_1275_;
goto v___jp_1257_;
}
}
}
}
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
lean_del_object(v___x_1042_);
v___x_1285_ = lean_unsigned_to_nat(1u);
v___x_1286_ = lean_nat_add(v___x_1285_, v_size_1224_);
v___x_1287_ = lean_nat_add(v___x_1286_, v_size_1225_);
lean_dec(v_size_1225_);
v___x_1288_ = lean_nat_add(v___x_1286_, v_size_1242_);
lean_dec(v___x_1286_);
lean_inc_ref(v_l_1039_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 4, v_l_1228_);
lean_ctor_set(v___x_1240_, 3, v_l_1039_);
lean_ctor_set(v___x_1240_, 2, v_v_1038_);
lean_ctor_set(v___x_1240_, 1, v_k_1037_);
lean_ctor_set(v___x_1240_, 0, v___x_1288_);
v___x_1290_ = v___x_1240_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_l_1039_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_l_1228_);
v___x_1290_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
v_isSharedCheck_1297_ = !lean_is_exclusive(v_l_1039_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; lean_object* v_unused_1299_; lean_object* v_unused_1300_; lean_object* v_unused_1301_; lean_object* v_unused_1302_; 
v_unused_1298_ = lean_ctor_get(v_l_1039_, 4);
lean_dec(v_unused_1298_);
v_unused_1299_ = lean_ctor_get(v_l_1039_, 3);
lean_dec(v_unused_1299_);
v_unused_1300_ = lean_ctor_get(v_l_1039_, 2);
lean_dec(v_unused_1300_);
v_unused_1301_ = lean_ctor_get(v_l_1039_, 1);
lean_dec(v_unused_1301_);
v_unused_1302_ = lean_ctor_get(v_l_1039_, 0);
lean_dec(v_unused_1302_);
v___x_1292_ = v_l_1039_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_dec(v_l_1039_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v_r_1229_);
lean_ctor_set(v___x_1292_, 3, v___x_1290_);
lean_ctor_set(v___x_1292_, 2, v_v_1227_);
lean_ctor_set(v___x_1292_, 1, v_k_1226_);
lean_ctor_set(v___x_1292_, 0, v___x_1287_);
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_r_1229_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
else
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec_ref_known(v_l_1228_, 5);
lean_del_object(v___x_1240_);
lean_dec(v_v_1227_);
lean_dec(v_k_1226_);
lean_dec(v_size_1225_);
lean_dec_ref_known(v_l_1039_, 5);
lean_del_object(v___x_1042_);
lean_dec(v_v_1038_);
lean_dec(v_k_1037_);
v___x_1304_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7);
v___x_1305_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1304_);
return v___x_1305_;
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_del_object(v___x_1240_);
lean_dec(v_r_1229_);
lean_dec(v_v_1227_);
lean_dec(v_k_1226_);
lean_dec(v_size_1225_);
lean_dec_ref_known(v_l_1039_, 5);
lean_del_object(v___x_1042_);
lean_dec(v_v_1038_);
lean_dec(v_k_1037_);
v___x_1306_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8);
v___x_1307_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1306_);
return v___x_1307_;
}
}
}
}
else
{
lean_object* v_size_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
v_size_1314_ = lean_ctor_get(v_l_1039_, 0);
v___x_1315_ = lean_unsigned_to_nat(1u);
v___x_1316_ = lean_nat_add(v___x_1315_, v_size_1314_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1223_);
lean_ctor_set(v___x_1042_, 0, v___x_1316_);
v___x_1318_ = v___x_1042_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_l_1039_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v___x_1223_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
else
{
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_l_1320_; 
v_l_1320_ = lean_ctor_get(v___x_1223_, 3);
lean_inc(v_l_1320_);
if (lean_obj_tag(v_l_1320_) == 0)
{
lean_object* v_r_1321_; 
v_r_1321_ = lean_ctor_get(v___x_1223_, 4);
lean_inc(v_r_1321_);
if (lean_obj_tag(v_r_1321_) == 0)
{
lean_object* v_size_1322_; lean_object* v_k_1323_; lean_object* v_v_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1338_; 
v_size_1322_ = lean_ctor_get(v___x_1223_, 0);
v_k_1323_ = lean_ctor_get(v___x_1223_, 1);
v_v_1324_ = lean_ctor_get(v___x_1223_, 2);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; lean_object* v_unused_1340_; 
v_unused_1339_ = lean_ctor_get(v___x_1223_, 4);
lean_dec(v_unused_1339_);
v_unused_1340_ = lean_ctor_get(v___x_1223_, 3);
lean_dec(v_unused_1340_);
v___x_1326_ = v___x_1223_;
v_isShared_1327_ = v_isSharedCheck_1338_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_v_1324_);
lean_inc(v_k_1323_);
lean_inc(v_size_1322_);
lean_dec(v___x_1223_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1338_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v_size_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v_size_1328_ = lean_ctor_get(v_l_1320_, 0);
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_nat_add(v___x_1329_, v_size_1322_);
lean_dec(v_size_1322_);
v___x_1331_ = lean_nat_add(v___x_1329_, v_size_1328_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 4, v_l_1320_);
lean_ctor_set(v___x_1326_, 3, v_l_1039_);
lean_ctor_set(v___x_1326_, 2, v_v_1038_);
lean_ctor_set(v___x_1326_, 1, v_k_1037_);
lean_ctor_set(v___x_1326_, 0, v___x_1331_);
v___x_1333_ = v___x_1326_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1337_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1337_, 3, v_l_1039_);
lean_ctor_set(v_reuseFailAlloc_1337_, 4, v_l_1320_);
v___x_1333_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1335_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v_r_1321_);
lean_ctor_set(v___x_1042_, 3, v___x_1333_);
lean_ctor_set(v___x_1042_, 2, v_v_1324_);
lean_ctor_set(v___x_1042_, 1, v_k_1323_);
lean_ctor_set(v___x_1042_, 0, v___x_1330_);
v___x_1335_ = v___x_1042_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_k_1323_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_v_1324_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1336_, 4, v_r_1321_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_k_1341_; lean_object* v_v_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1366_; 
v_k_1341_ = lean_ctor_get(v___x_1223_, 1);
v_v_1342_ = lean_ctor_get(v___x_1223_, 2);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; lean_object* v_unused_1368_; lean_object* v_unused_1369_; 
v_unused_1367_ = lean_ctor_get(v___x_1223_, 4);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v___x_1223_, 3);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v___x_1223_, 0);
lean_dec(v_unused_1369_);
v___x_1344_ = v___x_1223_;
v_isShared_1345_ = v_isSharedCheck_1366_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_v_1342_);
lean_inc(v_k_1341_);
lean_dec(v___x_1223_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1366_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v_k_1346_; lean_object* v_v_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1362_; 
v_k_1346_ = lean_ctor_get(v_l_1320_, 1);
v_v_1347_ = lean_ctor_get(v_l_1320_, 2);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_l_1320_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; lean_object* v_unused_1364_; lean_object* v_unused_1365_; 
v_unused_1363_ = lean_ctor_get(v_l_1320_, 4);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_l_1320_, 3);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_l_1320_, 0);
lean_dec(v_unused_1365_);
v___x_1349_ = v_l_1320_;
v_isShared_1350_ = v_isSharedCheck_1362_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_v_1347_);
lean_inc(v_k_1346_);
lean_dec(v_l_1320_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1362_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_unsigned_to_nat(3u);
v___x_1352_ = lean_unsigned_to_nat(1u);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 4, v_r_1321_);
lean_ctor_set(v___x_1349_, 3, v_r_1321_);
lean_ctor_set(v___x_1349_, 2, v_v_1038_);
lean_ctor_set(v___x_1349_, 1, v_k_1037_);
lean_ctor_set(v___x_1349_, 0, v___x_1352_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_r_1321_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v_r_1321_);
v___x_1354_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 3, v_r_1321_);
lean_ctor_set(v___x_1344_, 0, v___x_1352_);
v___x_1356_ = v___x_1344_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v_r_1321_);
lean_ctor_set(v_reuseFailAlloc_1360_, 4, v_r_1321_);
v___x_1356_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1356_);
lean_ctor_set(v___x_1042_, 3, v___x_1354_);
lean_ctor_set(v___x_1042_, 2, v_v_1347_);
lean_ctor_set(v___x_1042_, 1, v_k_1346_);
lean_ctor_set(v___x_1042_, 0, v___x_1351_);
v___x_1358_ = v___x_1042_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_k_1346_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_v_1347_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1359_, 4, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1370_; 
v_r_1370_ = lean_ctor_get(v___x_1223_, 4);
lean_inc(v_r_1370_);
if (lean_obj_tag(v_r_1370_) == 0)
{
lean_object* v_k_1371_; lean_object* v_v_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1384_; 
v_k_1371_ = lean_ctor_get(v___x_1223_, 1);
v_v_1372_ = lean_ctor_get(v___x_1223_, 2);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; lean_object* v_unused_1386_; lean_object* v_unused_1387_; 
v_unused_1385_ = lean_ctor_get(v___x_1223_, 4);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v___x_1223_, 3);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v___x_1223_, 0);
lean_dec(v_unused_1387_);
v___x_1374_ = v___x_1223_;
v_isShared_1375_ = v_isSharedCheck_1384_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_v_1372_);
lean_inc(v_k_1371_);
lean_dec(v___x_1223_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1384_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1376_ = lean_unsigned_to_nat(3u);
v___x_1377_ = lean_unsigned_to_nat(1u);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 4, v_l_1320_);
lean_ctor_set(v___x_1374_, 2, v_v_1038_);
lean_ctor_set(v___x_1374_, 1, v_k_1037_);
lean_ctor_set(v___x_1374_, 0, v___x_1377_);
v___x_1379_ = v___x_1374_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v_l_1320_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v_l_1320_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1381_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v_r_1370_);
lean_ctor_set(v___x_1042_, 3, v___x_1379_);
lean_ctor_set(v___x_1042_, 2, v_v_1372_);
lean_ctor_set(v___x_1042_, 1, v_k_1371_);
lean_ctor_set(v___x_1042_, 0, v___x_1376_);
v___x_1381_ = v___x_1042_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v_r_1370_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = lean_unsigned_to_nat(2u);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1223_);
lean_ctor_set(v___x_1042_, 3, v_r_1370_);
lean_ctor_set(v___x_1042_, 0, v___x_1388_);
v___x_1390_ = v___x_1042_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_r_1370_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v___x_1223_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = lean_unsigned_to_nat(1u);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1223_);
lean_ctor_set(v___x_1042_, 3, v___x_1223_);
lean_ctor_set(v___x_1042_, 0, v___x_1392_);
v___x_1394_ = v___x_1042_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_k_1037_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_v_1038_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v___x_1223_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v_k_1033_);
lean_ctor_set(v___x_1398_, 2, v_v_1034_);
lean_ctor_set(v___x_1398_, 3, v_t_1035_);
lean_ctor_set(v___x_1398_, 4, v_t_1035_);
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(lean_object* v_init_1399_, lean_object* v_x_1400_){
_start:
{
if (lean_obj_tag(v_x_1400_) == 0)
{
lean_object* v_k_1401_; lean_object* v_v_1402_; lean_object* v_l_1403_; lean_object* v_r_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_k_1401_ = lean_ctor_get(v_x_1400_, 1);
lean_inc(v_k_1401_);
v_v_1402_ = lean_ctor_get(v_x_1400_, 2);
lean_inc(v_v_1402_);
v_l_1403_ = lean_ctor_get(v_x_1400_, 3);
lean_inc(v_l_1403_);
v_r_1404_ = lean_ctor_get(v_x_1400_, 4);
lean_inc(v_r_1404_);
lean_dec_ref_known(v_x_1400_, 5);
v___x_1405_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v_init_1399_, v_l_1403_);
v___x_1406_ = 1;
v___x_1407_ = l_Lean_Name_toString(v_k_1401_, v___x_1406_);
v___x_1408_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1408_, 0, v_v_1402_);
v___x_1409_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v___x_1407_, v___x_1408_, v___x_1405_);
v_init_1399_ = v___x_1409_;
v_x_1400_ = v_r_1404_;
goto _start;
}
else
{
return v_init_1399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(lean_object* v_m_1411_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = lean_box(1);
v___x_1413_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v___x_1412_, v_m_1411_);
v___x_1414_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object* v_env_1420_){
_start:
{
lean_object* v_lake_1421_; lean_object* v_lean_1422_; lean_object* v_elan_x3f_1423_; lean_object* v_pkgUrlMap_1424_; uint8_t v_noCache_1425_; lean_object* v_lakeConfig_x3f_1426_; lean_object* v_cacheKey_x3f_1427_; lean_object* v_cacheArtifactEndpoint_x3f_1428_; lean_object* v_cacheRevisionEndpoint_x3f_1429_; lean_object* v_cacheService_x3f_1430_; lean_object* v_toolchain_1431_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___x_1560_; lean_object* v___y_1562_; 
v_lake_1421_ = lean_ctor_get(v_env_1420_, 0);
lean_inc_ref(v_lake_1421_);
v_lean_1422_ = lean_ctor_get(v_env_1420_, 1);
lean_inc_ref(v_lean_1422_);
v_elan_x3f_1423_ = lean_ctor_get(v_env_1420_, 2);
lean_inc(v_elan_x3f_1423_);
v_pkgUrlMap_1424_ = lean_ctor_get(v_env_1420_, 5);
lean_inc(v_pkgUrlMap_1424_);
v_noCache_1425_ = lean_ctor_get_uint8(v_env_1420_, sizeof(void*)*20);
v_lakeConfig_x3f_1426_ = lean_ctor_get(v_env_1420_, 10);
lean_inc(v_lakeConfig_x3f_1426_);
v_cacheKey_x3f_1427_ = lean_ctor_get(v_env_1420_, 11);
lean_inc(v_cacheKey_x3f_1427_);
v_cacheArtifactEndpoint_x3f_1428_ = lean_ctor_get(v_env_1420_, 12);
lean_inc(v_cacheArtifactEndpoint_x3f_1428_);
v_cacheRevisionEndpoint_x3f_1429_ = lean_ctor_get(v_env_1420_, 13);
lean_inc(v_cacheRevisionEndpoint_x3f_1429_);
v_cacheService_x3f_1430_ = lean_ctor_get(v_env_1420_, 14);
lean_inc(v_cacheService_x3f_1430_);
v_toolchain_1431_ = lean_ctor_get(v_env_1420_, 19);
lean_inc_ref(v_toolchain_1431_);
lean_dec_ref(v_env_1420_);
v___x_1560_ = ((lean_object*)(l_Lake_Env_baseVars___closed__3));
if (lean_obj_tag(v_elan_x3f_1423_) == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_box(0);
v___y_1562_ = v___x_1575_;
goto v___jp_1561_;
}
else
{
lean_object* v_val_1576_; lean_object* v_elan_1577_; lean_object* v___x_1578_; 
v_val_1576_ = lean_ctor_get(v_elan_x3f_1423_, 0);
v_elan_1577_ = lean_ctor_get(v_val_1576_, 1);
lean_inc_ref(v_elan_1577_);
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v_elan_1577_);
v___y_1562_ = v___x_1578_;
goto v___jp_1561_;
}
v___jp_1432_:
{
lean_object* v_sysroot_1446_; lean_object* v_lean_1447_; lean_object* v_ar_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_sysroot_1446_ = lean_ctor_get(v_lean_1422_, 0);
v_lean_1447_ = lean_ctor_get(v_lean_1422_, 7);
v_ar_1448_ = lean_ctor_get(v_lean_1422_, 13);
lean_inc_ref(v___y_1444_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1444_);
lean_ctor_set(v___x_1449_, 1, v___y_1445_);
v___x_1450_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__7));
lean_inc_ref(v_lean_1447_);
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_lean_1447_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__10));
lean_inc_ref(v_sysroot_1446_);
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_sysroot_1446_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__12));
lean_inc_ref(v_ar_1448_);
v___x_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_ar_1448_);
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = ((lean_object*)(l_Lake_Env_baseVars___closed__0));
v___x_1460_ = l_Lake_LeanInstall_leanCc_x3f(v_lean_1422_);
lean_dec_ref(v_lean_1422_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_unsigned_to_nat(16u);
v___x_1463_ = lean_mk_empty_array_with_capacity(v___x_1462_);
v___x_1464_ = lean_array_push(v___x_1463_, v___y_1442_);
v___x_1465_ = lean_array_push(v___x_1464_, v___y_1440_);
v___x_1466_ = lean_array_push(v___x_1465_, v___y_1436_);
v___x_1467_ = lean_array_push(v___x_1466_, v___y_1441_);
v___x_1468_ = lean_array_push(v___x_1467_, v___y_1443_);
v___x_1469_ = lean_array_push(v___x_1468_, v___y_1439_);
v___x_1470_ = lean_array_push(v___x_1469_, v___y_1435_);
v___x_1471_ = lean_array_push(v___x_1470_, v___y_1433_);
v___x_1472_ = lean_array_push(v___x_1471_, v___y_1438_);
v___x_1473_ = lean_array_push(v___x_1472_, v___y_1434_);
v___x_1474_ = lean_array_push(v___x_1473_, v___y_1437_);
v___x_1475_ = lean_array_push(v___x_1474_, v___x_1449_);
v___x_1476_ = lean_array_push(v___x_1475_, v___x_1452_);
v___x_1477_ = lean_array_push(v___x_1476_, v___x_1455_);
v___x_1478_ = lean_array_push(v___x_1477_, v___x_1458_);
v___x_1479_ = lean_array_push(v___x_1478_, v___x_1461_);
return v___x_1479_;
}
v___jp_1480_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_inc_ref(v___y_1489_);
v___x_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1489_);
lean_inc_ref(v___y_1485_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___y_1485_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = ((lean_object*)(l_Lake_Env_compute___closed__6));
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
lean_ctor_set(v___x_1493_, 1, v_cacheKey_x3f_1427_);
v___x_1494_ = ((lean_object*)(l_Lake_Env_compute___closed__7));
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v_cacheArtifactEndpoint_x3f_1428_);
v___x_1496_ = ((lean_object*)(l_Lake_Env_compute___closed__8));
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v_cacheRevisionEndpoint_x3f_1429_);
v___x_1498_ = ((lean_object*)(l_Lake_Env_compute___closed__9));
if (lean_obj_tag(v_cacheService_x3f_1430_) == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_box(0);
v___y_1433_ = v___x_1491_;
v___y_1434_ = v___x_1495_;
v___y_1435_ = v___y_1482_;
v___y_1436_ = v___y_1481_;
v___y_1437_ = v___x_1497_;
v___y_1438_ = v___x_1493_;
v___y_1439_ = v___y_1483_;
v___y_1440_ = v___y_1484_;
v___y_1441_ = v___y_1486_;
v___y_1442_ = v___y_1487_;
v___y_1443_ = v___y_1488_;
v___y_1444_ = v___x_1498_;
v___y_1445_ = v___x_1499_;
goto v___jp_1432_;
}
else
{
lean_object* v_val_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_val_1500_ = lean_ctor_get(v_cacheService_x3f_1430_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_cacheService_x3f_1430_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v_cacheService_x3f_1430_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_val_1500_);
lean_dec(v_cacheService_x3f_1430_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_val_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
v___y_1433_ = v___x_1491_;
v___y_1434_ = v___x_1495_;
v___y_1435_ = v___y_1482_;
v___y_1436_ = v___y_1481_;
v___y_1437_ = v___x_1497_;
v___y_1438_ = v___x_1493_;
v___y_1439_ = v___y_1483_;
v___y_1440_ = v___y_1484_;
v___y_1441_ = v___y_1486_;
v___y_1442_ = v___y_1487_;
v___y_1443_ = v___y_1488_;
v___y_1444_ = v___x_1498_;
v___y_1445_ = v___x_1505_;
goto v___jp_1432_;
}
}
}
}
v___jp_1508_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_inc_ref(v___y_1512_);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___y_1512_);
lean_ctor_set(v___x_1516_, 1, v___y_1515_);
v___x_1517_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0));
v___x_1518_ = l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(v_pkgUrlMap_1424_);
v___x_1519_ = l_Lean_Json_compress(v___x_1518_);
v___x_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1517_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = ((lean_object*)(l_Lake_Env_compute___closed__2));
if (v_noCache_1425_ == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = ((lean_object*)(l_Lake_Env_baseVars___closed__1));
v___y_1481_ = v___y_1509_;
v___y_1482_ = v___x_1521_;
v___y_1483_ = v___x_1516_;
v___y_1484_ = v___y_1510_;
v___y_1485_ = v___x_1522_;
v___y_1486_ = v___y_1511_;
v___y_1487_ = v___y_1513_;
v___y_1488_ = v___y_1514_;
v___y_1489_ = v___x_1523_;
goto v___jp_1480_;
}
else
{
lean_object* v___x_1524_; 
v___x_1524_ = ((lean_object*)(l_Lake_Env_baseVars___closed__2));
v___y_1481_ = v___y_1509_;
v___y_1482_ = v___x_1521_;
v___y_1483_ = v___x_1516_;
v___y_1484_ = v___y_1510_;
v___y_1485_ = v___x_1522_;
v___y_1486_ = v___y_1511_;
v___y_1487_ = v___y_1513_;
v___y_1488_ = v___y_1514_;
v___y_1489_ = v___x_1524_;
goto v___jp_1480_;
}
}
v___jp_1525_:
{
lean_object* v_home_1530_; lean_object* v_lake_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_home_1530_ = lean_ctor_get(v_lake_1421_, 0);
lean_inc_ref(v_home_1530_);
v_lake_1531_ = lean_ctor_get(v_lake_1421_, 5);
lean_inc_ref(v_lake_1531_);
lean_dec_ref(v_lake_1421_);
lean_inc_ref(v___y_1528_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___y_1528_);
lean_ctor_set(v___x_1532_, 1, v___y_1529_);
v___x_1533_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__1));
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_lake_1531_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__5));
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_home_1530_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = ((lean_object*)(l_Lake_Env_compute___closed__5));
if (lean_obj_tag(v_lakeConfig_x3f_1426_) == 1)
{
lean_object* v_val_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
v_val_1540_ = lean_ctor_get(v_lakeConfig_x3f_1426_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_lakeConfig_x3f_1426_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v_lakeConfig_x3f_1426_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_val_1540_);
lean_dec(v_lakeConfig_x3f_1426_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_val_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
v___y_1509_ = v___x_1532_;
v___y_1510_ = v___y_1526_;
v___y_1511_ = v___x_1535_;
v___y_1512_ = v___x_1539_;
v___y_1513_ = v___y_1527_;
v___y_1514_ = v___x_1538_;
v___y_1515_ = v___x_1545_;
goto v___jp_1508_;
}
}
}
else
{
lean_object* v___x_1548_; 
lean_dec(v_lakeConfig_x3f_1426_);
v___x_1548_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_1509_ = v___x_1532_;
v___y_1510_ = v___y_1526_;
v___y_1511_ = v___x_1535_;
v___y_1512_ = v___x_1539_;
v___y_1513_ = v___y_1527_;
v___y_1514_ = v___x_1538_;
v___y_1515_ = v___x_1548_;
goto v___jp_1508_;
}
}
v___jp_1549_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
lean_inc_ref(v___y_1551_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___y_1551_);
lean_ctor_set(v___x_1553_, 1, v___y_1552_);
v___x_1554_ = ((lean_object*)(l_Lake_Env_computeToolchain___closed__0));
v___x_1555_ = lean_string_utf8_byte_size(v_toolchain_1431_);
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = lean_nat_dec_eq(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_toolchain_1431_);
v___y_1526_ = v___x_1553_;
v___y_1527_ = v___y_1550_;
v___y_1528_ = v___x_1554_;
v___y_1529_ = v___x_1558_;
goto v___jp_1525_;
}
else
{
lean_object* v___x_1559_; 
lean_dec_ref(v_toolchain_1431_);
v___x_1559_ = lean_box(0);
v___y_1526_ = v___x_1553_;
v___y_1527_ = v___y_1550_;
v___y_1528_ = v___x_1554_;
v___y_1529_ = v___x_1559_;
goto v___jp_1525_;
}
}
v___jp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1560_);
lean_ctor_set(v___x_1563_, 1, v___y_1562_);
v___x_1564_ = ((lean_object*)(l_Lake_Env_baseVars___closed__4));
if (lean_obj_tag(v_elan_x3f_1423_) == 0)
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_box(0);
v___y_1550_ = v___x_1563_;
v___y_1551_ = v___x_1564_;
v___y_1552_ = v___x_1565_;
goto v___jp_1549_;
}
else
{
lean_object* v_val_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1574_; 
v_val_1566_ = lean_ctor_get(v_elan_x3f_1423_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_elan_x3f_1423_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1568_ = v_elan_x3f_1423_;
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_val_1566_);
lean_dec(v_elan_x3f_1423_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_home_1570_; lean_object* v___x_1572_; 
v_home_1570_ = lean_ctor_get(v_val_1566_, 0);
lean_inc_ref(v_home_1570_);
lean_dec(v_val_1566_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v_home_1570_);
v___x_1572_ = v___x_1568_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_home_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
v___y_1550_ = v___x_1563_;
v___y_1551_ = v___x_1564_;
v___y_1552_ = v___x_1572_;
goto v___jp_1549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1579_, lean_object* v_msg_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v_msg_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(lean_object* v_00_u03b2_1582_, lean_object* v_k_1583_, lean_object* v_v_1584_, lean_object* v_t_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_1583_, v_v_1584_, v_t_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(lean_object* v_init_1587_, lean_object* v_t_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v_init_1587_, v_t_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__0(lean_object* v_x_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__0___boxed(lean_object* v_x_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lake_Env_vars___lam__0(v_x_1592_);
lean_dec(v_x_1592_);
return v_res_1593_;
}
}
lean_object* l_Lake_Env_vars___lam__1(uint8_t v_b_1598_){
_start:
{
if (v_b_1598_ == 0)
{
lean_object* v___x_1599_; 
v___x_1599_ = ((lean_object*)(l_Lake_Env_vars___lam__1___closed__0));
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; 
v___x_1600_ = ((lean_object*)(l_Lake_Env_vars___lam__1___closed__1));
return v___x_1600_;
}
}
}
LEAN_EXPORT void l_Lake_Env_vars___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_1598_ = stack[0].m_num;
lean_object* v_res_1601_;
v_res_1601_ = l_Lake_Env_vars___lam__1(v_b_1598_);
stack->m_obj
 = v_res_1601_;
}
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__1___boxed(lean_object* v_b_1602_){
_start:
{
uint8_t v_b_boxed_1603_; lean_object* v_res_1604_; 
v_b_boxed_1603_ = lean_unbox(v_b_1602_);
v_res_1604_ = l_Lake_Env_vars___lam__1(v_b_boxed_1603_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object* v_env_1605_){
_start:
{
lean_object* v_enableArtifactCache_x3f_1606_; lean_object* v_restoreAllArtifacts_x3f_1607_; lean_object* v_lakeCache_x3f_1608_; lean_object* v___x_1609_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___x_1662_; lean_object* v___y_1664_; 
v_enableArtifactCache_x3f_1606_ = lean_ctor_get(v_env_1605_, 6);
v_restoreAllArtifacts_x3f_1607_ = lean_ctor_get(v_env_1605_, 7);
v_lakeCache_x3f_1608_ = lean_ctor_get(v_env_1605_, 8);
lean_inc(v_lakeCache_x3f_1608_);
lean_inc_ref(v_env_1605_);
v___x_1609_ = l_Lake_Env_baseVars(v_env_1605_);
v___x_1662_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
if (lean_obj_tag(v_lakeCache_x3f_1608_) == 1)
{
lean_object* v_val_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
v_val_1671_ = lean_ctor_get(v_lakeCache_x3f_1608_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_lakeCache_x3f_1608_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v_lakeCache_x3f_1608_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_val_1671_);
lean_dec(v_lakeCache_x3f_1608_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_val_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
v___y_1664_ = v___x_1676_;
goto v___jp_1663_;
}
}
}
else
{
lean_object* v___x_1679_; 
lean_dec(v_lakeCache_x3f_1608_);
v___x_1679_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_1664_ = v___x_1679_;
goto v___jp_1663_;
}
v___jp_1610_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_vars_1644_; uint8_t v___x_1645_; 
lean_inc_ref(v___y_1613_);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___y_1613_);
lean_ctor_set(v___x_1615_, 1, v___y_1614_);
v___x_1616_ = ((lean_object*)(l_Lake_Env_compute___closed__11));
v___x_1617_ = l_Lake_Env_leanPath(v_env_1605_);
v___x_1618_ = l_System_SearchPath_toString(v___x_1617_);
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1616_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = ((lean_object*)(l_Lake_Env_compute___closed__12));
v___x_1622_ = l_Lake_Env_leanSrcPath(v_env_1605_);
v___x_1623_ = l_System_SearchPath_toString(v___x_1622_);
v___x_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1621_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = ((lean_object*)(l_Lake_Env_compute___closed__10));
v___x_1627_ = l_Lake_Env_leanGithash(v_env_1605_);
v___x_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1626_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = ((lean_object*)(l_Lake_Env_compute___closed__13));
v___x_1631_ = l_Lake_Env_path(v_env_1605_);
v___x_1632_ = l_System_SearchPath_toString(v___x_1631_);
v___x_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1630_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_unsigned_to_nat(7u);
v___x_1636_ = lean_mk_empty_array_with_capacity(v___x_1635_);
v___x_1637_ = lean_array_push(v___x_1636_, v___y_1611_);
v___x_1638_ = lean_array_push(v___x_1637_, v___y_1612_);
v___x_1639_ = lean_array_push(v___x_1638_, v___x_1615_);
v___x_1640_ = lean_array_push(v___x_1639_, v___x_1620_);
v___x_1641_ = lean_array_push(v___x_1640_, v___x_1625_);
v___x_1642_ = lean_array_push(v___x_1641_, v___x_1629_);
v___x_1643_ = lean_array_push(v___x_1642_, v___x_1634_);
v_vars_1644_ = l_Array_append___redArg(v___x_1609_, v___x_1643_);
lean_dec_ref(v___x_1643_);
v___x_1645_ = l_System_Platform_isWindows;
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1646_ = l_Lake_sharedLibPathEnvVar;
v___x_1647_ = l_Lake_Env_sharedLibPath(v_env_1605_);
v___x_1648_ = l_System_SearchPath_toString(v___x_1647_);
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1646_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_array_push(v_vars_1644_, v___x_1650_);
return v___x_1651_;
}
else
{
lean_dec_ref(v_env_1605_);
return v_vars_1644_;
}
}
v___jp_1652_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_inc_ref(v___y_1654_);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___y_1654_);
lean_ctor_set(v___x_1656_, 1, v___y_1655_);
v___x_1657_ = ((lean_object*)(l_Lake_Env_compute___closed__4));
if (lean_obj_tag(v_restoreAllArtifacts_x3f_1607_) == 1)
{
lean_object* v_val_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; 
v_val_1658_ = lean_ctor_get(v_restoreAllArtifacts_x3f_1607_, 0);
v___x_1659_ = lean_unbox(v_val_1658_);
v___x_1660_ = l_Lake_Env_vars___lam__1(v___x_1659_);
v___y_1611_ = v___y_1653_;
v___y_1612_ = v___x_1656_;
v___y_1613_ = v___x_1657_;
v___y_1614_ = v___x_1660_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lake_Env_vars___lam__0(v_restoreAllArtifacts_x3f_1607_);
v___y_1611_ = v___y_1653_;
v___y_1612_ = v___x_1656_;
v___y_1613_ = v___x_1657_;
v___y_1614_ = v___x_1661_;
goto v___jp_1610_;
}
}
v___jp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1662_);
lean_ctor_set(v___x_1665_, 1, v___y_1664_);
v___x_1666_ = ((lean_object*)(l_Lake_Env_compute___closed__3));
if (lean_obj_tag(v_enableArtifactCache_x3f_1606_) == 1)
{
lean_object* v_val_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; 
v_val_1667_ = lean_ctor_get(v_enableArtifactCache_x3f_1606_, 0);
v___x_1668_ = lean_unbox(v_val_1667_);
v___x_1669_ = l_Lake_Env_vars___lam__1(v___x_1668_);
v___y_1653_ = v___x_1665_;
v___y_1654_ = v___x_1666_;
v___y_1655_ = v___x_1669_;
goto v___jp_1652_;
}
else
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lake_Env_vars___lam__0(v_enableArtifactCache_x3f_1606_);
v___y_1653_ = v___x_1665_;
v___y_1654_ = v___x_1666_;
v___y_1655_ = v___x_1670_;
goto v___jp_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object* v_env_1680_){
_start:
{
lean_object* v_lake_1681_; lean_object* v_lean_1682_; lean_object* v_libDir_1683_; lean_object* v_leanLibDir_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_lake_1681_ = lean_ctor_get(v_env_1680_, 0);
v_lean_1682_ = lean_ctor_get(v_env_1680_, 1);
v_libDir_1683_ = lean_ctor_get(v_lake_1681_, 3);
v_leanLibDir_1684_ = lean_ctor_get(v_lean_1682_, 3);
v___x_1685_ = l_Lake_Env_leanPath(v_env_1680_);
lean_inc_ref(v_leanLibDir_1684_);
v___x_1686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_leanLibDir_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
lean_inc_ref(v_libDir_1683_);
v___x_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_libDir_1683_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object* v_env_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lake_Env_leanSearchPath(v_env_1688_);
lean_dec_ref(v_env_1688_);
return v_res_1689_;
}
}
lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
