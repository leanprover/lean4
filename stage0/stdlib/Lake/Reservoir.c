// Lean compiler output
// Module: Lake.Reservoir
// Imports: Lake.Util.Log Lake.Util.JsonObject Lake.Config.Env Lake.Util.Proc Init.Data.String.Extra
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__5;
LEAN_EXPORT lean_object* l_Lake_uriEncode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__7;
static lean_object* l_Lake_foldlUtf8___redArg___closed__7;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_fromJson_x3f(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__3;
static lean_object* l_Lake_Reservoir_fetchPkg_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_uriEncode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar(uint32_t, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_foldlUtf8___redArg___closed__1;
uint8_t lean_uint8_lor(uint8_t, uint8_t);
static lean_object* l_Option_fromJson_x3f___at___Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_ReservoirResp_fromJson_x3f___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data___boxed(lean_object*);
static lean_object* l_Lake_getUrl___closed__8;
static lean_object* l_Lake_foldlUtf8___redArg___closed__0;
static lean_object* l_Lake_Reservoir_pkgApiUrl___closed__0;
static lean_object* l_Lake_instInhabitedRegistryPkg___closed__1;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_hexEncodeByte___boxed(lean_object*);
static lean_object* l_Lake_foldlUtf8___redArg___closed__8;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte(uint8_t, lean_object*);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_RegistryPkg_gitSrc_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1(uint32_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__10;
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_instFromJson;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Reservoir_lakeHeaders;
uint8_t lean_uint8_land(uint8_t, uint8_t);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6;
static lean_object* l_Lake_foldlUtf8___redArg___closed__9;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__5;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__2;
static lean_object* l_Lake_instInhabitedRegistrySrc___closed__1;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2(lean_object*);
static lean_object* l_Lake_getUrl___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__0;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__5(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0;
static lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1;
static lean_object* l_Lake_Reservoir_fetchPkg_x3f___closed__4;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__9;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__1;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_isGit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__9;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__11;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7;
static lean_object* l_Lake_RegistrySrc_instToJson___closed__0;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Reservoir_fetchPkg_x3f___closed__0;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_RegistryPkg_fromJson_x3f_spec__0(size_t, size_t, lean_object*);
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__1;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__6;
static lean_object* l_Lake_foldlUtf8___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___Lake_uriEscapeChar_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Reservoir_pkgApiUrl___closed__1;
static lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2_spec__2(lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__9;
static lean_object* l_Lake_RegistryPkg_gitSrc_x3f___closed__0;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_RegistryPkg_fromJson_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5;
static lean_object* l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__1;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__6;
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___Lake_uriEscapeChar_spec__0(uint32_t, lean_object*);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2(uint32_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data(lean_object*);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx(lean_object*, lean_object*);
lean_object* l_Lake_captureProc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg(lean_object*, uint32_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__8;
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__3;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg(lean_object*);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__1;
LEAN_EXPORT uint8_t l_Lake_isUriUnreservedMark(uint32_t);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_uriEncode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__2;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson___boxed(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_foldlUtf8___redArg___closed__4;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Reservoir_fetchPkg_x3f___closed__1;
static lean_object* l_Lake_getUrl___closed__6;
static lean_object* l_Lake_foldlUtf8___redArg___closed__6;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__7;
static lean_object* l_Lake_RegistryPkg_instFromJson___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedRegistryPkg___closed__0;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__3;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__1;
LEAN_EXPORT uint32_t l_Lake_hexEncodeByte(uint8_t);
static lean_object* l_Lake_Reservoir_fetchPkg_x3f___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedRegistrySrc;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
lean_object* l_Lake_JsonObject_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getUrl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_RegistryPkg_gitSrc_x3f_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__2;
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_instToJson;
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx(lean_object*);
lean_object* l_Option_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncode(lean_object*);
LEAN_EXPORT lean_object* l_Lake_isUriUnreservedMark___boxed(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__6(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_uint8_shift_right(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__4;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__1;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_foldlUtf8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__5;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_toJson(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__10;
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_instFromJson;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Json_parse(lean_object*);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__4;
static lean_object* l_Lake_instInhabitedRegistrySrc___closed__0;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_RegistrySrc_isGit(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedRegistryPkg;
static lean_object* l_Lake_foldlUtf8___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___boxed(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_fromJson_x3f(lean_object*);
static lean_object* l_Lake_RegistrySrc_instFromJson___closed__0;
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_RegistrySrc_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistrySrc___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistrySrc___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_instInhabitedRegistrySrc___closed__0;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
lean_ctor_set(x_4, 4, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistrySrc() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_RegistrySrc_isGit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_isGit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_RegistrySrc_isGit(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_RegistrySrc_data(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_toJson(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_ctor_set_tag(x_1, 5);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
}
static lean_object* _init_l_Lake_RegistrySrc_instToJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_RegistrySrc_toJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_RegistrySrc_instToJson___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_string_dec_lt(x_2, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_string_dec_eq(x_2, x_3);
if (x_8 == 0)
{
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
}
else
{
x_1 = x_5;
goto _start;
}
}
else
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
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
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
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
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid registry source: ", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gitUrl", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gitUrl: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defaultBranch", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defaultBranch: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("host", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("host: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("github", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("repoUrl", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("repoUrl: ", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_7; 
x_7 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_2 = x_8;
goto block_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_14 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_15 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lake_RegistrySrc_fromJson_x3f___closed__2;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_2 = x_20;
goto block_6;
}
else
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec_ref(x_17);
x_2 = x_21;
goto block_6;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_23 = x_17;
} else {
 lean_dec_ref(x_17);
 x_23 = lean_box(0);
}
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_23);
goto block_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_31; lean_object* x_32; lean_object* x_44; lean_object* x_56; lean_object* x_57; 
lean_dec(x_10);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec_ref(x_22);
x_56 = l_Lake_RegistrySrc_fromJson_x3f___closed__7;
x_57 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_9, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_box(0);
x_44 = x_58;
goto block_55;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_9);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = l_Lake_RegistrySrc_fromJson_x3f___closed__8;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
x_2 = x_63;
goto block_6;
}
else
{
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_64; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_9);
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
lean_dec_ref(x_60);
x_2 = x_64;
goto block_6;
}
else
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
lean_dec_ref(x_60);
if (lean_obj_tag(x_65) == 0)
{
x_44 = x_65;
goto block_55;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = l_Lake_RegistrySrc_fromJson_x3f___closed__9;
x_68 = lean_string_dec_eq(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_box(0);
x_44 = x_69;
goto block_55;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = l_Lake_RegistrySrc_fromJson_x3f___closed__10;
x_71 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_9, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_box(0);
x_44 = x_72;
goto block_55;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_9);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lake_RegistrySrc_fromJson_x3f___closed__11;
x_77 = lean_string_append(x_76, x_75);
lean_dec(x_75);
x_2 = x_77;
goto block_6;
}
else
{
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_78; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_9);
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
lean_dec_ref(x_74);
x_2 = x_78;
goto block_6;
}
else
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec_ref(x_74);
x_44 = x_79;
goto block_55;
}
}
}
}
}
}
}
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_27);
if (lean_is_scalar(x_23)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_23;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
block_43:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lake_RegistrySrc_fromJson_x3f___closed__3;
x_34 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_25 = x_32;
x_26 = x_31;
x_27 = x_35;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__2(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_9);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_2 = x_40;
goto block_6;
}
else
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_41; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_9);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec_ref(x_37);
x_2 = x_41;
goto block_6;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec_ref(x_37);
x_25 = x_32;
x_26 = x_31;
x_27 = x_42;
goto block_30;
}
}
}
}
block_55:
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lake_RegistrySrc_fromJson_x3f___closed__5;
x_46 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_31 = x_44;
x_32 = x_47;
goto block_43;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_44);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_9);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Lake_RegistrySrc_fromJson_x3f___closed__6;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_2 = x_52;
goto block_6;
}
else
{
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_53; 
lean_dec(x_44);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_9);
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
lean_dec_ref(x_49);
x_2 = x_53;
goto block_6;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
lean_dec_ref(x_49);
x_31 = x_44;
x_32 = x_54;
goto block_43;
}
}
}
}
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(1, 1, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_RegistrySrc_fromJson_x3f___closed__0;
x_4 = lean_string_append(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_RegistrySrc_instFromJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_RegistrySrc_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_RegistrySrc_instFromJson___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistryPkg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistryPkg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_instInhabitedRegistryPkg___closed__0;
x_3 = l_Lake_instInhabitedRegistrySrc___closed__0;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistryPkg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedRegistryPkg___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_RegistryPkg_gitSrc_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_inc_ref(x_6);
return x_6;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = l_Lake_RegistrySrc_isGit(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
lean_dec_ref(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_5, x_10);
{
size_t _tmp_4 = x_11;
lean_object* _tmp_5 = x_1;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
}
}
}
static lean_object* _init_l_Lake_RegistryPkg_gitSrc_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = l_Lake_RegistryPkg_gitSrc_x3f___closed__0;
x_6 = lean_array_size(x_2);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_RegistryPkg_gitSrc_x3f_spec__0(x_5, x_4, x_2, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 0)
{
return x_3;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_RegistryPkg_gitSrc_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_RegistryPkg_gitSrc_x3f_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_RegistryPkg_gitSrc_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_RegistryPkg_toJson(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_RegistryPkg_toJson___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_RegistryPkg_fromJson_x3f_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l_Lake_RegistrySrc_fromJson_x3f(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__1(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(x_1);
if (lean_obj_tag(x_3) == 0)
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
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid registry package: ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: name", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fullName", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: fullName", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fullName: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sources", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sources: ", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_7; 
x_7 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_2 = x_8;
goto block_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_11 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = l_Lake_RegistryPkg_fromJson_x3f___closed__2;
x_2 = x_12;
goto block_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_Json_getStr_x3f(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lake_RegistryPkg_fromJson_x3f___closed__3;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_2 = x_17;
goto block_6;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_18; 
lean_dec(x_9);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec_ref(x_14);
x_2 = x_18;
goto block_6;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec_ref(x_14);
x_20 = l_Lake_RegistryPkg_fromJson_x3f___closed__4;
x_21 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_9);
x_22 = l_Lake_RegistryPkg_fromJson_x3f___closed__5;
x_2 = x_22;
goto block_6;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = l_Lean_Json_getStr_x3f(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
lean_dec(x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lake_RegistryPkg_fromJson_x3f___closed__6;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_2 = x_27;
goto block_6;
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_9);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec_ref(x_24);
x_2 = x_28;
goto block_6;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_47; lean_object* x_48; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_30 = x_24;
} else {
 lean_dec_ref(x_24);
 x_30 = lean_box(0);
}
x_47 = l_Lake_RegistryPkg_fromJson_x3f___closed__8;
x_48 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
goto block_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_9);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Lake_RegistryPkg_fromJson_x3f___closed__9;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_2 = x_53;
goto block_6;
}
else
{
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_54; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_9);
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
lean_dec_ref(x_50);
x_2 = x_54;
goto block_6;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec_ref(x_50);
if (lean_obj_tag(x_55) == 0)
{
goto block_46;
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_31 = x_56;
goto block_44;
}
}
}
}
block_44:
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = lean_array_size(x_31);
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_RegistryPkg_fromJson_x3f_spec__0(x_32, x_33, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_9);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_2 = x_35;
goto block_6;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_34, 0);
if (lean_is_scalar(x_30)) {
 x_38 = lean_alloc_ctor(5, 1, 0);
} else {
 x_38 = x_30;
 lean_ctor_set_tag(x_38, 5);
}
lean_ctor_set(x_38, 0, x_9);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
if (lean_is_scalar(x_30)) {
 x_41 = lean_alloc_ctor(5, 1, 0);
} else {
 x_41 = x_30;
 lean_ctor_set_tag(x_41, 5);
}
lean_ctor_set(x_41, 0, x_9);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_42, 2, x_40);
lean_ctor_set(x_42, 3, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
block_46:
{
lean_object* x_45; 
x_45 = l_Lake_RegistryPkg_fromJson_x3f___closed__7;
x_31 = x_45;
goto block_44;
}
}
}
}
}
}
}
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_RegistryPkg_fromJson_x3f___closed__0;
x_4 = lean_string_append(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_RegistryPkg_fromJson_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_RegistryPkg_fromJson_x3f_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_RegistryPkg_instFromJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_RegistryPkg_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_RegistryPkg_instFromJson___closed__0;
return x_1;
}
}
LEAN_EXPORT uint32_t l_Lake_hexEncodeByte(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = lean_uint8_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; uint8_t x_5; 
x_4 = 1;
x_5 = lean_uint8_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; uint8_t x_7; 
x_6 = 2;
x_7 = lean_uint8_dec_eq(x_1, x_6);
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; 
x_8 = 3;
x_9 = lean_uint8_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = 4;
x_11 = lean_uint8_dec_eq(x_1, x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; 
x_12 = 5;
x_13 = lean_uint8_dec_eq(x_1, x_12);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; 
x_14 = 6;
x_15 = lean_uint8_dec_eq(x_1, x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; 
x_16 = 7;
x_17 = lean_uint8_dec_eq(x_1, x_16);
if (x_17 == 0)
{
uint8_t x_18; uint8_t x_19; 
x_18 = 8;
x_19 = lean_uint8_dec_eq(x_1, x_18);
if (x_19 == 0)
{
uint8_t x_20; uint8_t x_21; 
x_20 = 9;
x_21 = lean_uint8_dec_eq(x_1, x_20);
if (x_21 == 0)
{
uint8_t x_22; uint8_t x_23; 
x_22 = 10;
x_23 = lean_uint8_dec_eq(x_1, x_22);
if (x_23 == 0)
{
uint8_t x_24; uint8_t x_25; 
x_24 = 11;
x_25 = lean_uint8_dec_eq(x_1, x_24);
if (x_25 == 0)
{
uint8_t x_26; uint8_t x_27; 
x_26 = 12;
x_27 = lean_uint8_dec_eq(x_1, x_26);
if (x_27 == 0)
{
uint8_t x_28; uint8_t x_29; 
x_28 = 13;
x_29 = lean_uint8_dec_eq(x_1, x_28);
if (x_29 == 0)
{
uint8_t x_30; uint8_t x_31; 
x_30 = 14;
x_31 = lean_uint8_dec_eq(x_1, x_30);
if (x_31 == 0)
{
uint8_t x_32; uint8_t x_33; 
x_32 = 15;
x_33 = lean_uint8_dec_eq(x_1, x_32);
if (x_33 == 0)
{
uint32_t x_34; 
x_34 = 42;
return x_34;
}
else
{
uint32_t x_35; 
x_35 = 70;
return x_35;
}
}
else
{
uint32_t x_36; 
x_36 = 69;
return x_36;
}
}
else
{
uint32_t x_37; 
x_37 = 68;
return x_37;
}
}
else
{
uint32_t x_38; 
x_38 = 67;
return x_38;
}
}
else
{
uint32_t x_39; 
x_39 = 66;
return x_39;
}
}
else
{
uint32_t x_40; 
x_40 = 65;
return x_40;
}
}
else
{
uint32_t x_41; 
x_41 = 57;
return x_41;
}
}
else
{
uint32_t x_42; 
x_42 = 56;
return x_42;
}
}
else
{
uint32_t x_43; 
x_43 = 55;
return x_43;
}
}
else
{
uint32_t x_44; 
x_44 = 54;
return x_44;
}
}
else
{
uint32_t x_45; 
x_45 = 53;
return x_45;
}
}
else
{
uint32_t x_46; 
x_46 = 52;
return x_46;
}
}
else
{
uint32_t x_47; 
x_47 = 51;
return x_47;
}
}
else
{
uint32_t x_48; 
x_48 = 50;
return x_48;
}
}
else
{
uint32_t x_49; 
x_49 = 49;
return x_49;
}
}
else
{
uint32_t x_50; 
x_50 = 48;
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lake_hexEncodeByte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_hexEncodeByte(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte(uint8_t x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint32_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint32_t x_11; lean_object* x_12; 
x_3 = 37;
x_4 = lean_string_push(x_2, x_3);
x_5 = 4;
x_6 = lean_uint8_shift_right(x_1, x_5);
x_7 = l_Lake_hexEncodeByte(x_6);
x_8 = lean_string_push(x_4, x_7);
x_9 = 15;
x_10 = lean_uint8_land(x_1, x_9);
x_11 = l_Lake_hexEncodeByte(x_10);
x_12 = lean_string_push(x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_uriEscapeByte(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_2(x_3, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1(uint32_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_uint32_to_uint8(x_1);
x_9 = lean_uint8_land(x_8, x_2);
x_10 = lean_uint8_lor(x_9, x_3);
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_4, x_7, x_11);
x_13 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_12, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2(uint32_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = 6;
x_9 = lean_uint32_shift_right(x_1, x_8);
x_10 = lean_uint32_to_uint8(x_9);
x_11 = lean_uint8_land(x_10, x_2);
x_12 = lean_uint8_lor(x_11, x_3);
x_13 = lean_box(x_12);
x_14 = lean_apply_2(x_4, x_7, x_13);
x_15 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_14, x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = 12;
x_7 = lean_uint32_shift_right(x_1, x_6);
x_8 = lean_uint32_to_uint8(x_7);
x_9 = 63;
x_10 = lean_uint8_land(x_8, x_9);
x_11 = 128;
x_12 = lean_box_uint32(x_1);
x_13 = lean_box(x_9);
x_14 = lean_box(x_11);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_4);
x_16 = lean_box_uint32(x_1);
x_17 = lean_box(x_9);
x_18 = lean_box(x_11);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_2);
lean_closure_set(x_19, 4, x_3);
lean_closure_set(x_19, 5, x_15);
x_20 = lean_uint8_lor(x_10, x_11);
x_21 = lean_box(x_20);
x_22 = lean_apply_2(x_2, x_5, x_21);
x_23 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_19);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__6(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = 6;
x_7 = lean_uint32_shift_right(x_1, x_6);
x_8 = lean_uint32_to_uint8(x_7);
x_9 = 63;
x_10 = lean_uint8_land(x_8, x_9);
x_11 = 128;
x_12 = lean_box_uint32(x_1);
x_13 = lean_box(x_9);
x_14 = lean_box(x_11);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_4);
x_16 = lean_uint8_lor(x_10, x_11);
x_17 = lean_box(x_16);
x_18 = lean_apply_2(x_2, x_5, x_17);
x_19 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_18, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__5(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_uint32_to_uint8(x_1);
x_7 = 63;
x_8 = lean_uint8_land(x_6, x_7);
x_9 = 128;
x_10 = lean_uint8_lor(x_8, x_9);
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_2, x_5, x_11);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; 
x_5 = 127;
x_6 = lean_uint32_dec_le(x_2, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 2047;
x_8 = lean_uint32_dec_le(x_2, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 65535;
x_10 = lean_uint32_dec_le(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint32_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__0), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_box_uint32(x_2);
lean_inc(x_12);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__3___boxed), 5, 4);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_12);
lean_closure_set(x_15, 3, x_13);
x_16 = 18;
x_17 = lean_uint32_shift_right(x_2, x_16);
x_18 = lean_uint32_to_uint8(x_17);
x_19 = 7;
x_20 = lean_uint8_land(x_18, x_19);
x_21 = 240;
x_22 = lean_uint8_lor(x_20, x_21);
x_23 = lean_box(x_22);
x_24 = lean_apply_2(x_3, x_4, x_23);
x_25 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_24, x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; uint32_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec_ref(x_1);
x_28 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__0), 2, 1);
lean_closure_set(x_28, 0, x_26);
x_29 = lean_box_uint32(x_2);
lean_inc(x_27);
lean_inc(x_3);
x_30 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__6___boxed), 5, 4);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_3);
lean_closure_set(x_30, 2, x_27);
lean_closure_set(x_30, 3, x_28);
x_31 = 12;
x_32 = lean_uint32_shift_right(x_2, x_31);
x_33 = lean_uint32_to_uint8(x_32);
x_34 = 15;
x_35 = lean_uint8_land(x_33, x_34);
x_36 = 224;
x_37 = lean_uint8_lor(x_35, x_36);
x_38 = lean_box(x_37);
x_39 = lean_apply_2(x_3, x_4, x_38);
x_40 = lean_apply_4(x_27, lean_box(0), lean_box(0), x_39, x_30);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; uint32_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_dec_ref(x_1);
x_43 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__0), 2, 1);
lean_closure_set(x_43, 0, x_41);
x_44 = lean_box_uint32(x_2);
lean_inc(x_42);
lean_inc(x_3);
x_45 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__5___boxed), 5, 4);
lean_closure_set(x_45, 0, x_44);
lean_closure_set(x_45, 1, x_3);
lean_closure_set(x_45, 2, x_42);
lean_closure_set(x_45, 3, x_43);
x_46 = 6;
x_47 = lean_uint32_shift_right(x_2, x_46);
x_48 = lean_uint32_to_uint8(x_47);
x_49 = 31;
x_50 = lean_uint8_land(x_48, x_49);
x_51 = 192;
x_52 = lean_uint8_lor(x_50, x_51);
x_53 = lean_box(x_52);
x_54 = lean_apply_2(x_3, x_4, x_53);
x_55 = lean_apply_4(x_42, lean_box(0), lean_box(0), x_54, x_45);
return x_55;
}
}
else
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_1);
x_56 = lean_uint32_to_uint8(x_2);
x_57 = lean_box(x_56);
x_58 = lean_apply_2(x_3, x_4, x_57);
return x_58;
}
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint32_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_foldlUtf8M___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lake_foldlUtf8M___redArg___lam__1(x_8, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lake_foldlUtf8M___redArg___lam__2(x_8, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_7 = l_Lake_foldlUtf8M___redArg___lam__3(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_7 = l_Lake_foldlUtf8M___redArg___lam__6(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_7 = l_Lake_foldlUtf8M___redArg___lam__5(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_Lake_foldlUtf8M___redArg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_8 = l_Lake_foldlUtf8M(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(x_3);
x_5 = lean_apply_2(x_1, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_foldlUtf8___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_foldlUtf8___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_foldlUtf8___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_foldlUtf8___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_foldlUtf8___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_foldlUtf8___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_foldlUtf8___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_foldlUtf8___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_foldlUtf8___redArg___closed__1;
x_2 = l_Lake_foldlUtf8___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_foldlUtf8___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_foldlUtf8___redArg___closed__5;
x_2 = l_Lake_foldlUtf8___redArg___closed__4;
x_3 = l_Lake_foldlUtf8___redArg___closed__3;
x_4 = l_Lake_foldlUtf8___redArg___closed__2;
x_5 = l_Lake_foldlUtf8___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_foldlUtf8___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_foldlUtf8___redArg___closed__6;
x_2 = l_Lake_foldlUtf8___redArg___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lake_foldlUtf8___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_Lake_foldlUtf8___redArg___closed__9;
x_6 = l_Lake_foldlUtf8M___redArg(x_5, x_1, x_4, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lake_foldlUtf8___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_Lake_foldlUtf8___redArg___closed__9;
x_7 = l_Lake_foldlUtf8M___redArg(x_6, x_2, x_5, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lake_foldlUtf8___redArg___lam__0(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_Lake_foldlUtf8___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_Lake_foldlUtf8(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___Lake_uriEscapeChar_spec__0(uint32_t x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 127;
x_4 = lean_uint32_dec_le(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 2047;
x_6 = lean_uint32_dec_le(x_1, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 65535;
x_8 = lean_uint32_dec_le(x_1, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint32_t x_17; uint32_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; uint32_t x_25; uint32_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_9 = 18;
x_10 = lean_uint32_shift_right(x_1, x_9);
x_11 = lean_uint32_to_uint8(x_10);
x_12 = 7;
x_13 = lean_uint8_land(x_11, x_12);
x_14 = 240;
x_15 = lean_uint8_lor(x_13, x_14);
x_16 = l_Lake_uriEscapeByte(x_15, x_2);
x_17 = 12;
x_18 = lean_uint32_shift_right(x_1, x_17);
x_19 = lean_uint32_to_uint8(x_18);
x_20 = 63;
x_21 = lean_uint8_land(x_19, x_20);
x_22 = 128;
x_23 = lean_uint8_lor(x_21, x_22);
x_24 = l_Lake_uriEscapeByte(x_23, x_16);
x_25 = 6;
x_26 = lean_uint32_shift_right(x_1, x_25);
x_27 = lean_uint32_to_uint8(x_26);
x_28 = lean_uint8_land(x_27, x_20);
x_29 = lean_uint8_lor(x_28, x_22);
x_30 = l_Lake_uriEscapeByte(x_29, x_24);
x_31 = lean_uint32_to_uint8(x_1);
x_32 = lean_uint8_land(x_31, x_20);
x_33 = lean_uint8_lor(x_32, x_22);
x_34 = l_Lake_uriEscapeByte(x_33, x_30);
return x_34;
}
else
{
uint32_t x_35; uint32_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; uint32_t x_43; uint32_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; 
x_35 = 12;
x_36 = lean_uint32_shift_right(x_1, x_35);
x_37 = lean_uint32_to_uint8(x_36);
x_38 = 15;
x_39 = lean_uint8_land(x_37, x_38);
x_40 = 224;
x_41 = lean_uint8_lor(x_39, x_40);
x_42 = l_Lake_uriEscapeByte(x_41, x_2);
x_43 = 6;
x_44 = lean_uint32_shift_right(x_1, x_43);
x_45 = lean_uint32_to_uint8(x_44);
x_46 = 63;
x_47 = lean_uint8_land(x_45, x_46);
x_48 = 128;
x_49 = lean_uint8_lor(x_47, x_48);
x_50 = l_Lake_uriEscapeByte(x_49, x_42);
x_51 = lean_uint32_to_uint8(x_1);
x_52 = lean_uint8_land(x_51, x_46);
x_53 = lean_uint8_lor(x_52, x_48);
x_54 = l_Lake_uriEscapeByte(x_53, x_50);
return x_54;
}
}
else
{
uint32_t x_55; uint32_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; 
x_55 = 6;
x_56 = lean_uint32_shift_right(x_1, x_55);
x_57 = lean_uint32_to_uint8(x_56);
x_58 = 31;
x_59 = lean_uint8_land(x_57, x_58);
x_60 = 192;
x_61 = lean_uint8_lor(x_59, x_60);
x_62 = l_Lake_uriEscapeByte(x_61, x_2);
x_63 = lean_uint32_to_uint8(x_1);
x_64 = 63;
x_65 = lean_uint8_land(x_63, x_64);
x_66 = 128;
x_67 = lean_uint8_lor(x_65, x_66);
x_68 = l_Lake_uriEscapeByte(x_67, x_62);
return x_68;
}
}
else
{
uint8_t x_69; lean_object* x_70; 
x_69 = lean_uint32_to_uint8(x_1);
x_70 = l_Lake_uriEscapeByte(x_69, x_2);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_foldlUtf8M___at___Lake_uriEscapeChar_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___Lake_uriEscapeChar_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lake_foldlUtf8M___at___Lake_uriEscapeChar_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lake_uriEscapeChar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_isUriUnreservedMark(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 45;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 95;
x_5 = lean_uint32_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 46;
x_7 = lean_uint32_dec_eq(x_1, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 33;
x_9 = lean_uint32_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 126;
x_11 = lean_uint32_dec_eq(x_1, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 42;
x_13 = lean_uint32_dec_eq(x_1, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 39;
x_15 = lean_uint32_dec_eq(x_1, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 40;
x_17 = lean_uint32_dec_eq(x_1, x_16);
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 41;
x_19 = lean_uint32_dec_eq(x_1, x_18);
return x_19;
}
else
{
return x_17;
}
}
else
{
return x_15;
}
}
else
{
return x_13;
}
}
else
{
return x_11;
}
}
else
{
return x_9;
}
}
else
{
return x_7;
}
}
else
{
return x_5;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_isUriUnreservedMark___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lake_isUriUnreservedMark(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar(uint32_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_9; uint8_t x_16; uint32_t x_23; uint8_t x_24; 
x_23 = 65;
x_24 = lean_uint32_dec_le(x_23, x_1);
if (x_24 == 0)
{
x_16 = x_24;
goto block_22;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 90;
x_26 = lean_uint32_dec_le(x_1, x_25);
x_16 = x_26;
goto block_22;
}
block_8:
{
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lake_isUriUnreservedMark(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lake_foldlUtf8M___at___Lake_uriEscapeChar_spec__0(x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_string_push(x_2, x_1);
return x_6;
}
}
else
{
lean_object* x_7; 
x_7 = lean_string_push(x_2, x_1);
return x_7;
}
}
block_15:
{
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 48;
x_11 = lean_uint32_dec_le(x_10, x_1);
if (x_11 == 0)
{
x_3 = x_11;
goto block_8;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 57;
x_13 = lean_uint32_dec_le(x_1, x_12);
x_3 = x_13;
goto block_8;
}
}
else
{
lean_object* x_14; 
x_14 = lean_string_push(x_2, x_1);
return x_14;
}
}
block_22:
{
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 97;
x_18 = lean_uint32_dec_le(x_17, x_1);
if (x_18 == 0)
{
x_9 = x_18;
goto block_15;
}
else
{
uint32_t x_19; uint8_t x_20; 
x_19 = 122;
x_20 = lean_uint32_dec_le(x_1, x_19);
x_9 = x_20;
goto block_15;
}
}
else
{
lean_object* x_21; 
x_21 = lean_string_push(x_2, x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lake_uriEncodeChar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_uriEncode_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_6 = lean_string_utf8_next(x_1, x_3);
x_7 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
x_8 = l_Lake_uriEncodeChar(x_7, x_4);
x_3 = x_6;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncode(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_instInhabitedRegistrySrc___closed__0;
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_foldlAux___at___Lake_uriEncode_spec__0(x_1, x_3, x_4, x_2);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_uriEncode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___at___Lake_uriEncode_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncode___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_uriEncode(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-H", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__0;
x_2 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__2;
x_8 = lean_array_push(x_7, x_6);
x_9 = l_Array_append___redArg(x_4, x_8);
lean_dec_ref(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lake_getUrl___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_getUrl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("curl", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_getUrl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_getUrl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-s", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_getUrl___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_getUrl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--retry", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_getUrl___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("3", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_getUrl___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_getUrl___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_getUrl___closed__3;
x_2 = l_Lake_getUrl___closed__7;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_getUrl___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_getUrl___closed__4;
x_2 = l_Lake_getUrl___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_getUrl___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_getUrl___closed__5;
x_2 = l_Lake_getUrl___closed__9;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_getUrl___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_getUrl___closed__6;
x_2 = l_Lake_getUrl___closed__10;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = l_Lake_getUrl___closed__11;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_2);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
x_5 = x_16;
goto block_15;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
x_5 = x_16;
goto block_15;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0(x_2, x_21, x_22, x_16);
x_5 = x_23;
goto block_15;
}
}
block_15:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lake_getUrl___closed__0;
x_7 = l_Lake_getUrl___closed__1;
x_8 = lean_array_push(x_5, x_1);
x_9 = lean_box(0);
x_10 = l_Lake_getUrl___closed__2;
x_11 = 1;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 1, x_12);
x_14 = l_Lake_captureProc(x_13, x_3, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_getUrl(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_ReservoirResp_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_ReservoirResp_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_ReservoirResp_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_ReservoirResp_fromJson_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_string_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_JsonObject_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("status", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: status", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("status: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("message", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: message", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("message: ", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_14; 
lean_inc(x_2);
x_14 = l_Lean_Json_getObj_x3f(x_2);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec_ref(x_14);
x_19 = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___lam__0___boxed), 2, 0);
x_20 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0;
lean_inc_ref(x_19);
x_21 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(x_19, x_18, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_19);
goto block_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1;
x_24 = l_Option_fromJson_x3f___redArg(x_23, x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec_ref(x_19);
lean_dec(x_2);
lean_dec_ref(x_1);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_33; 
lean_dec_ref(x_19);
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_ctor_set_tag(x_24, 0);
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
lean_dec_ref(x_24);
if (lean_obj_tag(x_36) == 0)
{
lean_dec_ref(x_19);
goto block_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3;
lean_inc(x_37);
lean_inc_ref(x_19);
x_39 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(x_19, x_37, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_37);
lean_dec_ref(x_19);
x_40 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5;
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Lean_Json_getNat_x3f(x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_37);
lean_dec_ref(x_19);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_51; 
lean_dec(x_37);
lean_dec_ref(x_19);
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
lean_ctor_set_tag(x_42, 0);
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
lean_dec(x_42);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_42, 0);
lean_inc(x_54);
lean_dec_ref(x_42);
x_55 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7;
x_56 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(x_19, x_37, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec(x_54);
x_57 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9;
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = l_Lean_Json_getStr_x3f(x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
lean_dec(x_54);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_63);
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
x_65 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10;
x_66 = lean_string_append(x_65, x_64);
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
else
{
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_68; 
lean_dec(x_54);
x_68 = !lean_is_exclusive(x_59);
if (x_68 == 0)
{
lean_ctor_set_tag(x_59, 0);
return x_59;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec(x_59);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_59);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_59, 0);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_54);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_59, 0, x_73);
return x_59;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_59, 0);
lean_inc(x_74);
lean_dec(x_59);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_54);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
}
}
}
}
}
}
}
}
block_13:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
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
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_ReservoirResp_fromJson_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_ReservoirResp_fromJson_x3f___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Reservoir_pkgApiUrl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/packages/", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_pkgApiUrl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = l_Lake_Reservoir_pkgApiUrl___closed__0;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Lake_uriEncode(x_2);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lake_uriEncode(x_3);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Reservoir_pkgApiUrl(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("X-Reservoir-Api-Version:1.0.0", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("X-Lake-Registry-Api-Version:0.1.0", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Reservoir_lakeHeaders___closed__0;
x_2 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Reservoir_lakeHeaders___closed__1;
x_2 = l_Lake_Reservoir_lakeHeaders___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Reservoir_lakeHeaders___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; uint32_t x_9; uint8_t x_10; uint32_t x_17; uint8_t x_18; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_5);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_9, x_19);
x_10 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
goto block_16;
}
block_8:
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
block_16:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_9, x_13);
x_6 = x_14;
goto block_8;
}
else
{
x_6 = x_12;
goto block_8;
}
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2_spec__2___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
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
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec_ref(x_13);
x_18 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0;
x_19 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_17, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
goto block_12;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Option_fromJson_x3f___at___Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2_spec__2(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_ctor_set_tag(x_21, 0);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec_ref(x_21);
if (lean_obj_tag(x_33) == 0)
{
goto block_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3;
x_36 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_34, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec(x_34);
x_37 = l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__0;
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lean_Json_getNat_x3f(x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_34);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
else
{
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_48; 
lean_dec(x_34);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
lean_ctor_set_tag(x_39, 0);
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
lean_dec_ref(x_39);
x_52 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7;
x_53 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__0___redArg(x_34, x_52);
lean_dec(x_34);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
lean_dec(x_51);
x_54 = l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__1;
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Json_getStr_x3f(x_55);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_51);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10;
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_62 = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
else
{
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_65; 
lean_dec(x_51);
x_65 = !lean_is_exclusive(x_56);
if (x_65 == 0)
{
lean_ctor_set_tag(x_56, 0);
return x_56;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_56, 0);
lean_inc(x_66);
lean_dec(x_56);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_56);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_56, 0);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_56, 0, x_70);
return x_56;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_56, 0);
lean_inc(x_71);
lean_dec(x_56);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_51);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
}
}
}
}
}
}
}
}
}
block_12:
{
lean_object* x_2; 
x_2 = l_Lake_RegistryPkg_fromJson_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
}
static lean_object* _init_l_Lake_Reservoir_fetchPkg_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Reservoir lookup failed; server returned invalid JSON: ", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_fetchPkg_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Reservoir responded with:\n", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_fetchPkg_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Reservoir lookup failed; server returned unsupported JSON: ", 61, 61);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_fetchPkg_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Reservoir lookup failed: ", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_fetchPkg_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Reservoir lookup failed", 25, 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lake_Reservoir_pkgApiUrl(x_1, x_2, x_3);
x_13 = l_Lake_Reservoir_lakeHeaders;
x_14 = l_Lake_getUrl(x_12, x_13, x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
x_22 = l_Lean_Json_parse(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_25 = lean_string_append(x_2, x_24);
x_26 = lean_string_append(x_25, x_3);
x_27 = l_Lake_Reservoir_fetchPkg_x3f___closed__0;
lean_inc_ref(x_26);
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_23);
lean_dec(x_23);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_get_size(x_21);
x_33 = lean_array_push(x_21, x_31);
x_34 = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
x_35 = lean_string_append(x_26, x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_string_utf8_byte_size(x_20);
x_38 = l_Substring_takeWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__0(x_20, x_37, x_36);
x_39 = l_Substring_takeRightWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__1(x_20, x_38, x_37);
x_40 = lean_string_utf8_extract(x_20, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_20);
x_41 = lean_string_append(x_35, x_40);
lean_dec_ref(x_40);
x_42 = 0;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_array_push(x_33, x_43);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_44);
lean_ctor_set(x_16, 0, x_32);
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_22, 0);
lean_inc(x_45);
lean_dec_ref(x_22);
x_46 = l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_49 = lean_string_append(x_2, x_48);
x_50 = lean_string_append(x_49, x_3);
x_51 = l_Lake_Reservoir_fetchPkg_x3f___closed__2;
lean_inc_ref(x_50);
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_string_append(x_52, x_47);
lean_dec(x_47);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_21);
x_57 = lean_array_push(x_21, x_55);
x_58 = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
x_59 = lean_string_append(x_50, x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_string_utf8_byte_size(x_20);
x_62 = l_Substring_takeWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__0(x_20, x_61, x_60);
x_63 = l_Substring_takeRightWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__1(x_20, x_62, x_61);
x_64 = lean_string_utf8_extract(x_20, x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_20);
x_65 = lean_string_append(x_59, x_64);
lean_dec_ref(x_64);
x_66 = 0;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_array_push(x_57, x_67);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_68);
lean_ctor_set(x_16, 0, x_56);
return x_14;
}
else
{
lean_object* x_69; 
lean_dec(x_20);
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
lean_dec_ref(x_46);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
lean_dec_ref(x_2);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_16, 0, x_69);
return x_14;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_16, 0, x_72);
return x_14;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_74);
lean_dec_ref(x_69);
x_75 = lean_unsigned_to_nat(404u);
x_76 = lean_nat_dec_eq(x_73, x_75);
lean_dec(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_78 = lean_string_append(x_2, x_77);
x_79 = lean_string_append(x_78, x_3);
x_80 = l_Lake_Reservoir_fetchPkg_x3f___closed__3;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_string_append(x_81, x_74);
lean_dec_ref(x_74);
x_83 = 3;
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = lean_array_get_size(x_21);
x_86 = lean_array_push(x_21, x_84);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_86);
lean_ctor_set(x_16, 0, x_85);
return x_14;
}
else
{
lean_object* x_87; 
lean_dec_ref(x_74);
lean_dec_ref(x_2);
x_87 = lean_box(0);
lean_ctor_set(x_16, 0, x_87);
return x_14;
}
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_16, 0);
x_89 = lean_ctor_get(x_16, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_16);
lean_inc(x_88);
x_90 = l_Lean_Json_parse(x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_93 = lean_string_append(x_2, x_92);
x_94 = lean_string_append(x_93, x_3);
x_95 = l_Lake_Reservoir_fetchPkg_x3f___closed__0;
lean_inc_ref(x_94);
x_96 = lean_string_append(x_94, x_95);
x_97 = lean_string_append(x_96, x_91);
lean_dec(x_91);
x_98 = 3;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
x_100 = lean_array_get_size(x_89);
x_101 = lean_array_push(x_89, x_99);
x_102 = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
x_103 = lean_string_append(x_94, x_102);
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_string_utf8_byte_size(x_88);
x_106 = l_Substring_takeWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__0(x_88, x_105, x_104);
x_107 = l_Substring_takeRightWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__1(x_88, x_106, x_105);
x_108 = lean_string_utf8_extract(x_88, x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_88);
x_109 = lean_string_append(x_103, x_108);
lean_dec_ref(x_108);
x_110 = 0;
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_array_push(x_101, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_100);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_14, 0, x_113);
return x_14;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_90, 0);
lean_inc(x_114);
lean_dec_ref(x_90);
x_115 = l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2(x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
x_117 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_118 = lean_string_append(x_2, x_117);
x_119 = lean_string_append(x_118, x_3);
x_120 = l_Lake_Reservoir_fetchPkg_x3f___closed__2;
lean_inc_ref(x_119);
x_121 = lean_string_append(x_119, x_120);
x_122 = lean_string_append(x_121, x_116);
lean_dec(x_116);
x_123 = 3;
x_124 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_123);
x_125 = lean_array_get_size(x_89);
x_126 = lean_array_push(x_89, x_124);
x_127 = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
x_128 = lean_string_append(x_119, x_127);
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_string_utf8_byte_size(x_88);
x_131 = l_Substring_takeWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__0(x_88, x_130, x_129);
x_132 = l_Substring_takeRightWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__1(x_88, x_131, x_130);
x_133 = lean_string_utf8_extract(x_88, x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_88);
x_134 = lean_string_append(x_128, x_133);
lean_dec_ref(x_133);
x_135 = 0;
x_136 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_135);
x_137 = lean_array_push(x_126, x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_125);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_14, 0, x_138);
return x_14;
}
else
{
lean_object* x_139; 
lean_dec(x_88);
x_139 = lean_ctor_get(x_115, 0);
lean_inc(x_139);
lean_dec_ref(x_115);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec_ref(x_2);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_141;
 lean_ctor_set_tag(x_142, 1);
}
lean_ctor_set(x_142, 0, x_140);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_89);
lean_ctor_set(x_14, 0, x_143);
return x_14;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_139, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_139, 1);
lean_inc_ref(x_145);
lean_dec_ref(x_139);
x_146 = lean_unsigned_to_nat(404u);
x_147 = lean_nat_dec_eq(x_144, x_146);
lean_dec(x_144);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_148 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_149 = lean_string_append(x_2, x_148);
x_150 = lean_string_append(x_149, x_3);
x_151 = l_Lake_Reservoir_fetchPkg_x3f___closed__3;
x_152 = lean_string_append(x_150, x_151);
x_153 = lean_string_append(x_152, x_145);
lean_dec_ref(x_145);
x_154 = 3;
x_155 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_154);
x_156 = lean_array_get_size(x_89);
x_157 = lean_array_push(x_89, x_155);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_14, 0, x_158);
return x_14;
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec_ref(x_145);
lean_dec_ref(x_2);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_89);
lean_ctor_set(x_14, 0, x_160);
return x_14;
}
}
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_14, 1);
lean_inc(x_161);
lean_dec(x_14);
x_162 = lean_ctor_get(x_16, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_16, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_164 = x_16;
} else {
 lean_dec_ref(x_16);
 x_164 = lean_box(0);
}
lean_inc(x_162);
x_165 = l_Lean_Json_parse(x_162);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec_ref(x_165);
x_167 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_168 = lean_string_append(x_2, x_167);
x_169 = lean_string_append(x_168, x_3);
x_170 = l_Lake_Reservoir_fetchPkg_x3f___closed__0;
lean_inc_ref(x_169);
x_171 = lean_string_append(x_169, x_170);
x_172 = lean_string_append(x_171, x_166);
lean_dec(x_166);
x_173 = 3;
x_174 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_173);
x_175 = lean_array_get_size(x_163);
x_176 = lean_array_push(x_163, x_174);
x_177 = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
x_178 = lean_string_append(x_169, x_177);
x_179 = lean_unsigned_to_nat(0u);
x_180 = lean_string_utf8_byte_size(x_162);
x_181 = l_Substring_takeWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__0(x_162, x_180, x_179);
x_182 = l_Substring_takeRightWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__1(x_162, x_181, x_180);
x_183 = lean_string_utf8_extract(x_162, x_181, x_182);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_162);
x_184 = lean_string_append(x_178, x_183);
lean_dec_ref(x_183);
x_185 = 0;
x_186 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_185);
x_187 = lean_array_push(x_176, x_186);
if (lean_is_scalar(x_164)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_164;
 lean_ctor_set_tag(x_188, 1);
}
lean_ctor_set(x_188, 0, x_175);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_161);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_165, 0);
lean_inc(x_190);
lean_dec_ref(x_165);
x_191 = l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2(x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
x_193 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_194 = lean_string_append(x_2, x_193);
x_195 = lean_string_append(x_194, x_3);
x_196 = l_Lake_Reservoir_fetchPkg_x3f___closed__2;
lean_inc_ref(x_195);
x_197 = lean_string_append(x_195, x_196);
x_198 = lean_string_append(x_197, x_192);
lean_dec(x_192);
x_199 = 3;
x_200 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_199);
x_201 = lean_array_get_size(x_163);
x_202 = lean_array_push(x_163, x_200);
x_203 = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
x_204 = lean_string_append(x_195, x_203);
x_205 = lean_unsigned_to_nat(0u);
x_206 = lean_string_utf8_byte_size(x_162);
x_207 = l_Substring_takeWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__0(x_162, x_206, x_205);
x_208 = l_Substring_takeRightWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__1(x_162, x_207, x_206);
x_209 = lean_string_utf8_extract(x_162, x_207, x_208);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_162);
x_210 = lean_string_append(x_204, x_209);
lean_dec_ref(x_209);
x_211 = 0;
x_212 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*1, x_211);
x_213 = lean_array_push(x_202, x_212);
if (lean_is_scalar(x_164)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_164;
 lean_ctor_set_tag(x_214, 1);
}
lean_ctor_set(x_214, 0, x_201);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_161);
return x_215;
}
else
{
lean_object* x_216; 
lean_dec(x_162);
x_216 = lean_ctor_get(x_191, 0);
lean_inc(x_216);
lean_dec_ref(x_191);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec_ref(x_2);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 x_218 = x_216;
} else {
 lean_dec_ref(x_216);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 1, 0);
} else {
 x_219 = x_218;
 lean_ctor_set_tag(x_219, 1);
}
lean_ctor_set(x_219, 0, x_217);
if (lean_is_scalar(x_164)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_164;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_163);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_161);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_222 = lean_ctor_get(x_216, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_216, 1);
lean_inc_ref(x_223);
lean_dec_ref(x_216);
x_224 = lean_unsigned_to_nat(404u);
x_225 = lean_nat_dec_eq(x_222, x_224);
lean_dec(x_222);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_226 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_227 = lean_string_append(x_2, x_226);
x_228 = lean_string_append(x_227, x_3);
x_229 = l_Lake_Reservoir_fetchPkg_x3f___closed__3;
x_230 = lean_string_append(x_228, x_229);
x_231 = lean_string_append(x_230, x_223);
lean_dec_ref(x_223);
x_232 = 3;
x_233 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set_uint8(x_233, sizeof(void*)*1, x_232);
x_234 = lean_array_get_size(x_163);
x_235 = lean_array_push(x_163, x_233);
if (lean_is_scalar(x_164)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_164;
 lean_ctor_set_tag(x_236, 1);
}
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_161);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec_ref(x_223);
lean_dec_ref(x_2);
x_238 = lean_box(0);
if (lean_is_scalar(x_164)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_164;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_163);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_161);
return x_240;
}
}
}
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec_ref(x_2);
x_241 = lean_ctor_get(x_14, 1);
lean_inc(x_241);
lean_dec_ref(x_14);
x_242 = lean_ctor_get(x_16, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_16, 1);
lean_inc(x_243);
lean_dec_ref(x_16);
x_6 = x_242;
x_7 = x_243;
x_8 = x_241;
goto block_11;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; 
x_244 = lean_ctor_get(x_14, 1);
lean_inc(x_244);
lean_dec_ref(x_14);
x_245 = lean_ctor_get(x_15, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_15, 1);
lean_inc(x_246);
lean_dec_ref(x_15);
x_247 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_248 = lean_string_append(x_2, x_247);
x_249 = lean_string_append(x_248, x_3);
x_250 = l_Lake_Reservoir_fetchPkg_x3f___closed__4;
x_251 = lean_string_append(x_249, x_250);
x_252 = 3;
x_253 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set_uint8(x_253, sizeof(void*)*1, x_252);
x_254 = lean_array_push(x_246, x_253);
x_6 = x_245;
x_7 = x_254;
x_8 = x_244;
goto block_11;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lake_Reservoir_fetchPkg_x3f_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Reservoir_fetchPkg_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Env(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Reservoir(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Env(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedRegistrySrc___closed__0 = _init_l_Lake_instInhabitedRegistrySrc___closed__0();
lean_mark_persistent(l_Lake_instInhabitedRegistrySrc___closed__0);
l_Lake_instInhabitedRegistrySrc___closed__1 = _init_l_Lake_instInhabitedRegistrySrc___closed__1();
lean_mark_persistent(l_Lake_instInhabitedRegistrySrc___closed__1);
l_Lake_instInhabitedRegistrySrc = _init_l_Lake_instInhabitedRegistrySrc();
lean_mark_persistent(l_Lake_instInhabitedRegistrySrc);
l_Lake_RegistrySrc_instToJson___closed__0 = _init_l_Lake_RegistrySrc_instToJson___closed__0();
lean_mark_persistent(l_Lake_RegistrySrc_instToJson___closed__0);
l_Lake_RegistrySrc_instToJson = _init_l_Lake_RegistrySrc_instToJson();
lean_mark_persistent(l_Lake_RegistrySrc_instToJson);
l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_RegistrySrc_fromJson_x3f_spec__1___closed__0);
l_Lake_RegistrySrc_fromJson_x3f___closed__0 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__0();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__0);
l_Lake_RegistrySrc_fromJson_x3f___closed__1 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__1();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__1);
l_Lake_RegistrySrc_fromJson_x3f___closed__2 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__2();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__2);
l_Lake_RegistrySrc_fromJson_x3f___closed__3 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__3();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__3);
l_Lake_RegistrySrc_fromJson_x3f___closed__4 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__4();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__4);
l_Lake_RegistrySrc_fromJson_x3f___closed__5 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__5();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__5);
l_Lake_RegistrySrc_fromJson_x3f___closed__6 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__6();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__6);
l_Lake_RegistrySrc_fromJson_x3f___closed__7 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__7();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__7);
l_Lake_RegistrySrc_fromJson_x3f___closed__8 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__8();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__8);
l_Lake_RegistrySrc_fromJson_x3f___closed__9 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__9();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__9);
l_Lake_RegistrySrc_fromJson_x3f___closed__10 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__10();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__10);
l_Lake_RegistrySrc_fromJson_x3f___closed__11 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__11();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__11);
l_Lake_RegistrySrc_instFromJson___closed__0 = _init_l_Lake_RegistrySrc_instFromJson___closed__0();
lean_mark_persistent(l_Lake_RegistrySrc_instFromJson___closed__0);
l_Lake_RegistrySrc_instFromJson = _init_l_Lake_RegistrySrc_instFromJson();
lean_mark_persistent(l_Lake_RegistrySrc_instFromJson);
l_Lake_instInhabitedRegistryPkg___closed__0 = _init_l_Lake_instInhabitedRegistryPkg___closed__0();
lean_mark_persistent(l_Lake_instInhabitedRegistryPkg___closed__0);
l_Lake_instInhabitedRegistryPkg___closed__1 = _init_l_Lake_instInhabitedRegistryPkg___closed__1();
lean_mark_persistent(l_Lake_instInhabitedRegistryPkg___closed__1);
l_Lake_instInhabitedRegistryPkg = _init_l_Lake_instInhabitedRegistryPkg();
lean_mark_persistent(l_Lake_instInhabitedRegistryPkg);
l_Lake_RegistryPkg_gitSrc_x3f___closed__0 = _init_l_Lake_RegistryPkg_gitSrc_x3f___closed__0();
lean_mark_persistent(l_Lake_RegistryPkg_gitSrc_x3f___closed__0);
l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0 = _init_l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0();
lean_mark_persistent(l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0);
l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson = _init_l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson();
lean_mark_persistent(l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson);
l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0 = _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0();
lean_mark_persistent(l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0);
l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1 = _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1();
lean_mark_persistent(l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1);
l_Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0);
l_Lake_RegistryPkg_fromJson_x3f___closed__0 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__0();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__0);
l_Lake_RegistryPkg_fromJson_x3f___closed__1 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__1();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__1);
l_Lake_RegistryPkg_fromJson_x3f___closed__2 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__2();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__2);
l_Lake_RegistryPkg_fromJson_x3f___closed__3 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__3();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__3);
l_Lake_RegistryPkg_fromJson_x3f___closed__4 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__4();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__4);
l_Lake_RegistryPkg_fromJson_x3f___closed__5 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__5();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__5);
l_Lake_RegistryPkg_fromJson_x3f___closed__6 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__6();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__6);
l_Lake_RegistryPkg_fromJson_x3f___closed__7 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__7();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__7);
l_Lake_RegistryPkg_fromJson_x3f___closed__8 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__8();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__8);
l_Lake_RegistryPkg_fromJson_x3f___closed__9 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__9();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__9);
l_Lake_RegistryPkg_instFromJson___closed__0 = _init_l_Lake_RegistryPkg_instFromJson___closed__0();
lean_mark_persistent(l_Lake_RegistryPkg_instFromJson___closed__0);
l_Lake_RegistryPkg_instFromJson = _init_l_Lake_RegistryPkg_instFromJson();
lean_mark_persistent(l_Lake_RegistryPkg_instFromJson);
l_Lake_foldlUtf8___redArg___closed__0 = _init_l_Lake_foldlUtf8___redArg___closed__0();
lean_mark_persistent(l_Lake_foldlUtf8___redArg___closed__0);
l_Lake_foldlUtf8___redArg___closed__1 = _init_l_Lake_foldlUtf8___redArg___closed__1();
lean_mark_persistent(l_Lake_foldlUtf8___redArg___closed__1);
l_Lake_foldlUtf8___redArg___closed__2 = _init_l_Lake_foldlUtf8___redArg___closed__2();
lean_mark_persistent(l_Lake_foldlUtf8___redArg___closed__2);
l_Lake_foldlUtf8___redArg___closed__3 = _init_l_Lake_foldlUtf8___redArg___closed__3();
lean_mark_persistent(l_Lake_foldlUtf8___redArg___closed__3);
l_Lake_foldlUtf8___redArg___closed__4 = _init_l_Lake_foldlUtf8___redArg___closed__4();
lean_mark_persistent(l_Lake_foldlUtf8___redArg___closed__4);
l_Lake_foldlUtf8___redArg___closed__5 = _init_l_Lake_foldlUtf8___redArg___closed__5();
lean_mark_persistent(l_Lake_foldlUtf8___redArg___closed__5);
l_Lake_foldlUtf8___redArg___closed__6 = _init_l_Lake_foldlUtf8___redArg___closed__6();
lean_mark_persistent(l_Lake_foldlUtf8___redArg___closed__6);
l_Lake_foldlUtf8___redArg___closed__7 = _init_l_Lake_foldlUtf8___redArg___closed__7();
lean_mark_persistent(l_Lake_foldlUtf8___redArg___closed__7);
l_Lake_foldlUtf8___redArg___closed__8 = _init_l_Lake_foldlUtf8___redArg___closed__8();
lean_mark_persistent(l_Lake_foldlUtf8___redArg___closed__8);
l_Lake_foldlUtf8___redArg___closed__9 = _init_l_Lake_foldlUtf8___redArg___closed__9();
lean_mark_persistent(l_Lake_foldlUtf8___redArg___closed__9);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__1);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_getUrl_spec__0___closed__2);
l_Lake_getUrl___closed__0 = _init_l_Lake_getUrl___closed__0();
lean_mark_persistent(l_Lake_getUrl___closed__0);
l_Lake_getUrl___closed__1 = _init_l_Lake_getUrl___closed__1();
lean_mark_persistent(l_Lake_getUrl___closed__1);
l_Lake_getUrl___closed__2 = _init_l_Lake_getUrl___closed__2();
lean_mark_persistent(l_Lake_getUrl___closed__2);
l_Lake_getUrl___closed__3 = _init_l_Lake_getUrl___closed__3();
lean_mark_persistent(l_Lake_getUrl___closed__3);
l_Lake_getUrl___closed__4 = _init_l_Lake_getUrl___closed__4();
lean_mark_persistent(l_Lake_getUrl___closed__4);
l_Lake_getUrl___closed__5 = _init_l_Lake_getUrl___closed__5();
lean_mark_persistent(l_Lake_getUrl___closed__5);
l_Lake_getUrl___closed__6 = _init_l_Lake_getUrl___closed__6();
lean_mark_persistent(l_Lake_getUrl___closed__6);
l_Lake_getUrl___closed__7 = _init_l_Lake_getUrl___closed__7();
lean_mark_persistent(l_Lake_getUrl___closed__7);
l_Lake_getUrl___closed__8 = _init_l_Lake_getUrl___closed__8();
lean_mark_persistent(l_Lake_getUrl___closed__8);
l_Lake_getUrl___closed__9 = _init_l_Lake_getUrl___closed__9();
lean_mark_persistent(l_Lake_getUrl___closed__9);
l_Lake_getUrl___closed__10 = _init_l_Lake_getUrl___closed__10();
lean_mark_persistent(l_Lake_getUrl___closed__10);
l_Lake_getUrl___closed__11 = _init_l_Lake_getUrl___closed__11();
lean_mark_persistent(l_Lake_getUrl___closed__11);
l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0 = _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0);
l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1 = _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1);
l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2 = _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2);
l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3 = _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3);
l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4 = _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4);
l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5 = _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5);
l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6 = _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6);
l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7 = _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7);
l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8 = _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8);
l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9 = _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9);
l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10 = _init_l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10);
l_Lake_Reservoir_pkgApiUrl___closed__0 = _init_l_Lake_Reservoir_pkgApiUrl___closed__0();
lean_mark_persistent(l_Lake_Reservoir_pkgApiUrl___closed__0);
l_Lake_Reservoir_pkgApiUrl___closed__1 = _init_l_Lake_Reservoir_pkgApiUrl___closed__1();
lean_mark_persistent(l_Lake_Reservoir_pkgApiUrl___closed__1);
l_Lake_Reservoir_lakeHeaders___closed__0 = _init_l_Lake_Reservoir_lakeHeaders___closed__0();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__0);
l_Lake_Reservoir_lakeHeaders___closed__1 = _init_l_Lake_Reservoir_lakeHeaders___closed__1();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__1);
l_Lake_Reservoir_lakeHeaders___closed__2 = _init_l_Lake_Reservoir_lakeHeaders___closed__2();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__2);
l_Lake_Reservoir_lakeHeaders___closed__3 = _init_l_Lake_Reservoir_lakeHeaders___closed__3();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__3);
l_Lake_Reservoir_lakeHeaders = _init_l_Lake_Reservoir_lakeHeaders();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders);
l_Option_fromJson_x3f___at___Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2_spec__2___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2_spec__2___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2_spec__2___closed__0);
l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__0 = _init_l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__0();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__0);
l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__1 = _init_l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__1();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___at___Lake_Reservoir_fetchPkg_x3f_spec__2___closed__1);
l_Lake_Reservoir_fetchPkg_x3f___closed__0 = _init_l_Lake_Reservoir_fetchPkg_x3f___closed__0();
lean_mark_persistent(l_Lake_Reservoir_fetchPkg_x3f___closed__0);
l_Lake_Reservoir_fetchPkg_x3f___closed__1 = _init_l_Lake_Reservoir_fetchPkg_x3f___closed__1();
lean_mark_persistent(l_Lake_Reservoir_fetchPkg_x3f___closed__1);
l_Lake_Reservoir_fetchPkg_x3f___closed__2 = _init_l_Lake_Reservoir_fetchPkg_x3f___closed__2();
lean_mark_persistent(l_Lake_Reservoir_fetchPkg_x3f___closed__2);
l_Lake_Reservoir_fetchPkg_x3f___closed__3 = _init_l_Lake_Reservoir_fetchPkg_x3f___closed__3();
lean_mark_persistent(l_Lake_Reservoir_fetchPkg_x3f___closed__3);
l_Lake_Reservoir_fetchPkg_x3f___closed__4 = _init_l_Lake_Reservoir_fetchPkg_x3f___closed__4();
lean_mark_persistent(l_Lake_Reservoir_fetchPkg_x3f___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
