// Lean compiler output
// Module: Lake.Reservoir
// Imports: Lake.Util.Log Lake.Util.Proc Lake.Util.JsonObject Lake.Config.Env
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
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp___rarg(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__5;
LEAN_EXPORT lean_object* l_Lake_uriEncode___boxed(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static lean_object* l_Lake_getUrl___closed__7;
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_fromJson_x3f(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar(uint32_t, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(lean_object*, lean_object*);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__12;
lean_object* l_Option_fromJson_x3f___at___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_607____spec__2(lean_object*);
static lean_object* l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__3;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at_Lake_Reservoir_fetchPkg_x3f___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data___boxed(lean_object*);
static lean_object* l_Lake_getUrl___closed__8;
static lean_object* l_Lake_instInhabitedRegistryPkg___closed__1;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8(lean_object*);
LEAN_EXPORT lean_object* l_Lake_hexEncodeByte___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_RegistryPkg_fromJson_x3f___spec__1(size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte(uint8_t, lean_object*);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___rarg(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__13;
static lean_object* l_Lake_getUrl___closed__10;
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_instFromJson;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__8;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__19;
LEAN_EXPORT lean_object* l_Lake_Reservoir_lakeHeaders;
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__5;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__21;
uint8_t lean_uint8_land(uint8_t, uint8_t);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__16;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__5;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__2;
static lean_object* l_Lake_instInhabitedRegistrySrc___closed__1;
static lean_object* l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__5;
static lean_object* l_Lake_getUrl___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_RegistryPkg_fromJson_x3f___spec__2(lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__23;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__13;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__9;
static lean_object* l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__4;
static lean_object* l_Lake_RegistryPkg_gitSrc_x3f___closed__3;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_isGit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_instToJson;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__15;
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__22;
static size_t l_Lake_RegistryPkg_fromJson_x3f___closed__20;
static lean_object* l_Lake_getUrl___closed__9;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_ReservoirResp_fromJson_x3f___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__5(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__11;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__15;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__1;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__6;
static lean_object* l_Lake_Reservoir_pkgApiUrl___closed__1;
static lean_object* l_Lake_instInhabitedRegistrySrc___closed__2;
static lean_object* l_Lake_Reservoir_pkgApiUrl___closed__2;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__4;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_RegistryPkg_gitSrc_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__13;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__1;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__6;
static lean_object* l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__1;
static lean_object* l_Lake_RegistrySrc_instFromJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__2(uint32_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data(lean_object*);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__8;
static lean_object* l_Lake_RegistryPkg_gitSrc_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___lambda__1___boxed(lean_object*);
lean_object* l_Lake_captureProc(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson(lean_object*);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__11;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__8;
static lean_object* l_Lake_RegistryPkg_instToJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__6(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__3;
LEAN_EXPORT uint8_t l_Lake_isUriUnreservedMark(uint32_t);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__10;
static lean_object* l_Lake_getUrl___closed__2;
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson___boxed(lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__10;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__11;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__17;
LEAN_EXPORT lean_object* l_Lake_getUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__18;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at_Lake_foldlUtf8___spec__1___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Reservoir_fetchPkg_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getUrl___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_RegistryPkg_gitSrc_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__7;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__14;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp(lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lake_uriEncode___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__17;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__3;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__1;
LEAN_EXPORT uint32_t l_Lake_hexEncodeByte(uint8_t);
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at_Lake_uriEscapeChar___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__18;
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedRegistrySrc;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__4;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__12;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getUrl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__11;
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__2;
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_instToJson;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncode(lean_object*);
LEAN_EXPORT lean_object* l_Lake_isUriUnreservedMark___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_toJson___boxed(lean_object*);
static lean_object* l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1___closed__1;
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_uint8_shift_right(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at_Lake_foldlUtf8___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_any(lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at_Lake_foldlUtf8___spec__1(lean_object*);
static lean_object* l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__2;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__9;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__4;
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lake_uriEncode___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedRegistryPkg___closed__2;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__7;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_RegistrySrc_instToJson___closed__1;
static lean_object* l_Lake_getUrl___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__4(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__14;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__15;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__5;
static lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__5;
static lean_object* l_Lake_RegistryPkg_gitSrc_x3f___closed__2;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__16;
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__3(uint32_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_toJson(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_RegistryPkg_instFromJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__10;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_fromJson_x3f___at_Lean_Server_instRpcEncodableArray___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_instFromJson;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__6;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__4;
LEAN_EXPORT uint8_t l_Lake_RegistrySrc_isGit(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedRegistryPkg;
static lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__12;
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___lambda__1(lean_object*);
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at_Lake_uriEscapeChar___spec__1(uint32_t, lean_object*);
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__4;
static lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__14;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_RegistryPkg_fromJson_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_instInhabitedRegistrySrc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistrySrc___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistrySrc() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__2;
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
lean_dec(x_1);
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
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_RegistrySrc_data(x_1);
x_3 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_toJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_RegistrySrc_toJson(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_RegistrySrc_instToJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_RegistrySrc_toJson___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_RegistrySrc_instToJson___closed__1;
return x_1;
}
}
static lean_object* _init_l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1___closed__1;
return x_2;
}
case 1:
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
default: 
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_13 = l_Lean_Json_getStr_x3f(x_1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_16; 
lean_free_object(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_27 = x_13;
} else {
 lean_dec_ref(x_13);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid registry source: ", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistrySrc_fromJson_x3f___closed__3;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defaultBranch", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistrySrc_fromJson_x3f___closed__7;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistrySrc_fromJson_x3f___closed__11;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("host", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistrySrc_fromJson_x3f___closed__14;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gitUrl", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__16;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistrySrc_fromJson_x3f___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistrySrc_fromJson_x3f___closed__17;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_8 = lean_string_append(x_6, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_136; lean_object* x_137; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_16 = x_2;
} else {
 lean_dec_ref(x_2);
 x_16 = lean_box(0);
}
x_136 = l_Lake_RegistrySrc_fromJson_x3f___closed__16;
x_137 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
x_138 = lean_box(0);
x_17 = x_138;
goto block_135;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1(x_139);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
lean_dec(x_16);
lean_dec(x_15);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = l_Lake_RegistrySrc_fromJson_x3f___closed__18;
x_144 = lean_string_append(x_143, x_142);
lean_dec(x_142);
x_145 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_146 = lean_string_append(x_144, x_145);
x_147 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_148 = lean_string_append(x_147, x_146);
lean_dec(x_146);
x_149 = lean_string_append(x_148, x_145);
lean_ctor_set(x_140, 0, x_149);
return x_140;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_150 = lean_ctor_get(x_140, 0);
lean_inc(x_150);
lean_dec(x_140);
x_151 = l_Lake_RegistrySrc_fromJson_x3f___closed__18;
x_152 = lean_string_append(x_151, x_150);
lean_dec(x_150);
x_153 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_154 = lean_string_append(x_152, x_153);
x_155 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_156 = lean_string_append(x_155, x_154);
lean_dec(x_154);
x_157 = lean_string_append(x_156, x_153);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
else
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_140, 0);
lean_inc(x_159);
lean_dec(x_140);
x_17 = x_159;
goto block_135;
}
}
block_135:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
if (lean_is_scalar(x_16)) {
 x_19 = lean_alloc_ctor(1, 1, 0);
} else {
 x_19 = x_16;
}
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_80; lean_object* x_111; lean_object* x_112; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_111 = l_Lake_RegistrySrc_fromJson_x3f___closed__13;
x_112 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_box(0);
x_80 = x_113;
goto block_110;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1(x_114);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = l_Lake_RegistrySrc_fromJson_x3f___closed__15;
x_119 = lean_string_append(x_118, x_117);
lean_dec(x_117);
x_120 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_121 = lean_string_append(x_119, x_120);
x_122 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_123 = lean_string_append(x_122, x_121);
lean_dec(x_121);
x_124 = lean_string_append(x_123, x_120);
lean_ctor_set(x_115, 0, x_124);
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_115, 0);
lean_inc(x_125);
lean_dec(x_115);
x_126 = l_Lake_RegistrySrc_fromJson_x3f___closed__15;
x_127 = lean_string_append(x_126, x_125);
lean_dec(x_125);
x_128 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_129 = lean_string_append(x_127, x_128);
x_130 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
x_132 = lean_string_append(x_131, x_128);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_115, 0);
lean_inc(x_134);
lean_dec(x_115);
x_80 = x_134;
goto block_110;
}
}
block_79:
{
lean_object* x_22; lean_object* x_55; lean_object* x_56; 
x_55 = l_Lake_RegistrySrc_fromJson_x3f___closed__6;
x_56 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_22 = x_57;
goto block_54;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1(x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = l_Lake_RegistrySrc_fromJson_x3f___closed__8;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
x_64 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_65 = lean_string_append(x_63, x_64);
x_66 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_67 = lean_string_append(x_66, x_65);
lean_dec(x_65);
x_68 = lean_string_append(x_67, x_64);
lean_ctor_set(x_59, 0, x_68);
return x_59;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec(x_59);
x_70 = l_Lake_RegistrySrc_fromJson_x3f___closed__8;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_73 = lean_string_append(x_71, x_72);
x_74 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = lean_string_append(x_75, x_72);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_59, 0);
lean_inc(x_78);
lean_dec(x_59);
x_22 = x_78;
goto block_54;
}
}
block_54:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lake_RegistrySrc_fromJson_x3f___closed__2;
x_24 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_25);
if (lean_is_scalar(x_16)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_16;
}
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Option_fromJson_x3f___at___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_607____spec__2(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lake_RegistrySrc_fromJson_x3f___closed__5;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = lean_string_append(x_37, x_34);
lean_ctor_set(x_29, 0, x_38);
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
x_40 = l_Lake_RegistrySrc_fromJson_x3f___closed__5;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = lean_string_append(x_45, x_42);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_29);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_15);
lean_ctor_set(x_50, 1, x_20);
lean_ctor_set(x_50, 2, x_21);
lean_ctor_set(x_50, 3, x_22);
lean_ctor_set(x_50, 4, x_49);
lean_ctor_set(x_29, 0, x_50);
return x_29;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_29, 0);
lean_inc(x_51);
lean_dec(x_29);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_15);
lean_ctor_set(x_52, 1, x_20);
lean_ctor_set(x_52, 2, x_21);
lean_ctor_set(x_52, 3, x_22);
lean_ctor_set(x_52, 4, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
}
block_110:
{
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_box(0);
x_21 = x_81;
goto block_79;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lake_RegistrySrc_fromJson_x3f___closed__9;
x_84 = lean_string_dec_eq(x_82, x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_box(0);
x_21 = x_85;
goto block_79;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lake_RegistrySrc_fromJson_x3f___closed__10;
x_87 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_box(0);
x_21 = x_88;
goto block_79;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1(x_89);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = l_Lake_RegistrySrc_fromJson_x3f___closed__12;
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_96 = lean_string_append(x_94, x_95);
x_97 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_98 = lean_string_append(x_97, x_96);
lean_dec(x_96);
x_99 = lean_string_append(x_98, x_95);
lean_ctor_set(x_90, 0, x_99);
return x_90;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_100 = lean_ctor_get(x_90, 0);
lean_inc(x_100);
lean_dec(x_90);
x_101 = l_Lake_RegistrySrc_fromJson_x3f___closed__12;
x_102 = lean_string_append(x_101, x_100);
lean_dec(x_100);
x_103 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_104 = lean_string_append(x_102, x_103);
x_105 = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
x_106 = lean_string_append(x_105, x_104);
lean_dec(x_104);
x_107 = lean_string_append(x_106, x_103);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_90, 0);
lean_inc(x_109);
lean_dec(x_90);
x_21 = x_109;
goto block_79;
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
static lean_object* _init_l_Lake_RegistrySrc_instFromJson___closed__1() {
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
x_1 = l_Lake_RegistrySrc_instFromJson___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistryPkg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistryPkg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_instInhabitedRegistryPkg___closed__1;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistryPkg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedRegistryPkg___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_RegistryPkg_gitSrc_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = l_Lake_RegistrySrc_isGit(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_6, x_11);
{
size_t _tmp_5 = x_12;
lean_object* _tmp_6 = x_3;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lake_RegistryPkg_gitSrc_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_gitSrc_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_RegistryPkg_gitSrc_x3f___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_gitSrc_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_gitSrc_x3f___closed__2;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_box(0);
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l_Lake_RegistryPkg_gitSrc_x3f___closed__1;
x_7 = l_Array_forIn_x27Unsafe_loop___at_Lake_RegistryPkg_gitSrc_x3f___spec__1(x_2, x_3, x_6, x_2, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lake_RegistryPkg_gitSrc_x3f___closed__3;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_RegistryPkg_gitSrc_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lake_RegistryPkg_gitSrc_x3f___spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_RegistryPkg_gitSrc_x3f___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_RegistryPkg_gitSrc_x3f(x_1);
lean_dec(x_1);
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
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_RegistryPkg_instToJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_RegistryPkg_toJson___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_RegistryPkg_instToJson___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_RegistryPkg_fromJson_x3f___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lake_RegistrySrc_fromJson_x3f(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_RegistryPkg_fromJson_x3f___spec__2(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at_Lean_Server_instRpcEncodableArray___spec__4(x_1);
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
default: 
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_13 = l_Array_fromJson_x3f___at_Lean_Server_instRpcEncodableArray___spec__4(x_1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_16; 
lean_free_object(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_27 = x_13;
} else {
 lean_dec_ref(x_13);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid registry package: ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__3;
x_2 = l_Lake_RegistryPkg_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__4;
x_2 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_2 = l_Lake_RegistryPkg_fromJson_x3f___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__6;
x_2 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_RegistryPkg_fromJson_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__9;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fullName", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__3;
x_2 = l_Lake_RegistryPkg_fromJson_x3f___closed__11;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__12;
x_2 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_2 = l_Lake_RegistryPkg_fromJson_x3f___closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__14;
x_2 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__15;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_RegistryPkg_fromJson_x3f___closed__11;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__17;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static size_t _init_l_Lake_RegistryPkg_fromJson_x3f___closed__20() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__19;
x_2 = lean_array_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sources", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_RegistryPkg_fromJson_x3f___closed__21;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_RegistryPkg_fromJson_x3f___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__22;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_8 = lean_string_append(x_6, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lake_RegistryPkg_fromJson_x3f___closed__2;
x_17 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_15);
x_18 = l_Lake_RegistryPkg_fromJson_x3f___closed__8;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Json_getStr_x3f(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lake_RegistryPkg_fromJson_x3f___closed__10;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = lean_string_append(x_28, x_25);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lake_RegistryPkg_fromJson_x3f___closed__10;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = lean_string_append(x_36, x_33);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
lean_dec(x_20);
x_40 = l_Lake_RegistryPkg_fromJson_x3f___closed__11;
x_41 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_15);
x_42 = l_Lake_RegistryPkg_fromJson_x3f___closed__16;
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = l_Lean_Json_getStr_x3f(x_43);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_15);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = l_Lake_RegistryPkg_fromJson_x3f___closed__18;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = lean_string_append(x_53, x_50);
lean_ctor_set(x_45, 0, x_54);
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_56 = l_Lake_RegistryPkg_fromJson_x3f___closed__18;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = lean_string_append(x_61, x_58);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_130; lean_object* x_131; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec(x_45);
x_130 = l_Lake_RegistryPkg_fromJson_x3f___closed__21;
x_131 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_15, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_box(0);
x_65 = x_132;
goto block_129;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Option_fromJson_x3f___at_Lake_RegistryPkg_fromJson_x3f___spec__2(x_133);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
lean_dec(x_64);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_15);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = l_Lake_RegistryPkg_fromJson_x3f___closed__23;
x_138 = lean_string_append(x_137, x_136);
lean_dec(x_136);
x_139 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_140 = lean_string_append(x_138, x_139);
x_141 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_142 = lean_string_append(x_141, x_140);
lean_dec(x_140);
x_143 = lean_string_append(x_142, x_139);
lean_ctor_set(x_134, 0, x_143);
return x_134;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_144 = lean_ctor_get(x_134, 0);
lean_inc(x_144);
lean_dec(x_134);
x_145 = l_Lake_RegistryPkg_fromJson_x3f___closed__23;
x_146 = lean_string_append(x_145, x_144);
lean_dec(x_144);
x_147 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_148 = lean_string_append(x_146, x_147);
x_149 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_150 = lean_string_append(x_149, x_148);
lean_dec(x_148);
x_151 = lean_string_append(x_150, x_147);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_134, 0);
lean_inc(x_153);
lean_dec(x_134);
x_65 = x_153;
goto block_129;
}
}
block_129:
{
if (lean_obj_tag(x_65) == 0)
{
size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; 
x_66 = 0;
x_67 = l_Lake_RegistryPkg_fromJson_x3f___closed__20;
x_68 = l_Lake_RegistryPkg_fromJson_x3f___closed__19;
x_69 = l_Array_mapMUnsafe_map___at_Lake_RegistryPkg_fromJson_x3f___spec__1(x_67, x_66, x_68);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
lean_dec(x_64);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_15);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_73 = lean_string_append(x_72, x_71);
lean_dec(x_71);
x_74 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_75 = lean_string_append(x_73, x_74);
lean_ctor_set(x_69, 0, x_75);
return x_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
lean_dec(x_69);
x_77 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_78 = lean_string_append(x_77, x_76);
lean_dec(x_76);
x_79 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_69);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_69, 0);
if (lean_is_scalar(x_44)) {
 x_84 = lean_alloc_ctor(5, 1, 0);
} else {
 x_84 = x_44;
 lean_ctor_set_tag(x_84, 5);
}
lean_ctor_set(x_84, 0, x_15);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_39);
lean_ctor_set(x_85, 1, x_64);
lean_ctor_set(x_85, 2, x_83);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_69, 0, x_85);
return x_69;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_69, 0);
lean_inc(x_86);
lean_dec(x_69);
if (lean_is_scalar(x_44)) {
 x_87 = lean_alloc_ctor(5, 1, 0);
} else {
 x_87 = x_44;
 lean_ctor_set_tag(x_87, 5);
}
lean_ctor_set(x_87, 0, x_15);
x_88 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_88, 0, x_39);
lean_ctor_set(x_88, 1, x_64);
lean_ctor_set(x_88, 2, x_86);
lean_ctor_set(x_88, 3, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_44);
x_90 = !lean_is_exclusive(x_65);
if (x_90 == 0)
{
lean_object* x_91; size_t x_92; size_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_65, 0);
x_92 = lean_array_size(x_91);
x_93 = 0;
x_94 = l_Array_mapMUnsafe_map___at_Lake_RegistryPkg_fromJson_x3f___spec__1(x_92, x_93, x_91);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
lean_free_object(x_65);
lean_dec(x_64);
lean_dec(x_39);
lean_dec(x_15);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_98 = lean_string_append(x_97, x_96);
lean_dec(x_96);
x_99 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_100 = lean_string_append(x_98, x_99);
lean_ctor_set(x_94, 0, x_100);
return x_94;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_94, 0);
lean_inc(x_101);
lean_dec(x_94);
x_102 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_94);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_94, 0);
lean_ctor_set_tag(x_65, 5);
lean_ctor_set(x_65, 0, x_15);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_39);
lean_ctor_set(x_109, 1, x_64);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_65);
lean_ctor_set(x_94, 0, x_109);
return x_94;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_94, 0);
lean_inc(x_110);
lean_dec(x_94);
lean_ctor_set_tag(x_65, 5);
lean_ctor_set(x_65, 0, x_15);
x_111 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_111, 0, x_39);
lean_ctor_set(x_111, 1, x_64);
lean_ctor_set(x_111, 2, x_110);
lean_ctor_set(x_111, 3, x_65);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_65, 0);
lean_inc(x_113);
lean_dec(x_65);
x_114 = lean_array_size(x_113);
x_115 = 0;
x_116 = l_Array_mapMUnsafe_map___at_Lake_RegistryPkg_fromJson_x3f___spec__1(x_114, x_115, x_113);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_64);
lean_dec(x_39);
lean_dec(x_15);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
x_120 = lean_string_append(x_119, x_117);
lean_dec(x_117);
x_121 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_122 = lean_string_append(x_120, x_121);
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(0, 1, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_116, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_125 = x_116;
} else {
 lean_dec_ref(x_116);
 x_125 = lean_box(0);
}
x_126 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_126, 0, x_15);
x_127 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_127, 0, x_39);
lean_ctor_set(x_127, 1, x_64);
lean_ctor_set(x_127, 2, x_124);
lean_ctor_set(x_127, 3, x_126);
if (lean_is_scalar(x_125)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_125;
}
lean_ctor_set(x_128, 0, x_127);
return x_128;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_RegistryPkg_fromJson_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_RegistryPkg_fromJson_x3f___spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_RegistryPkg_instFromJson___closed__1() {
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
x_1 = l_Lake_RegistryPkg_instFromJson___closed__1;
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
lean_dec(x_1);
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
lean_dec(x_1);
x_4 = l_Lake_uriEscapeByte(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__2(uint32_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_uint32_to_uint8(x_1);
x_9 = lean_uint8_land(x_8, x_2);
x_10 = lean_uint8_lor(x_9, x_3);
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_4, x_7, x_11);
x_13 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___rarg___lambda__1), 2, 1);
lean_closure_set(x_13, 0, x_5);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__3(uint32_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = 6;
x_9 = lean_uint32_shift_right(x_1, x_8);
x_10 = lean_uint32_to_uint8(x_9);
x_11 = lean_uint8_land(x_10, x_2);
x_12 = lean_uint8_lor(x_11, x_3);
x_13 = lean_box(x_12);
lean_inc(x_4);
x_14 = lean_apply_2(x_4, x_7, x_13);
x_15 = lean_box_uint32(x_1);
x_16 = lean_box(x_2);
x_17 = lean_box(x_3);
lean_inc(x_6);
x_18 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_6);
x_19 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_14, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__4(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = 12;
x_7 = lean_uint32_shift_right(x_1, x_6);
x_8 = lean_uint32_to_uint8(x_7);
x_9 = 63;
x_10 = lean_uint8_land(x_8, x_9);
x_11 = 128;
x_12 = lean_uint8_lor(x_10, x_11);
x_13 = lean_box(x_12);
lean_inc(x_2);
x_14 = lean_apply_2(x_2, x_5, x_13);
x_15 = lean_box_uint32(x_1);
x_16 = lean_box(x_9);
x_17 = lean_box(x_11);
lean_inc(x_4);
x_18 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___rarg___lambda__3___boxed), 7, 6);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_2);
lean_closure_set(x_18, 4, x_3);
lean_closure_set(x_18, 5, x_4);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__5(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = 6;
x_7 = lean_uint32_shift_right(x_1, x_6);
x_8 = lean_uint32_to_uint8(x_7);
x_9 = 63;
x_10 = lean_uint8_land(x_8, x_9);
x_11 = 128;
x_12 = lean_uint8_lor(x_10, x_11);
x_13 = lean_box(x_12);
lean_inc(x_2);
x_14 = lean_apply_2(x_2, x_5, x_13);
x_15 = lean_box_uint32(x_1);
x_16 = lean_box(x_9);
x_17 = lean_box(x_11);
lean_inc(x_4);
x_18 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_2);
lean_closure_set(x_18, 4, x_3);
lean_closure_set(x_18, 5, x_4);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__6(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_uint32_to_uint8(x_1);
x_7 = 63;
x_8 = lean_uint8_land(x_6, x_7);
x_9 = 128;
x_10 = lean_uint8_lor(x_8, x_9);
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_2, x_5, x_11);
x_13 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___rarg___lambda__1), 2, 1);
lean_closure_set(x_13, 0, x_3);
x_14 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_11; uint32_t x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = 18;
x_13 = lean_uint32_shift_right(x_2, x_12);
x_14 = lean_uint32_to_uint8(x_13);
x_15 = 7;
x_16 = lean_uint8_land(x_14, x_15);
x_17 = 240;
x_18 = lean_uint8_lor(x_16, x_17);
x_19 = lean_box(x_18);
lean_inc(x_3);
x_20 = lean_apply_2(x_3, x_4, x_19);
x_21 = lean_box_uint32(x_2);
lean_inc(x_11);
x_22 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___rarg___lambda__4___boxed), 5, 4);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_1);
lean_closure_set(x_22, 3, x_11);
x_23 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_20, x_22);
return x_23;
}
else
{
lean_object* x_24; uint32_t x_25; uint32_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = 12;
x_26 = lean_uint32_shift_right(x_2, x_25);
x_27 = lean_uint32_to_uint8(x_26);
x_28 = 15;
x_29 = lean_uint8_land(x_27, x_28);
x_30 = 224;
x_31 = lean_uint8_lor(x_29, x_30);
x_32 = lean_box(x_31);
lean_inc(x_3);
x_33 = lean_apply_2(x_3, x_4, x_32);
x_34 = lean_box_uint32(x_2);
lean_inc(x_24);
x_35 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___rarg___lambda__5___boxed), 5, 4);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_3);
lean_closure_set(x_35, 2, x_1);
lean_closure_set(x_35, 3, x_24);
x_36 = lean_apply_4(x_24, lean_box(0), lean_box(0), x_33, x_35);
return x_36;
}
}
else
{
lean_object* x_37; uint32_t x_38; uint32_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = 6;
x_39 = lean_uint32_shift_right(x_2, x_38);
x_40 = lean_uint32_to_uint8(x_39);
x_41 = 31;
x_42 = lean_uint8_land(x_40, x_41);
x_43 = 192;
x_44 = lean_uint8_lor(x_42, x_43);
x_45 = lean_box(x_44);
lean_inc(x_3);
x_46 = lean_apply_2(x_3, x_4, x_45);
x_47 = lean_box_uint32(x_2);
lean_inc(x_37);
x_48 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___rarg___lambda__6___boxed), 5, 4);
lean_closure_set(x_48, 0, x_47);
lean_closure_set(x_48, 1, x_3);
lean_closure_set(x_48, 2, x_1);
lean_closure_set(x_48, 3, x_37);
x_49 = lean_apply_4(x_37, lean_box(0), lean_box(0), x_46, x_48);
return x_49;
}
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_50 = lean_uint32_to_uint8(x_2);
x_51 = lean_box(x_50);
x_52 = lean_apply_2(x_3, x_4, x_51);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_foldlUtf8M___rarg___lambda__2(x_8, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_foldlUtf8M___rarg___lambda__3(x_8, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_7 = l_Lake_foldlUtf8M___rarg___lambda__4(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_7 = l_Lake_foldlUtf8M___rarg___lambda__5(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_7 = l_Lake_foldlUtf8M___rarg___lambda__6(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_Lake_foldlUtf8M___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at_Lake_foldlUtf8___spec__1___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 127;
x_5 = lean_uint32_dec_le(x_2, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 2047;
x_7 = lean_uint32_dec_le(x_2, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 65535;
x_9 = lean_uint32_dec_le(x_2, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; uint32_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; uint32_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_10 = 18;
x_11 = lean_uint32_shift_right(x_2, x_10);
x_12 = lean_uint32_to_uint8(x_11);
x_13 = 7;
x_14 = lean_uint8_land(x_12, x_13);
x_15 = 240;
x_16 = lean_uint8_lor(x_14, x_15);
x_17 = lean_box(x_16);
lean_inc(x_1);
x_18 = lean_apply_2(x_1, x_3, x_17);
x_19 = 12;
x_20 = lean_uint32_shift_right(x_2, x_19);
x_21 = lean_uint32_to_uint8(x_20);
x_22 = 63;
x_23 = lean_uint8_land(x_21, x_22);
x_24 = 128;
x_25 = lean_uint8_lor(x_23, x_24);
x_26 = lean_box(x_25);
lean_inc(x_1);
x_27 = lean_apply_2(x_1, x_18, x_26);
x_28 = 6;
x_29 = lean_uint32_shift_right(x_2, x_28);
x_30 = lean_uint32_to_uint8(x_29);
x_31 = lean_uint8_land(x_30, x_22);
x_32 = lean_uint8_lor(x_31, x_24);
x_33 = lean_box(x_32);
lean_inc(x_1);
x_34 = lean_apply_2(x_1, x_27, x_33);
x_35 = lean_uint32_to_uint8(x_2);
x_36 = lean_uint8_land(x_35, x_22);
x_37 = lean_uint8_lor(x_36, x_24);
x_38 = lean_box(x_37);
x_39 = lean_apply_2(x_1, x_34, x_38);
return x_39;
}
else
{
uint32_t x_40; uint32_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; uint32_t x_49; uint32_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_40 = 12;
x_41 = lean_uint32_shift_right(x_2, x_40);
x_42 = lean_uint32_to_uint8(x_41);
x_43 = 15;
x_44 = lean_uint8_land(x_42, x_43);
x_45 = 224;
x_46 = lean_uint8_lor(x_44, x_45);
x_47 = lean_box(x_46);
lean_inc(x_1);
x_48 = lean_apply_2(x_1, x_3, x_47);
x_49 = 6;
x_50 = lean_uint32_shift_right(x_2, x_49);
x_51 = lean_uint32_to_uint8(x_50);
x_52 = 63;
x_53 = lean_uint8_land(x_51, x_52);
x_54 = 128;
x_55 = lean_uint8_lor(x_53, x_54);
x_56 = lean_box(x_55);
lean_inc(x_1);
x_57 = lean_apply_2(x_1, x_48, x_56);
x_58 = lean_uint32_to_uint8(x_2);
x_59 = lean_uint8_land(x_58, x_52);
x_60 = lean_uint8_lor(x_59, x_54);
x_61 = lean_box(x_60);
x_62 = lean_apply_2(x_1, x_57, x_61);
return x_62;
}
}
else
{
uint32_t x_63; uint32_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_63 = 6;
x_64 = lean_uint32_shift_right(x_2, x_63);
x_65 = lean_uint32_to_uint8(x_64);
x_66 = 31;
x_67 = lean_uint8_land(x_65, x_66);
x_68 = 192;
x_69 = lean_uint8_lor(x_67, x_68);
x_70 = lean_box(x_69);
lean_inc(x_1);
x_71 = lean_apply_2(x_1, x_3, x_70);
x_72 = lean_uint32_to_uint8(x_2);
x_73 = 63;
x_74 = lean_uint8_land(x_72, x_73);
x_75 = 128;
x_76 = lean_uint8_lor(x_74, x_75);
x_77 = lean_box(x_76);
x_78 = lean_apply_2(x_1, x_71, x_77);
return x_78;
}
}
else
{
uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_uint32_to_uint8(x_2);
x_80 = lean_box(x_79);
x_81 = lean_apply_2(x_1, x_3, x_80);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at_Lake_foldlUtf8___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___at_Lake_foldlUtf8___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___rarg(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_foldlUtf8M___at_Lake_foldlUtf8___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_foldlUtf8___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at_Lake_foldlUtf8___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Lake_foldlUtf8M___at_Lake_foldlUtf8___spec__1___rarg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_Lake_foldlUtf8___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at_Lake_uriEscapeChar___spec__1(uint32_t x_1, lean_object* x_2) {
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
x_3 = l_Lake_foldlUtf8M___at_Lake_uriEscapeChar___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at_Lake_uriEscapeChar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lake_foldlUtf8M___at_Lake_uriEscapeChar___spec__1(x_3, x_2);
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
uint8_t x_20; 
x_20 = 1;
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = 1;
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = 1;
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = 1;
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = 1;
return x_27;
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
lean_object* x_3; uint32_t x_16; uint8_t x_17; 
x_16 = 65;
x_17 = lean_uint32_dec_le(x_16, x_1);
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 97;
x_19 = lean_uint32_dec_le(x_18, x_1);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
x_3 = x_20;
goto block_15;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 122;
x_22 = lean_uint32_dec_le(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
x_3 = x_23;
goto block_15;
}
else
{
lean_object* x_24; 
x_24 = lean_string_push(x_2, x_1);
return x_24;
}
}
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 90;
x_26 = lean_uint32_dec_le(x_1, x_25);
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 97;
x_28 = lean_uint32_dec_le(x_27, x_1);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_3 = x_29;
goto block_15;
}
else
{
uint32_t x_30; uint8_t x_31; 
x_30 = 122;
x_31 = lean_uint32_dec_le(x_1, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
x_3 = x_32;
goto block_15;
}
else
{
lean_object* x_33; 
x_33 = lean_string_push(x_2, x_1);
return x_33;
}
}
}
else
{
lean_object* x_34; 
x_34 = lean_string_push(x_2, x_1);
return x_34;
}
}
block_15:
{
uint32_t x_4; uint8_t x_5; 
lean_dec(x_3);
x_4 = 48;
x_5 = lean_uint32_dec_le(x_4, x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lake_isUriUnreservedMark(x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lake_foldlUtf8M___at_Lake_uriEscapeChar___spec__1(x_1, x_2);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_string_push(x_2, x_1);
return x_8;
}
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 57;
x_10 = lean_uint32_dec_le(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lake_isUriUnreservedMark(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lake_foldlUtf8M___at_Lake_uriEscapeChar___spec__1(x_1, x_2);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_string_push(x_2, x_1);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = lean_string_push(x_2, x_1);
return x_14;
}
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
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lake_uriEncode___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_5 = l_String_foldlAux___at_Lake_uriEncode___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lake_uriEncode___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___at_Lake_uriEncode___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncode___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_uriEncode(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-H", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_array_mk(x_10);
x_12 = l_Array_append___rarg(x_5, x_11);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
static lean_object* _init_l_Lake_getUrl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("3", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_getUrl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_getUrl___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_getUrl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--retry", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_getUrl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_getUrl___closed__3;
x_2 = l_Lake_getUrl___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_getUrl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_getUrl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_getUrl___closed__5;
x_2 = l_Lake_getUrl___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_getUrl___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-s", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_getUrl___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_getUrl___closed__7;
x_2 = l_Lake_getUrl___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_getUrl___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_getUrl___closed__8;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_getUrl___closed__10() {
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
static lean_object* _init_l_Lake_getUrl___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("curl", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_array_get_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
x_9 = lean_box(0);
if (x_8 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_10 = l_Lake_getUrl___closed__9;
x_11 = lean_array_push(x_10, x_1);
x_12 = l_Lake_getUrl___closed__10;
x_13 = l_Lake_getUrl___closed__11;
x_14 = l_Lake_RegistryPkg_fromJson_x3f___closed__19;
x_15 = 1;
x_16 = 0;
x_17 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set(x_17, 4, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_16);
x_18 = l_Lake_captureProc(x_17, x_3, x_4);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_6, x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
x_20 = l_Lake_getUrl___closed__9;
x_21 = lean_array_push(x_20, x_1);
x_22 = l_Lake_getUrl___closed__10;
x_23 = l_Lake_getUrl___closed__11;
x_24 = l_Lake_RegistryPkg_fromJson_x3f___closed__19;
x_25 = 1;
x_26 = 0;
x_27 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_9);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_26);
x_28 = l_Lake_captureProc(x_27, x_3, x_4);
return x_28;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_31 = l_Lake_getUrl___closed__9;
x_32 = l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1(x_5, x_2, x_29, x_30, x_31);
x_33 = lean_array_push(x_32, x_1);
x_34 = l_Lake_getUrl___closed__10;
x_35 = l_Lake_getUrl___closed__11;
x_36 = l_Lake_RegistryPkg_fromJson_x3f___closed__19;
x_37 = 1;
x_38 = 0;
x_39 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_9);
lean_ctor_set(x_39, 4, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*5, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*5 + 1, x_38);
x_40 = l_Lake_captureProc(x_39, x_3, x_4);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_getUrl(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at_Lake_ReservoirResp_fromJson_x3f___spec__1(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1___closed__1;
return x_2;
}
case 1:
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
default: 
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_13 = l_Lean_Json_getObj_x3f(x_1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_16; 
lean_free_object(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_27 = x_13;
} else {
 lean_dec_ref(x_13);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("status", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__3;
x_2 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__2;
x_2 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__5;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("message", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_RegistryPkg_fromJson_x3f___closed__3;
x_2 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__8;
x_2 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__11;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_2 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__14;
x_2 = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_57; 
lean_inc(x_2);
x_57 = l_Lean_Json_getObj_x3f(x_2);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
lean_dec(x_57);
x_62 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__13;
x_63 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_61, x_62);
lean_dec(x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_box(0);
x_3 = x_64;
goto block_56;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Option_fromJson_x3f___at_Lake_ReservoirResp_fromJson_x3f___spec__1(x_65);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__15;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_72 = lean_string_append(x_70, x_71);
lean_ctor_set(x_66, 0, x_72);
return x_66;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
lean_dec(x_66);
x_74 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__15;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
else
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_66, 0);
lean_inc(x_79);
lean_dec(x_66);
x_3 = x_79;
goto block_56;
}
}
}
block_56:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
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
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__1;
x_16 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__4;
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Json_getNat_x3f(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__6;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_25 = lean_string_append(x_23, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__6;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
x_33 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__7;
x_34 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_14, x_33);
lean_dec(x_14);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_32);
x_35 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__10;
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Json_getStr_x3f(x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_32);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__12;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_43 = lean_string_append(x_41, x_42);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__12;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_32);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_37, 0, x_52);
return x_37;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_37, 0);
lean_inc(x_53);
lean_dec(x_37);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_32);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instFromJsonReservoirResp___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_Reservoir_pkgApiUrl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/packages/", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_pkgApiUrl___closed__2() {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_6 = lean_string_append(x_5, x_4);
x_7 = l_Lake_Reservoir_pkgApiUrl___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lake_uriEncode(x_2);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = l_Lake_Reservoir_pkgApiUrl___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Lake_uriEncode(x_3);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_14, x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Reservoir_pkgApiUrl(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
x_1 = lean_box(0);
x_2 = l_Lake_Reservoir_lakeHeaders___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("X-Reservoir-Api-Version:1.0.0", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Reservoir_lakeHeaders___closed__3;
x_2 = l_Lake_Reservoir_lakeHeaders___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Reservoir_lakeHeaders___closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Reservoir_lakeHeaders___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at_Lake_Reservoir_fetchPkg_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_56; 
lean_inc(x_1);
x_56 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
lean_dec(x_56);
x_61 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__13;
x_62 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_60, x_61);
lean_dec(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_box(0);
x_2 = x_63;
goto block_55;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Option_fromJson_x3f___at_Lake_ReservoirResp_fromJson_x3f___spec__1(x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__15;
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
x_70 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_71 = lean_string_append(x_69, x_70);
lean_ctor_set(x_65, 0, x_71);
return x_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_65, 0);
lean_inc(x_72);
lean_dec(x_65);
x_73 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__15;
x_74 = lean_string_append(x_73, x_72);
lean_dec(x_72);
x_75 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_76 = lean_string_append(x_74, x_75);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_65, 0);
lean_inc(x_78);
lean_dec(x_65);
x_2 = x_78;
goto block_55;
}
}
}
block_55:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lake_RegistryPkg_fromJson_x3f(x_1);
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
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__1;
x_15 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__4;
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Json_getNat_x3f(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__6;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_24 = lean_string_append(x_22, x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__6;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_dec(x_18);
x_32 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__7;
x_33 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_13, x_32);
lean_dec(x_13);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_31);
x_34 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__10;
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Json_getStr_x3f(x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_31);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__12;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_42 = lean_string_append(x_40, x_41);
lean_ctor_set(x_36, 0, x_42);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
x_44 = l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__12;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_36);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_31);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_36, 0, x_51);
return x_36;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_36, 0);
lean_inc(x_52);
lean_dec(x_36);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_31);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Reservoir lookup failed; server returned invalid JSON: ", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Reservoir responded with:\n", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Reservoir lookup failed; server returned unsupported JSON: ", 61, 61);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Reservoir lookup failed: ", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__1;
lean_inc(x_3);
x_7 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_10 = lean_string_append(x_9, x_1);
x_11 = l_Lake_Reservoir_pkgApiUrl___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_2);
x_14 = l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__2;
lean_inc(x_13);
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_8);
lean_dec(x_8);
x_17 = lean_string_append(x_16, x_9);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_4);
x_21 = lean_array_push(x_4, x_19);
x_22 = l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__3;
x_23 = lean_string_append(x_13, x_22);
x_24 = lean_string_utf8_byte_size(x_3);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_3, x_24, x_25);
x_27 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_3, x_26, x_24);
x_28 = lean_string_utf8_extract(x_3, x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_3);
x_29 = lean_string_append(x_23, x_28);
lean_dec(x_28);
x_30 = lean_string_append(x_29, x_9);
x_31 = 0;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_push(x_21, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
lean_dec(x_7);
x_37 = l_Lake_ReservoirResp_fromJson_x3f___at_Lake_Reservoir_fetchPkg_x3f___spec__1(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_40 = lean_string_append(x_39, x_1);
x_41 = l_Lake_Reservoir_pkgApiUrl___closed__2;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_string_append(x_42, x_2);
x_44 = l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__4;
lean_inc(x_43);
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_string_append(x_45, x_38);
lean_dec(x_38);
x_47 = lean_string_append(x_46, x_39);
x_48 = 3;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = lean_array_get_size(x_4);
x_51 = lean_array_push(x_4, x_49);
x_52 = l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__3;
x_53 = lean_string_append(x_43, x_52);
x_54 = lean_string_utf8_byte_size(x_3);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_3, x_54, x_55);
x_57 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_3, x_56, x_54);
x_58 = lean_string_utf8_extract(x_3, x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_3);
x_59 = lean_string_append(x_53, x_58);
lean_dec(x_58);
x_60 = lean_string_append(x_59, x_39);
x_61 = 0;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_array_push(x_51, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_50);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_5);
return x_65;
}
else
{
lean_object* x_66; 
lean_dec(x_3);
x_66 = lean_ctor_get(x_37, 0);
lean_inc(x_66);
lean_dec(x_37);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_ctor_set_tag(x_66, 1);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_4);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_5);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_4);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_5);
return x_73;
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_66);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_66, 0);
x_76 = lean_ctor_get(x_66, 1);
x_77 = lean_unsigned_to_nat(404u);
x_78 = lean_nat_dec_eq(x_75, x_77);
lean_dec(x_75);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_79 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_80 = lean_string_append(x_79, x_1);
x_81 = l_Lake_Reservoir_pkgApiUrl___closed__2;
x_82 = lean_string_append(x_80, x_81);
x_83 = lean_string_append(x_82, x_2);
x_84 = l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__5;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_string_append(x_85, x_76);
lean_dec(x_76);
x_87 = lean_string_append(x_86, x_79);
x_88 = 3;
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = lean_array_get_size(x_4);
x_91 = lean_array_push(x_4, x_89);
lean_ctor_set(x_66, 1, x_91);
lean_ctor_set(x_66, 0, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_66);
lean_ctor_set(x_92, 1, x_5);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_76);
x_93 = lean_box(0);
lean_ctor_set_tag(x_66, 0);
lean_ctor_set(x_66, 1, x_4);
lean_ctor_set(x_66, 0, x_93);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_66);
lean_ctor_set(x_94, 1, x_5);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_66, 0);
x_96 = lean_ctor_get(x_66, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_66);
x_97 = lean_unsigned_to_nat(404u);
x_98 = lean_nat_dec_eq(x_95, x_97);
lean_dec(x_95);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_99 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_100 = lean_string_append(x_99, x_1);
x_101 = l_Lake_Reservoir_pkgApiUrl___closed__2;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_string_append(x_102, x_2);
x_104 = l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__5;
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_string_append(x_105, x_96);
lean_dec(x_96);
x_107 = lean_string_append(x_106, x_99);
x_108 = 3;
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_108);
x_110 = lean_array_get_size(x_4);
x_111 = lean_array_push(x_4, x_109);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_5);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_96);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_4);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_5);
return x_116;
}
}
}
}
}
}
}
static lean_object* _init_l_Lake_Reservoir_fetchPkg_x3f___closed__1() {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lake_Reservoir_pkgApiUrl(x_1, x_2, x_3);
x_7 = l_Lake_Reservoir_lakeHeaders;
x_8 = l_Lake_getUrl(x_6, x_7, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lake_Reservoir_fetchPkg_x3f___lambda__1(x_2, x_3, x_11, x_12, x_10);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_9, 1);
x_18 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_19 = lean_string_append(x_18, x_2);
x_20 = l_Lake_Reservoir_pkgApiUrl___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_3);
x_23 = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = 3;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_array_push(x_17, x_26);
lean_ctor_set(x_9, 1, x_27);
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_31 = lean_string_append(x_30, x_2);
x_32 = l_Lake_Reservoir_pkgApiUrl___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_3);
x_35 = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
x_36 = lean_string_append(x_34, x_35);
x_37 = 3;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_push(x_29, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_8, 0, x_40);
return x_8;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_ctor_get(x_9, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_44 = x_9;
} else {
 lean_dec_ref(x_9);
 x_44 = lean_box(0);
}
x_45 = l_Lake_instInhabitedRegistrySrc___closed__1;
x_46 = lean_string_append(x_45, x_2);
x_47 = l_Lake_Reservoir_pkgApiUrl___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_3);
x_50 = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
x_51 = lean_string_append(x_49, x_50);
x_52 = 3;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_push(x_43, x_53);
if (lean_is_scalar(x_44)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_44;
}
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_41);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Reservoir_fetchPkg_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Reservoir_fetchPkg_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Env(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Reservoir(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Env(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedRegistrySrc___closed__1 = _init_l_Lake_instInhabitedRegistrySrc___closed__1();
lean_mark_persistent(l_Lake_instInhabitedRegistrySrc___closed__1);
l_Lake_instInhabitedRegistrySrc___closed__2 = _init_l_Lake_instInhabitedRegistrySrc___closed__2();
lean_mark_persistent(l_Lake_instInhabitedRegistrySrc___closed__2);
l_Lake_instInhabitedRegistrySrc = _init_l_Lake_instInhabitedRegistrySrc();
lean_mark_persistent(l_Lake_instInhabitedRegistrySrc);
l_Lake_RegistrySrc_instToJson___closed__1 = _init_l_Lake_RegistrySrc_instToJson___closed__1();
lean_mark_persistent(l_Lake_RegistrySrc_instToJson___closed__1);
l_Lake_RegistrySrc_instToJson = _init_l_Lake_RegistrySrc_instToJson();
lean_mark_persistent(l_Lake_RegistrySrc_instToJson);
l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1___closed__1 = _init_l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1___closed__1();
lean_mark_persistent(l_Option_fromJson_x3f___at_Lake_RegistrySrc_fromJson_x3f___spec__1___closed__1);
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
l_Lake_RegistrySrc_fromJson_x3f___closed__12 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__12();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__12);
l_Lake_RegistrySrc_fromJson_x3f___closed__13 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__13();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__13);
l_Lake_RegistrySrc_fromJson_x3f___closed__14 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__14();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__14);
l_Lake_RegistrySrc_fromJson_x3f___closed__15 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__15();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__15);
l_Lake_RegistrySrc_fromJson_x3f___closed__16 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__16();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__16);
l_Lake_RegistrySrc_fromJson_x3f___closed__17 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__17();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__17);
l_Lake_RegistrySrc_fromJson_x3f___closed__18 = _init_l_Lake_RegistrySrc_fromJson_x3f___closed__18();
lean_mark_persistent(l_Lake_RegistrySrc_fromJson_x3f___closed__18);
l_Lake_RegistrySrc_instFromJson___closed__1 = _init_l_Lake_RegistrySrc_instFromJson___closed__1();
lean_mark_persistent(l_Lake_RegistrySrc_instFromJson___closed__1);
l_Lake_RegistrySrc_instFromJson = _init_l_Lake_RegistrySrc_instFromJson();
lean_mark_persistent(l_Lake_RegistrySrc_instFromJson);
l_Lake_instInhabitedRegistryPkg___closed__1 = _init_l_Lake_instInhabitedRegistryPkg___closed__1();
lean_mark_persistent(l_Lake_instInhabitedRegistryPkg___closed__1);
l_Lake_instInhabitedRegistryPkg___closed__2 = _init_l_Lake_instInhabitedRegistryPkg___closed__2();
lean_mark_persistent(l_Lake_instInhabitedRegistryPkg___closed__2);
l_Lake_instInhabitedRegistryPkg = _init_l_Lake_instInhabitedRegistryPkg();
lean_mark_persistent(l_Lake_instInhabitedRegistryPkg);
l_Lake_RegistryPkg_gitSrc_x3f___closed__1 = _init_l_Lake_RegistryPkg_gitSrc_x3f___closed__1();
lean_mark_persistent(l_Lake_RegistryPkg_gitSrc_x3f___closed__1);
l_Lake_RegistryPkg_gitSrc_x3f___closed__2 = _init_l_Lake_RegistryPkg_gitSrc_x3f___closed__2();
lean_mark_persistent(l_Lake_RegistryPkg_gitSrc_x3f___closed__2);
l_Lake_RegistryPkg_gitSrc_x3f___closed__3 = _init_l_Lake_RegistryPkg_gitSrc_x3f___closed__3();
lean_mark_persistent(l_Lake_RegistryPkg_gitSrc_x3f___closed__3);
l_Lake_RegistryPkg_instToJson___closed__1 = _init_l_Lake_RegistryPkg_instToJson___closed__1();
lean_mark_persistent(l_Lake_RegistryPkg_instToJson___closed__1);
l_Lake_RegistryPkg_instToJson = _init_l_Lake_RegistryPkg_instToJson();
lean_mark_persistent(l_Lake_RegistryPkg_instToJson);
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
l_Lake_RegistryPkg_fromJson_x3f___closed__10 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__10();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__10);
l_Lake_RegistryPkg_fromJson_x3f___closed__11 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__11();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__11);
l_Lake_RegistryPkg_fromJson_x3f___closed__12 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__12();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__12);
l_Lake_RegistryPkg_fromJson_x3f___closed__13 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__13();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__13);
l_Lake_RegistryPkg_fromJson_x3f___closed__14 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__14();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__14);
l_Lake_RegistryPkg_fromJson_x3f___closed__15 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__15();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__15);
l_Lake_RegistryPkg_fromJson_x3f___closed__16 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__16();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__16);
l_Lake_RegistryPkg_fromJson_x3f___closed__17 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__17();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__17);
l_Lake_RegistryPkg_fromJson_x3f___closed__18 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__18();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__18);
l_Lake_RegistryPkg_fromJson_x3f___closed__19 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__19();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__19);
l_Lake_RegistryPkg_fromJson_x3f___closed__20 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__20();
l_Lake_RegistryPkg_fromJson_x3f___closed__21 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__21();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__21);
l_Lake_RegistryPkg_fromJson_x3f___closed__22 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__22();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__22);
l_Lake_RegistryPkg_fromJson_x3f___closed__23 = _init_l_Lake_RegistryPkg_fromJson_x3f___closed__23();
lean_mark_persistent(l_Lake_RegistryPkg_fromJson_x3f___closed__23);
l_Lake_RegistryPkg_instFromJson___closed__1 = _init_l_Lake_RegistryPkg_instFromJson___closed__1();
lean_mark_persistent(l_Lake_RegistryPkg_instFromJson___closed__1);
l_Lake_RegistryPkg_instFromJson = _init_l_Lake_RegistryPkg_instFromJson();
lean_mark_persistent(l_Lake_RegistryPkg_instFromJson);
l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_getUrl___spec__1___closed__1);
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
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__1 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__1();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__1);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__2 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__2();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__2);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__3 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__3();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__3);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__4 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__4();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__4);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__5 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__5();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__5);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__6 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__6();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__6);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__7 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__7();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__7);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__8 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__8();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__8);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__9 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__9();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__9);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__10 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__10();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__10);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__11 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__11();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__11);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__12 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__12();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__12);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__13 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__13();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__13);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__14 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__14();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__14);
l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__15 = _init_l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__15();
lean_mark_persistent(l_Lake_ReservoirResp_fromJson_x3f___rarg___closed__15);
l_Lake_Reservoir_pkgApiUrl___closed__1 = _init_l_Lake_Reservoir_pkgApiUrl___closed__1();
lean_mark_persistent(l_Lake_Reservoir_pkgApiUrl___closed__1);
l_Lake_Reservoir_pkgApiUrl___closed__2 = _init_l_Lake_Reservoir_pkgApiUrl___closed__2();
lean_mark_persistent(l_Lake_Reservoir_pkgApiUrl___closed__2);
l_Lake_Reservoir_lakeHeaders___closed__1 = _init_l_Lake_Reservoir_lakeHeaders___closed__1();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__1);
l_Lake_Reservoir_lakeHeaders___closed__2 = _init_l_Lake_Reservoir_lakeHeaders___closed__2();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__2);
l_Lake_Reservoir_lakeHeaders___closed__3 = _init_l_Lake_Reservoir_lakeHeaders___closed__3();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__3);
l_Lake_Reservoir_lakeHeaders___closed__4 = _init_l_Lake_Reservoir_lakeHeaders___closed__4();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__4);
l_Lake_Reservoir_lakeHeaders___closed__5 = _init_l_Lake_Reservoir_lakeHeaders___closed__5();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__5);
l_Lake_Reservoir_lakeHeaders = _init_l_Lake_Reservoir_lakeHeaders();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders);
l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__1 = _init_l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__1);
l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__2 = _init_l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__2);
l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__3 = _init_l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__3);
l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__4 = _init_l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__4);
l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__5 = _init_l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Reservoir_fetchPkg_x3f___lambda__1___closed__5);
l_Lake_Reservoir_fetchPkg_x3f___closed__1 = _init_l_Lake_Reservoir_fetchPkg_x3f___closed__1();
lean_mark_persistent(l_Lake_Reservoir_fetchPkg_x3f___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
