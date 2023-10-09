// Lean compiler output
// Module: Lean.Data.Lsp.Internal
// Imports: Init Lean.Expr Lean.Data.Lsp.Basic Lean.Server.Utils
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__3(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__13;
lean_object* l_List_join___rarg(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static lean_object* l_Lean_Lsp_instHashableRefIdent___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedRefIdent;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252_(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Lsp_instFromJsonModuleRefs___spec__7(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1(size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437____spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Lsp_instToJsonModuleRefs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_548____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_Lsp_instBEqRefIdent___closed__1;
static lean_object* l_Lean_Lsp_RefIdent_toString___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__18;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__12;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__16;
static lean_object* l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_129____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__5;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instInhabitedRefIdent___closed__1;
static lean_object* l_Lean_Lsp_RefIdent_fromString___closed__1;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__17;
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_RefIdent_toString___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__14;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Lsp_instToJsonModuleRefs___spec__5(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__9;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Lsp_instToJsonModuleRefs___spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromString___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__10;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__4;
static lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__3;
static lean_object* l_Lean_Lsp_RefIdent_fromString___closed__2;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Lsp_instFromJsonModuleRefs___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437____spec__1(size_t, size_t, size_t, lean_object*);
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRefIdent;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_28_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Lsp_instFromJsonModuleRefs___spec__7___boxed(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromString___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__15;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_toList___at_Lean_Lsp_instToJsonModuleRefs___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__1;
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRefIdent;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____boxed(lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__1;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__2;
static lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__3;
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1___closed__1;
LEAN_EXPORT uint64_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_129_(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__1;
static lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__2;
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Lsp_instFromJsonModuleRefs___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_28____boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1933_(lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__4(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__11;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__2;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__3;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__1;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Lsp_instFromJsonModuleRefs___spec__5(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_String_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__1;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__3(size_t, size_t, size_t, lean_object*);
static lean_object* l_Lean_Lsp_RefIdent_toString___closed__2;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
lean_object* l_String_take(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_28_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_name_eq(x_8, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_28____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_28_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqRefIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_28____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqRefIdent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instBEqRefIdent___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_129_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 1;
x_8 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1933_(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_129____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_129_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instHashableRefIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_129____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instHashableRefIdent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instHashableRefIdent___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedRefIdent___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedRefIdent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instInhabitedRefIdent___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("c:", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("f:", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 1;
x_4 = l_Lean_Name_toString(x_2, x_3);
x_5 = l_Lean_Lsp_RefIdent_toString___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = 1;
x_11 = l_Lean_Name_toString(x_9, x_10);
x_12 = l_Lean_Lsp_RefIdent_toString___closed__3;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("string must start with 'c:' or 'f:'", 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromString___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Lsp_RefIdent_toString___closed__1;
x_4 = lean_string_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Lsp_RefIdent_toString___closed__3;
x_6 = lean_string_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__2;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_fromString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[anonymous]", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_fromString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected a Name, got ", 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(2u);
lean_inc(x_1);
x_3 = l_String_take(x_1, x_2);
x_4 = l_String_drop(x_1, x_2);
x_5 = l_Lean_Lsp_RefIdent_fromString___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_7 = l_String_toName(x_4);
x_8 = l_Lean_Name_isAnonymous(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = l_Lean_Lsp_RefIdent_fromString___lambda__1(x_3, x_7);
lean_dec(x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = l_Lean_Lsp_RefIdent_fromString___closed__2;
x_11 = lean_string_append(x_10, x_4);
lean_dec(x_4);
x_12 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = l_Lean_Lsp_RefIdent_fromString___lambda__1(x_3, x_15);
lean_dec(x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromString___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_RefIdent_fromString___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 3);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 3);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_2, x_27);
x_29 = lean_array_uset(x_7, x_2, x_26);
x_2 = x_28;
x_3 = x_29;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_JsonNumber_fromNat(x_5);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__3(size_t x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_List_redLength___rarg(x_6);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
x_11 = l_List_toArrayAux___rarg(x_6, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_13, x_1, x_11);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_8, x_3, x_15);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonRefInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("usages", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonRefInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("definition", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonRefInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonRefInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_5, x_6, x_3);
x_8 = lean_array_get_size(x_7);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__3(x_6, x_9, x_6, x_7);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Json_mkObj(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 3);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 3);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Lsp_instToJsonRefInfo___closed__4;
x_31 = lean_array_push(x_30, x_21);
x_32 = lean_array_push(x_31, x_22);
x_33 = lean_array_push(x_32, x_23);
x_34 = lean_array_push(x_33, x_24);
x_35 = lean_array_push(x_34, x_26);
x_36 = lean_array_push(x_35, x_27);
x_37 = lean_array_push(x_36, x_28);
x_38 = lean_array_push(x_37, x_29);
x_39 = lean_array_get_size(x_38);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_40, x_6, x_38);
x_42 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_15);
x_46 = l_Lean_Json_mkObj(x_45);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__3(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_9 = l_Lean_Json_getNat_x3f(x_6);
lean_dec(x_6);
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
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected JSON array, got '", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; 
x_4 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__1;
return x_4;
}
case 4:
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2(x_7, x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
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
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_array_to_list(lean_box(0), x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_array_to_list(lean_box(0), x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_unsigned_to_nat(80u);
x_22 = l_Lean_Json_pretty(x_3, x_21);
x_23 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__2;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__3;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; 
x_6 = lean_array_uget(x_3, x_2);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = lean_array_get_size(x_7);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2(x_11, x_12, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_9);
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
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_array_to_list(lean_box(0), x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_9, x_2, x_18);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(80u);
x_24 = l_Lean_Json_pretty(x_6, x_23);
x_25 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__2;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__4(x_6, x_7, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(80u);
x_10 = l_Lean_Json_pretty(x_3, x_9);
x_11 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__2;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected list of length 8, not ", 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; 
x_6 = lean_array_uget(x_3, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_List_lengthTRAux___rarg(x_6, x_7);
x_9 = l_Nat_repr(x_8);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_List_lengthTRAux___rarg(x_6, x_16);
lean_dec(x_6);
x_18 = l_Nat_repr(x_17);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_15);
lean_dec(x_3);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_List_lengthTRAux___rarg(x_6, x_25);
lean_dec(x_6);
x_27 = l_Nat_repr(x_26);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_3);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_List_lengthTRAux___rarg(x_6, x_34);
lean_dec(x_6);
x_36 = l_Nat_repr(x_35);
x_37 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_33);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_3);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_List_lengthTRAux___rarg(x_6, x_43);
lean_dec(x_6);
x_45 = l_Nat_repr(x_44);
x_46 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_6, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_15, 0);
lean_inc(x_52);
lean_dec(x_15);
x_53 = lean_ctor_get(x_24, 0);
lean_inc(x_53);
lean_dec(x_24);
x_54 = lean_ctor_get(x_33, 0);
lean_inc(x_54);
lean_dec(x_33);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
lean_dec(x_42);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_array_uset(x_3, x_2, x_57);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_59 = l_List_lengthTRAux___rarg(x_6, x_57);
lean_dec(x_6);
x_60 = l_Nat_repr(x_59);
x_61 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_62 = lean_string_append(x_61, x_60);
lean_dec(x_60);
x_63 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_67 = l_List_lengthTRAux___rarg(x_6, x_57);
lean_dec(x_6);
x_68 = l_Nat_repr(x_67);
x_69 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_66);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_75 = l_List_lengthTRAux___rarg(x_6, x_57);
lean_dec(x_6);
x_76 = l_Nat_repr(x_75);
x_77 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_78 = lean_string_append(x_77, x_76);
lean_dec(x_76);
x_79 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_74, 1);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; lean_object* x_91; 
lean_dec(x_6);
x_83 = lean_ctor_get(x_56, 0);
lean_inc(x_83);
lean_dec(x_56);
x_84 = lean_ctor_get(x_66, 0);
lean_inc(x_84);
lean_dec(x_66);
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
lean_dec(x_74);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_51);
lean_ctor_set(x_86, 1, x_52);
lean_ctor_set(x_86, 2, x_53);
lean_ctor_set(x_86, 3, x_54);
x_87 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_87, 0, x_55);
lean_ctor_set(x_87, 1, x_83);
lean_ctor_set(x_87, 2, x_84);
lean_ctor_set(x_87, 3, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = 1;
x_90 = lean_usize_add(x_2, x_89);
x_91 = lean_array_uset(x_58, x_2, x_88);
x_2 = x_90;
x_3 = x_91;
goto _start;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_93 = l_List_lengthTRAux___rarg(x_6, x_57);
lean_dec(x_6);
x_94 = l_Nat_repr(x_93);
x_95 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_96 = lean_string_append(x_95, x_94);
lean_dec(x_94);
x_97 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_98 = lean_string_append(x_96, x_97);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
x_4 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__3(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
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
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5(x_10, x_11, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
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
lean_object* x_8; 
x_8 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_free_object(x_3);
x_9 = lean_box(0);
x_10 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_1, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_8);
lean_dec(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_List_lengthTRAux___rarg(x_12, x_13);
x_15 = l_Nat_repr(x_14);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_19 = lean_string_append(x_17, x_18);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_19);
return x_3;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_8);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_List_lengthTRAux___rarg(x_12, x_21);
lean_dec(x_12);
x_23 = l_Nat_repr(x_22);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_27 = lean_string_append(x_25, x_26);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_20);
lean_free_object(x_8);
lean_dec(x_1);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_List_lengthTRAux___rarg(x_12, x_29);
lean_dec(x_12);
x_31 = l_Nat_repr(x_30);
x_32 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_35 = lean_string_append(x_33, x_34);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_35);
return x_3;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_28);
lean_dec(x_20);
lean_free_object(x_8);
lean_dec(x_1);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_List_lengthTRAux___rarg(x_12, x_37);
lean_dec(x_12);
x_39 = l_Nat_repr(x_38);
x_40 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_43 = lean_string_append(x_41, x_42);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_43);
return x_3;
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_20);
lean_free_object(x_8);
lean_dec(x_1);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_List_lengthTRAux___rarg(x_12, x_45);
lean_dec(x_12);
x_47 = l_Nat_repr(x_46);
x_48 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_51 = lean_string_append(x_49, x_50);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_51);
return x_3;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_20);
lean_free_object(x_8);
lean_dec(x_1);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_List_lengthTRAux___rarg(x_12, x_53);
lean_dec(x_12);
x_55 = l_Nat_repr(x_54);
x_56 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_59 = lean_string_append(x_57, x_58);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_59);
return x_3;
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_52);
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_20);
lean_free_object(x_8);
lean_dec(x_1);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_List_lengthTRAux___rarg(x_12, x_61);
lean_dec(x_12);
x_63 = l_Nat_repr(x_62);
x_64 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_65 = lean_string_append(x_64, x_63);
lean_dec(x_63);
x_66 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_67 = lean_string_append(x_65, x_66);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_67);
return x_3;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_60);
lean_dec(x_52);
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_20);
lean_free_object(x_8);
lean_dec(x_1);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_List_lengthTRAux___rarg(x_12, x_69);
lean_dec(x_12);
x_71 = l_Nat_repr(x_70);
x_72 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_73 = lean_string_append(x_72, x_71);
lean_dec(x_71);
x_74 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_75 = lean_string_append(x_73, x_74);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_75);
return x_3;
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_free_object(x_3);
x_77 = lean_ctor_get(x_12, 0);
lean_inc(x_77);
lean_dec(x_12);
x_78 = lean_ctor_get(x_20, 0);
lean_inc(x_78);
lean_dec(x_20);
x_79 = lean_ctor_get(x_28, 0);
lean_inc(x_79);
lean_dec(x_28);
x_80 = lean_ctor_get(x_36, 0);
lean_inc(x_80);
lean_dec(x_36);
x_81 = lean_ctor_get(x_44, 0);
lean_inc(x_81);
lean_dec(x_44);
x_82 = lean_ctor_get(x_52, 0);
lean_inc(x_82);
lean_dec(x_52);
x_83 = lean_ctor_get(x_60, 0);
lean_inc(x_83);
lean_dec(x_60);
x_84 = lean_ctor_get(x_68, 0);
lean_inc(x_84);
lean_dec(x_68);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_78);
lean_ctor_set(x_85, 2, x_79);
lean_ctor_set(x_85, 3, x_80);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_83);
lean_ctor_set(x_86, 3, x_84);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_8, 0, x_87);
x_88 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_1, x_8);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_76);
lean_dec(x_68);
lean_dec(x_60);
lean_dec(x_52);
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_20);
lean_free_object(x_8);
lean_dec(x_1);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_List_lengthTRAux___rarg(x_12, x_89);
lean_dec(x_12);
x_91 = l_Nat_repr(x_90);
x_92 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_93 = lean_string_append(x_92, x_91);
lean_dec(x_91);
x_94 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_95 = lean_string_append(x_93, x_94);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_95);
return x_3;
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
else
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_8, 0);
lean_inc(x_96);
lean_dec(x_8);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_1);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_List_lengthTRAux___rarg(x_96, x_97);
x_99 = l_Nat_repr(x_98);
x_100 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
x_102 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_103 = lean_string_append(x_101, x_102);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_103);
return x_3;
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_96, 1);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_1);
x_105 = lean_unsigned_to_nat(0u);
x_106 = l_List_lengthTRAux___rarg(x_96, x_105);
lean_dec(x_96);
x_107 = l_Nat_repr(x_106);
x_108 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_109 = lean_string_append(x_108, x_107);
lean_dec(x_107);
x_110 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_111 = lean_string_append(x_109, x_110);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_111);
return x_3;
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_104, 1);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_104);
lean_dec(x_1);
x_113 = lean_unsigned_to_nat(0u);
x_114 = l_List_lengthTRAux___rarg(x_96, x_113);
lean_dec(x_96);
x_115 = l_Nat_repr(x_114);
x_116 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_117 = lean_string_append(x_116, x_115);
lean_dec(x_115);
x_118 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_119 = lean_string_append(x_117, x_118);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_119);
return x_3;
}
else
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_112, 1);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_112);
lean_dec(x_104);
lean_dec(x_1);
x_121 = lean_unsigned_to_nat(0u);
x_122 = l_List_lengthTRAux___rarg(x_96, x_121);
lean_dec(x_96);
x_123 = l_Nat_repr(x_122);
x_124 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_125 = lean_string_append(x_124, x_123);
lean_dec(x_123);
x_126 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_127 = lean_string_append(x_125, x_126);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_127);
return x_3;
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_120, 1);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_120);
lean_dec(x_112);
lean_dec(x_104);
lean_dec(x_1);
x_129 = lean_unsigned_to_nat(0u);
x_130 = l_List_lengthTRAux___rarg(x_96, x_129);
lean_dec(x_96);
x_131 = l_Nat_repr(x_130);
x_132 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_133 = lean_string_append(x_132, x_131);
lean_dec(x_131);
x_134 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_135 = lean_string_append(x_133, x_134);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_135);
return x_3;
}
else
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_128, 1);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_128);
lean_dec(x_120);
lean_dec(x_112);
lean_dec(x_104);
lean_dec(x_1);
x_137 = lean_unsigned_to_nat(0u);
x_138 = l_List_lengthTRAux___rarg(x_96, x_137);
lean_dec(x_96);
x_139 = l_Nat_repr(x_138);
x_140 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_141 = lean_string_append(x_140, x_139);
lean_dec(x_139);
x_142 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_143 = lean_string_append(x_141, x_142);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_143);
return x_3;
}
else
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_136, 1);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_136);
lean_dec(x_128);
lean_dec(x_120);
lean_dec(x_112);
lean_dec(x_104);
lean_dec(x_1);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_List_lengthTRAux___rarg(x_96, x_145);
lean_dec(x_96);
x_147 = l_Nat_repr(x_146);
x_148 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_149 = lean_string_append(x_148, x_147);
lean_dec(x_147);
x_150 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_151 = lean_string_append(x_149, x_150);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_151);
return x_3;
}
else
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_144, 1);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_144);
lean_dec(x_136);
lean_dec(x_128);
lean_dec(x_120);
lean_dec(x_112);
lean_dec(x_104);
lean_dec(x_1);
x_153 = lean_unsigned_to_nat(0u);
x_154 = l_List_lengthTRAux___rarg(x_96, x_153);
lean_dec(x_96);
x_155 = l_Nat_repr(x_154);
x_156 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_157 = lean_string_append(x_156, x_155);
lean_dec(x_155);
x_158 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_159 = lean_string_append(x_157, x_158);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_159);
return x_3;
}
else
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_152, 1);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_free_object(x_3);
x_161 = lean_ctor_get(x_96, 0);
lean_inc(x_161);
lean_dec(x_96);
x_162 = lean_ctor_get(x_104, 0);
lean_inc(x_162);
lean_dec(x_104);
x_163 = lean_ctor_get(x_112, 0);
lean_inc(x_163);
lean_dec(x_112);
x_164 = lean_ctor_get(x_120, 0);
lean_inc(x_164);
lean_dec(x_120);
x_165 = lean_ctor_get(x_128, 0);
lean_inc(x_165);
lean_dec(x_128);
x_166 = lean_ctor_get(x_136, 0);
lean_inc(x_166);
lean_dec(x_136);
x_167 = lean_ctor_get(x_144, 0);
lean_inc(x_167);
lean_dec(x_144);
x_168 = lean_ctor_get(x_152, 0);
lean_inc(x_168);
lean_dec(x_152);
x_169 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_169, 0, x_161);
lean_ctor_set(x_169, 1, x_162);
lean_ctor_set(x_169, 2, x_163);
lean_ctor_set(x_169, 3, x_164);
x_170 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_170, 0, x_165);
lean_ctor_set(x_170, 1, x_166);
lean_ctor_set(x_170, 2, x_167);
lean_ctor_set(x_170, 3, x_168);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_1, x_172);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_160);
lean_dec(x_152);
lean_dec(x_144);
lean_dec(x_136);
lean_dec(x_128);
lean_dec(x_120);
lean_dec(x_112);
lean_dec(x_104);
lean_dec(x_1);
x_174 = lean_unsigned_to_nat(0u);
x_175 = l_List_lengthTRAux___rarg(x_96, x_174);
lean_dec(x_96);
x_176 = l_Nat_repr(x_175);
x_177 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_178 = lean_string_append(x_177, x_176);
lean_dec(x_176);
x_179 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_180 = lean_string_append(x_178, x_179);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_180);
return x_3;
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
else
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_3, 0);
lean_inc(x_181);
lean_dec(x_3);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_box(0);
x_183 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_1, x_182);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_181, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_185 = x_181;
} else {
 lean_dec_ref(x_181);
 x_185 = lean_box(0);
}
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_185);
lean_dec(x_1);
x_186 = lean_unsigned_to_nat(0u);
x_187 = l_List_lengthTRAux___rarg(x_184, x_186);
x_188 = l_Nat_repr(x_187);
x_189 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_190 = lean_string_append(x_189, x_188);
lean_dec(x_188);
x_191 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_192 = lean_string_append(x_190, x_191);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_192);
return x_193;
}
else
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_184, 1);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_185);
lean_dec(x_1);
x_195 = lean_unsigned_to_nat(0u);
x_196 = l_List_lengthTRAux___rarg(x_184, x_195);
lean_dec(x_184);
x_197 = l_Nat_repr(x_196);
x_198 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_199 = lean_string_append(x_198, x_197);
lean_dec(x_197);
x_200 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_201 = lean_string_append(x_199, x_200);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
else
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_194, 1);
lean_inc(x_203);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_194);
lean_dec(x_185);
lean_dec(x_1);
x_204 = lean_unsigned_to_nat(0u);
x_205 = l_List_lengthTRAux___rarg(x_184, x_204);
lean_dec(x_184);
x_206 = l_Nat_repr(x_205);
x_207 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_208 = lean_string_append(x_207, x_206);
lean_dec(x_206);
x_209 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_210 = lean_string_append(x_208, x_209);
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_210);
return x_211;
}
else
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_203, 1);
lean_inc(x_212);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_203);
lean_dec(x_194);
lean_dec(x_185);
lean_dec(x_1);
x_213 = lean_unsigned_to_nat(0u);
x_214 = l_List_lengthTRAux___rarg(x_184, x_213);
lean_dec(x_184);
x_215 = l_Nat_repr(x_214);
x_216 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_217 = lean_string_append(x_216, x_215);
lean_dec(x_215);
x_218 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_219 = lean_string_append(x_217, x_218);
x_220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
else
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_212, 1);
lean_inc(x_221);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_194);
lean_dec(x_185);
lean_dec(x_1);
x_222 = lean_unsigned_to_nat(0u);
x_223 = l_List_lengthTRAux___rarg(x_184, x_222);
lean_dec(x_184);
x_224 = l_Nat_repr(x_223);
x_225 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_226 = lean_string_append(x_225, x_224);
lean_dec(x_224);
x_227 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_228 = lean_string_append(x_226, x_227);
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_228);
return x_229;
}
else
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_221, 1);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_221);
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_194);
lean_dec(x_185);
lean_dec(x_1);
x_231 = lean_unsigned_to_nat(0u);
x_232 = l_List_lengthTRAux___rarg(x_184, x_231);
lean_dec(x_184);
x_233 = l_Nat_repr(x_232);
x_234 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_235 = lean_string_append(x_234, x_233);
lean_dec(x_233);
x_236 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_237 = lean_string_append(x_235, x_236);
x_238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_238, 0, x_237);
return x_238;
}
else
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_230, 1);
lean_inc(x_239);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_230);
lean_dec(x_221);
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_194);
lean_dec(x_185);
lean_dec(x_1);
x_240 = lean_unsigned_to_nat(0u);
x_241 = l_List_lengthTRAux___rarg(x_184, x_240);
lean_dec(x_184);
x_242 = l_Nat_repr(x_241);
x_243 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_244 = lean_string_append(x_243, x_242);
lean_dec(x_242);
x_245 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_246 = lean_string_append(x_244, x_245);
x_247 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_247, 0, x_246);
return x_247;
}
else
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_239, 1);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_239);
lean_dec(x_230);
lean_dec(x_221);
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_194);
lean_dec(x_185);
lean_dec(x_1);
x_249 = lean_unsigned_to_nat(0u);
x_250 = l_List_lengthTRAux___rarg(x_184, x_249);
lean_dec(x_184);
x_251 = l_Nat_repr(x_250);
x_252 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_253 = lean_string_append(x_252, x_251);
lean_dec(x_251);
x_254 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_255 = lean_string_append(x_253, x_254);
x_256 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_256, 0, x_255);
return x_256;
}
else
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_248, 1);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_258 = lean_ctor_get(x_184, 0);
lean_inc(x_258);
lean_dec(x_184);
x_259 = lean_ctor_get(x_194, 0);
lean_inc(x_259);
lean_dec(x_194);
x_260 = lean_ctor_get(x_203, 0);
lean_inc(x_260);
lean_dec(x_203);
x_261 = lean_ctor_get(x_212, 0);
lean_inc(x_261);
lean_dec(x_212);
x_262 = lean_ctor_get(x_221, 0);
lean_inc(x_262);
lean_dec(x_221);
x_263 = lean_ctor_get(x_230, 0);
lean_inc(x_263);
lean_dec(x_230);
x_264 = lean_ctor_get(x_239, 0);
lean_inc(x_264);
lean_dec(x_239);
x_265 = lean_ctor_get(x_248, 0);
lean_inc(x_265);
lean_dec(x_248);
x_266 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_266, 0, x_258);
lean_ctor_set(x_266, 1, x_259);
lean_ctor_set(x_266, 2, x_260);
lean_ctor_set(x_266, 3, x_261);
x_267 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_267, 0, x_262);
lean_ctor_set(x_267, 1, x_263);
lean_ctor_set(x_267, 2, x_264);
lean_ctor_set(x_267, 3, x_265);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
if (lean_is_scalar(x_185)) {
 x_269 = lean_alloc_ctor(1, 1, 0);
} else {
 x_269 = x_185;
}
lean_ctor_set(x_269, 0, x_268);
x_270 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_1, x_269);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_257);
lean_dec(x_248);
lean_dec(x_239);
lean_dec(x_230);
lean_dec(x_221);
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_194);
lean_dec(x_185);
lean_dec(x_1);
x_271 = lean_unsigned_to_nat(0u);
x_272 = l_List_lengthTRAux___rarg(x_184, x_271);
lean_dec(x_184);
x_273 = l_Nat_repr(x_272);
x_274 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_275 = lean_string_append(x_274, x_273);
lean_dec(x_273);
x_276 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_277 = lean_string_append(x_275, x_276);
x_278 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_278, 0, x_277);
return x_278;
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1(size_t x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_List_redLength___rarg(x_6);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
x_11 = l_List_toArrayAux___rarg(x_6, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_13, x_1, x_11);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_8, x_3, x_15);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Lsp_instToJsonModuleRefs___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__3(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_toList___at_Lean_Lsp_instToJsonModuleRefs___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Lsp_instToJsonModuleRefs___spec__4(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Lsp_instToJsonModuleRefs___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = l_Lean_Lsp_RefIdent_toString(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_array_get_size(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_14, x_15, x_12);
x_17 = lean_array_get_size(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1(x_15, x_18, x_15, x_16);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_21);
x_22 = lean_box(0);
lean_ctor_set(x_1, 1, x_22);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_1);
x_25 = l_Lean_Json_mkObj(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_2);
x_1 = x_7;
x_2 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 3);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 3);
lean_inc(x_39);
lean_dec(x_35);
x_40 = l_Lean_Lsp_instToJsonRefInfo___closed__4;
x_41 = lean_array_push(x_40, x_31);
x_42 = lean_array_push(x_41, x_32);
x_43 = lean_array_push(x_42, x_33);
x_44 = lean_array_push(x_43, x_34);
x_45 = lean_array_push(x_44, x_36);
x_46 = lean_array_push(x_45, x_37);
x_47 = lean_array_push(x_46, x_38);
x_48 = lean_array_push(x_47, x_39);
x_49 = lean_array_get_size(x_48);
x_50 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_51 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_50, x_15, x_48);
x_52 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_1);
x_56 = l_Lean_Json_mkObj(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_10);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_2);
x_1 = x_7;
x_2 = x_58;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_1, 1);
x_61 = lean_ctor_get(x_5, 0);
x_62 = lean_ctor_get(x_5, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_5);
x_63 = l_Lean_Lsp_RefIdent_toString(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_array_get_size(x_65);
x_67 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_68 = 0;
x_69 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_67, x_68, x_65);
x_70 = lean_array_get_size(x_69);
x_71 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_72 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1(x_68, x_71, x_68, x_69);
x_73 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_box(0);
lean_ctor_set(x_1, 1, x_76);
lean_ctor_set(x_1, 0, x_75);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_1);
x_79 = l_Lean_Json_mkObj(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_63);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_2);
x_1 = x_60;
x_2 = x_81;
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; size_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_83 = lean_ctor_get(x_64, 0);
lean_inc(x_83);
lean_dec(x_64);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 3);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 3);
lean_inc(x_93);
lean_dec(x_89);
x_94 = l_Lean_Lsp_instToJsonRefInfo___closed__4;
x_95 = lean_array_push(x_94, x_85);
x_96 = lean_array_push(x_95, x_86);
x_97 = lean_array_push(x_96, x_87);
x_98 = lean_array_push(x_97, x_88);
x_99 = lean_array_push(x_98, x_90);
x_100 = lean_array_push(x_99, x_91);
x_101 = lean_array_push(x_100, x_92);
x_102 = lean_array_push(x_101, x_93);
x_103 = lean_array_get_size(x_102);
x_104 = lean_usize_of_nat(x_103);
lean_dec(x_103);
x_105 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_104, x_68, x_102);
x_106 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_1);
x_110 = l_Lean_Json_mkObj(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_63);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_2);
x_1 = x_60;
x_2 = x_112;
goto _start;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; size_t x_123; size_t x_124; lean_object* x_125; lean_object* x_126; size_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_114 = lean_ctor_get(x_1, 0);
x_115 = lean_ctor_get(x_1, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_1);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_118 = x_114;
} else {
 lean_dec_ref(x_114);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Lsp_RefIdent_toString(x_116);
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_dec(x_117);
x_122 = lean_array_get_size(x_121);
x_123 = lean_usize_of_nat(x_122);
lean_dec(x_122);
x_124 = 0;
x_125 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_123, x_124, x_121);
x_126 = lean_array_get_size(x_125);
x_127 = lean_usize_of_nat(x_126);
lean_dec(x_126);
x_128 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1(x_124, x_127, x_124, x_125);
x_129 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
if (lean_is_scalar(x_118)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_118;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l_Lean_Json_mkObj(x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_119);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_2);
x_1 = x_115;
x_2 = x_138;
goto _start;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; size_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_140 = lean_ctor_get(x_120, 0);
lean_inc(x_140);
lean_dec(x_120);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_141, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_141, 3);
lean_inc(x_145);
lean_dec(x_141);
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_dec(x_140);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 3);
lean_inc(x_150);
lean_dec(x_146);
x_151 = l_Lean_Lsp_instToJsonRefInfo___closed__4;
x_152 = lean_array_push(x_151, x_142);
x_153 = lean_array_push(x_152, x_143);
x_154 = lean_array_push(x_153, x_144);
x_155 = lean_array_push(x_154, x_145);
x_156 = lean_array_push(x_155, x_147);
x_157 = lean_array_push(x_156, x_148);
x_158 = lean_array_push(x_157, x_149);
x_159 = lean_array_push(x_158, x_150);
x_160 = lean_array_get_size(x_159);
x_161 = lean_usize_of_nat(x_160);
lean_dec(x_160);
x_162 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_161, x_124, x_159);
x_163 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_133);
x_167 = l_Lean_Json_mkObj(x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_119);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_2);
x_1 = x_115;
x_2 = x_169;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_HashMap_toList___at_Lean_Lsp_instToJsonModuleRefs___spec__2(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonModuleRefs___spec__5(x_2, x_3);
x_5 = l_Lean_Json_mkObj(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Lsp_instToJsonModuleRefs___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Lsp_instToJsonModuleRefs___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_28_(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Lsp_instFromJsonModuleRefs___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_129_(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_129_(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Lsp_instFromJsonModuleRefs___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Lean_AssocList_foldlM___at_Lean_Lsp_instFromJsonModuleRefs___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Lsp_instFromJsonModuleRefs___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Lsp_instFromJsonModuleRefs___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
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
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_28_(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_28_(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__6(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_129_(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_Lsp_instFromJsonModuleRefs___spec__3(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__6(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_129_(x_2);
lean_inc(x_23);
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__2(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_Lsp_instFromJsonModuleRefs___spec__3(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__6(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Lsp_instFromJsonModuleRefs___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__8(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_Lsp_RefIdent_fromString(x_5);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_13);
x_18 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_19 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1(x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_19);
x_25 = lean_box(0);
x_26 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_6, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_HashMap_insert___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(x_12, x_17, x_30);
x_1 = x_31;
x_2 = x_7;
goto _start;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_List_lengthTRAux___rarg(x_34, x_35);
x_37 = l_Nat_repr(x_36);
x_38 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_41 = lean_string_append(x_39, x_40);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_41);
return x_19;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_List_lengthTRAux___rarg(x_34, x_43);
lean_dec(x_34);
x_45 = l_Nat_repr(x_44);
x_46 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_49 = lean_string_append(x_47, x_48);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_49);
return x_19;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_42);
lean_free_object(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_List_lengthTRAux___rarg(x_34, x_51);
lean_dec(x_34);
x_53 = l_Nat_repr(x_52);
x_54 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_55 = lean_string_append(x_54, x_53);
lean_dec(x_53);
x_56 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_57 = lean_string_append(x_55, x_56);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_57);
return x_19;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_50);
lean_dec(x_42);
lean_free_object(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_List_lengthTRAux___rarg(x_34, x_59);
lean_dec(x_34);
x_61 = l_Nat_repr(x_60);
x_62 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
x_64 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_65 = lean_string_append(x_63, x_64);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_65);
return x_19;
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_42);
lean_free_object(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_List_lengthTRAux___rarg(x_34, x_67);
lean_dec(x_34);
x_69 = l_Nat_repr(x_68);
x_70 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_73 = lean_string_append(x_71, x_72);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_73);
return x_19;
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_66);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_42);
lean_free_object(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_List_lengthTRAux___rarg(x_34, x_75);
lean_dec(x_34);
x_77 = l_Nat_repr(x_76);
x_78 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_81 = lean_string_append(x_79, x_80);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_81);
return x_19;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_74, 1);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_42);
lean_free_object(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_List_lengthTRAux___rarg(x_34, x_83);
lean_dec(x_34);
x_85 = l_Nat_repr(x_84);
x_86 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_89 = lean_string_append(x_87, x_88);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_89);
return x_19;
}
else
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_42);
lean_free_object(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_List_lengthTRAux___rarg(x_34, x_91);
lean_dec(x_34);
x_93 = l_Nat_repr(x_92);
x_94 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_95 = lean_string_append(x_94, x_93);
lean_dec(x_93);
x_96 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_97 = lean_string_append(x_95, x_96);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_97);
return x_19;
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_90, 1);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_free_object(x_19);
x_99 = lean_ctor_get(x_34, 0);
lean_inc(x_99);
lean_dec(x_34);
x_100 = lean_ctor_get(x_42, 0);
lean_inc(x_100);
lean_dec(x_42);
x_101 = lean_ctor_get(x_50, 0);
lean_inc(x_101);
lean_dec(x_50);
x_102 = lean_ctor_get(x_58, 0);
lean_inc(x_102);
lean_dec(x_58);
x_103 = lean_ctor_get(x_66, 0);
lean_inc(x_103);
lean_dec(x_66);
x_104 = lean_ctor_get(x_74, 0);
lean_inc(x_104);
lean_dec(x_74);
x_105 = lean_ctor_get(x_82, 0);
lean_inc(x_105);
lean_dec(x_82);
x_106 = lean_ctor_get(x_90, 0);
lean_inc(x_106);
lean_dec(x_90);
x_107 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_100);
lean_ctor_set(x_107, 2, x_101);
lean_ctor_set(x_107, 3, x_102);
x_108 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_105);
lean_ctor_set(x_108, 3, x_106);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_24, 0, x_109);
x_110 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_6, x_24);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
return x_110;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_110, 0);
lean_inc(x_114);
lean_dec(x_110);
x_115 = l_Lean_HashMap_insert___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(x_12, x_17, x_114);
x_1 = x_115;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_98);
lean_dec(x_90);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_42);
lean_free_object(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_117 = lean_unsigned_to_nat(0u);
x_118 = l_List_lengthTRAux___rarg(x_34, x_117);
lean_dec(x_34);
x_119 = l_Nat_repr(x_118);
x_120 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_121 = lean_string_append(x_120, x_119);
lean_dec(x_119);
x_122 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_123 = lean_string_append(x_121, x_122);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_123);
return x_19;
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
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_24, 0);
lean_inc(x_124);
lean_dec(x_24);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_125 = lean_unsigned_to_nat(0u);
x_126 = l_List_lengthTRAux___rarg(x_124, x_125);
x_127 = l_Nat_repr(x_126);
x_128 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_129 = lean_string_append(x_128, x_127);
lean_dec(x_127);
x_130 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_131 = lean_string_append(x_129, x_130);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_131);
return x_19;
}
else
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_List_lengthTRAux___rarg(x_124, x_133);
lean_dec(x_124);
x_135 = l_Nat_repr(x_134);
x_136 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_137 = lean_string_append(x_136, x_135);
lean_dec(x_135);
x_138 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_139 = lean_string_append(x_137, x_138);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_139);
return x_19;
}
else
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_132, 1);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_132);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_141 = lean_unsigned_to_nat(0u);
x_142 = l_List_lengthTRAux___rarg(x_124, x_141);
lean_dec(x_124);
x_143 = l_Nat_repr(x_142);
x_144 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_145 = lean_string_append(x_144, x_143);
lean_dec(x_143);
x_146 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_147 = lean_string_append(x_145, x_146);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_147);
return x_19;
}
else
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_140, 1);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_140);
lean_dec(x_132);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_149 = lean_unsigned_to_nat(0u);
x_150 = l_List_lengthTRAux___rarg(x_124, x_149);
lean_dec(x_124);
x_151 = l_Nat_repr(x_150);
x_152 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_153 = lean_string_append(x_152, x_151);
lean_dec(x_151);
x_154 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_155 = lean_string_append(x_153, x_154);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_155);
return x_19;
}
else
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_148, 1);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_132);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_157 = lean_unsigned_to_nat(0u);
x_158 = l_List_lengthTRAux___rarg(x_124, x_157);
lean_dec(x_124);
x_159 = l_Nat_repr(x_158);
x_160 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_161 = lean_string_append(x_160, x_159);
lean_dec(x_159);
x_162 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_163 = lean_string_append(x_161, x_162);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_163);
return x_19;
}
else
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_156, 1);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_156);
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_132);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_165 = lean_unsigned_to_nat(0u);
x_166 = l_List_lengthTRAux___rarg(x_124, x_165);
lean_dec(x_124);
x_167 = l_Nat_repr(x_166);
x_168 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_169 = lean_string_append(x_168, x_167);
lean_dec(x_167);
x_170 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_171 = lean_string_append(x_169, x_170);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_171);
return x_19;
}
else
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_164, 1);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_164);
lean_dec(x_156);
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_132);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_173 = lean_unsigned_to_nat(0u);
x_174 = l_List_lengthTRAux___rarg(x_124, x_173);
lean_dec(x_124);
x_175 = l_Nat_repr(x_174);
x_176 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_177 = lean_string_append(x_176, x_175);
lean_dec(x_175);
x_178 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_179 = lean_string_append(x_177, x_178);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_179);
return x_19;
}
else
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_172, 1);
lean_inc(x_180);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_172);
lean_dec(x_164);
lean_dec(x_156);
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_132);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_181 = lean_unsigned_to_nat(0u);
x_182 = l_List_lengthTRAux___rarg(x_124, x_181);
lean_dec(x_124);
x_183 = l_Nat_repr(x_182);
x_184 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_185 = lean_string_append(x_184, x_183);
lean_dec(x_183);
x_186 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_187 = lean_string_append(x_185, x_186);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_187);
return x_19;
}
else
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_180, 1);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_free_object(x_19);
x_189 = lean_ctor_get(x_124, 0);
lean_inc(x_189);
lean_dec(x_124);
x_190 = lean_ctor_get(x_132, 0);
lean_inc(x_190);
lean_dec(x_132);
x_191 = lean_ctor_get(x_140, 0);
lean_inc(x_191);
lean_dec(x_140);
x_192 = lean_ctor_get(x_148, 0);
lean_inc(x_192);
lean_dec(x_148);
x_193 = lean_ctor_get(x_156, 0);
lean_inc(x_193);
lean_dec(x_156);
x_194 = lean_ctor_get(x_164, 0);
lean_inc(x_194);
lean_dec(x_164);
x_195 = lean_ctor_get(x_172, 0);
lean_inc(x_195);
lean_dec(x_172);
x_196 = lean_ctor_get(x_180, 0);
lean_inc(x_196);
lean_dec(x_180);
x_197 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_197, 0, x_189);
lean_ctor_set(x_197, 1, x_190);
lean_ctor_set(x_197, 2, x_191);
lean_ctor_set(x_197, 3, x_192);
x_198 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_194);
lean_ctor_set(x_198, 2, x_195);
lean_ctor_set(x_198, 3, x_196);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_6, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_201, 0);
lean_inc(x_205);
lean_dec(x_201);
x_206 = l_Lean_HashMap_insert___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(x_12, x_17, x_205);
x_1 = x_206;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_188);
lean_dec(x_180);
lean_dec(x_172);
lean_dec(x_164);
lean_dec(x_156);
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_132);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_208 = lean_unsigned_to_nat(0u);
x_209 = l_List_lengthTRAux___rarg(x_124, x_208);
lean_dec(x_124);
x_210 = l_Nat_repr(x_209);
x_211 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_212 = lean_string_append(x_211, x_210);
lean_dec(x_210);
x_213 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_214 = lean_string_append(x_212, x_213);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_214);
return x_19;
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
else
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_19, 0);
lean_inc(x_215);
lean_dec(x_19);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_box(0);
x_217 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_6, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(0, 1, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_218);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_217, 0);
lean_inc(x_221);
lean_dec(x_217);
x_222 = l_Lean_HashMap_insert___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(x_12, x_17, x_221);
x_1 = x_222;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_215, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 x_225 = x_215;
} else {
 lean_dec_ref(x_215);
 x_225 = lean_box(0);
}
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_225);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_226 = lean_unsigned_to_nat(0u);
x_227 = l_List_lengthTRAux___rarg(x_224, x_226);
x_228 = l_Nat_repr(x_227);
x_229 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_230 = lean_string_append(x_229, x_228);
lean_dec(x_228);
x_231 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_232 = lean_string_append(x_230, x_231);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
else
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_224, 1);
lean_inc(x_234);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_225);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_235 = lean_unsigned_to_nat(0u);
x_236 = l_List_lengthTRAux___rarg(x_224, x_235);
lean_dec(x_224);
x_237 = l_Nat_repr(x_236);
x_238 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_239 = lean_string_append(x_238, x_237);
lean_dec(x_237);
x_240 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_241 = lean_string_append(x_239, x_240);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_241);
return x_242;
}
else
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_234, 1);
lean_inc(x_243);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_234);
lean_dec(x_225);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_244 = lean_unsigned_to_nat(0u);
x_245 = l_List_lengthTRAux___rarg(x_224, x_244);
lean_dec(x_224);
x_246 = l_Nat_repr(x_245);
x_247 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_248 = lean_string_append(x_247, x_246);
lean_dec(x_246);
x_249 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_250 = lean_string_append(x_248, x_249);
x_251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_251, 0, x_250);
return x_251;
}
else
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_243, 1);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_243);
lean_dec(x_234);
lean_dec(x_225);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_253 = lean_unsigned_to_nat(0u);
x_254 = l_List_lengthTRAux___rarg(x_224, x_253);
lean_dec(x_224);
x_255 = l_Nat_repr(x_254);
x_256 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_257 = lean_string_append(x_256, x_255);
lean_dec(x_255);
x_258 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_259 = lean_string_append(x_257, x_258);
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_259);
return x_260;
}
else
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_252, 1);
lean_inc(x_261);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_252);
lean_dec(x_243);
lean_dec(x_234);
lean_dec(x_225);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_262 = lean_unsigned_to_nat(0u);
x_263 = l_List_lengthTRAux___rarg(x_224, x_262);
lean_dec(x_224);
x_264 = l_Nat_repr(x_263);
x_265 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_266 = lean_string_append(x_265, x_264);
lean_dec(x_264);
x_267 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_268 = lean_string_append(x_266, x_267);
x_269 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_269, 0, x_268);
return x_269;
}
else
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_261, 1);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_261);
lean_dec(x_252);
lean_dec(x_243);
lean_dec(x_234);
lean_dec(x_225);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_271 = lean_unsigned_to_nat(0u);
x_272 = l_List_lengthTRAux___rarg(x_224, x_271);
lean_dec(x_224);
x_273 = l_Nat_repr(x_272);
x_274 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_275 = lean_string_append(x_274, x_273);
lean_dec(x_273);
x_276 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_277 = lean_string_append(x_275, x_276);
x_278 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_278, 0, x_277);
return x_278;
}
else
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_270, 1);
lean_inc(x_279);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_270);
lean_dec(x_261);
lean_dec(x_252);
lean_dec(x_243);
lean_dec(x_234);
lean_dec(x_225);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_280 = lean_unsigned_to_nat(0u);
x_281 = l_List_lengthTRAux___rarg(x_224, x_280);
lean_dec(x_224);
x_282 = l_Nat_repr(x_281);
x_283 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_284 = lean_string_append(x_283, x_282);
lean_dec(x_282);
x_285 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_286 = lean_string_append(x_284, x_285);
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_286);
return x_287;
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_279, 1);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_279);
lean_dec(x_270);
lean_dec(x_261);
lean_dec(x_252);
lean_dec(x_243);
lean_dec(x_234);
lean_dec(x_225);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_289 = lean_unsigned_to_nat(0u);
x_290 = l_List_lengthTRAux___rarg(x_224, x_289);
lean_dec(x_224);
x_291 = l_Nat_repr(x_290);
x_292 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_293 = lean_string_append(x_292, x_291);
lean_dec(x_291);
x_294 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_295 = lean_string_append(x_293, x_294);
x_296 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_296, 0, x_295);
return x_296;
}
else
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_288, 1);
lean_inc(x_297);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_298 = lean_ctor_get(x_224, 0);
lean_inc(x_298);
lean_dec(x_224);
x_299 = lean_ctor_get(x_234, 0);
lean_inc(x_299);
lean_dec(x_234);
x_300 = lean_ctor_get(x_243, 0);
lean_inc(x_300);
lean_dec(x_243);
x_301 = lean_ctor_get(x_252, 0);
lean_inc(x_301);
lean_dec(x_252);
x_302 = lean_ctor_get(x_261, 0);
lean_inc(x_302);
lean_dec(x_261);
x_303 = lean_ctor_get(x_270, 0);
lean_inc(x_303);
lean_dec(x_270);
x_304 = lean_ctor_get(x_279, 0);
lean_inc(x_304);
lean_dec(x_279);
x_305 = lean_ctor_get(x_288, 0);
lean_inc(x_305);
lean_dec(x_288);
x_306 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_306, 0, x_298);
lean_ctor_set(x_306, 1, x_299);
lean_ctor_set(x_306, 2, x_300);
lean_ctor_set(x_306, 3, x_301);
x_307 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_307, 0, x_302);
lean_ctor_set(x_307, 1, x_303);
lean_ctor_set(x_307, 2, x_304);
lean_ctor_set(x_307, 3, x_305);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
if (lean_is_scalar(x_225)) {
 x_309 = lean_alloc_ctor(1, 1, 0);
} else {
 x_309 = x_225;
}
lean_ctor_set(x_309, 0, x_308);
x_310 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_6, x_309);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 x_312 = x_310;
} else {
 lean_dec_ref(x_310);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(0, 1, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_311);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_310, 0);
lean_inc(x_314);
lean_dec(x_310);
x_315 = l_Lean_HashMap_insert___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(x_12, x_17, x_314);
x_1 = x_315;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_297);
lean_dec(x_288);
lean_dec(x_279);
lean_dec(x_270);
lean_dec(x_261);
lean_dec(x_252);
lean_dec(x_243);
lean_dec(x_234);
lean_dec(x_225);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_317 = lean_unsigned_to_nat(0u);
x_318 = l_List_lengthTRAux___rarg(x_224, x_317);
lean_dec(x_224);
x_319 = l_Nat_repr(x_318);
x_320 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1;
x_321 = lean_string_append(x_320, x_319);
lean_dec(x_319);
x_322 = l_Lean_Lsp_RefIdent_toString___closed__2;
x_323 = lean_string_append(x_321, x_322);
x_324 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_324, 0, x_323);
return x_324;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getObj_x3f(x_1);
lean_dec(x_1);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(8u);
x_8 = l_Lean_mkHashMapImp___rarg(x_7);
x_9 = l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__8(x_8, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Lsp_instFromJsonModuleRefs___spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Lsp_instFromJsonModuleRefs___spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getObj_x3f(x_3);
lean_dec(x_3);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1___closed__1;
x_10 = l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__8(x_9, x_8);
return x_10;
}
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("version", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lsp", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LeanIleanInfoParams", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__2;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__3;
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__5;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__6;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__9;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__8;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__11;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__12;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("references", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__15;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__8;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__16;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__17;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__12;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_548____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__13;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__13;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__14;
x_14 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__18;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__18;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437____spec__1(size_t x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_List_redLength___rarg(x_6);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
x_11 = l_List_toArrayAux___rarg(x_6, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_13, x_1, x_11);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_8, x_3, x_15);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437____spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Lean_Lsp_RefIdent_toString(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_15, x_16, x_13);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437____spec__1(x_16, x_19, x_16, x_17);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_22);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_25 = l_Lean_Json_mkObj(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
x_2 = x_8;
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_29 = lean_ctor_get(x_12, 0);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 3);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 3);
lean_inc(x_39);
lean_dec(x_35);
x_40 = l_Lean_Lsp_instToJsonRefInfo___closed__4;
x_41 = lean_array_push(x_40, x_31);
x_42 = lean_array_push(x_41, x_32);
x_43 = lean_array_push(x_42, x_33);
x_44 = lean_array_push(x_43, x_34);
x_45 = lean_array_push(x_44, x_36);
x_46 = lean_array_push(x_45, x_37);
x_47 = lean_array_push(x_46, x_38);
x_48 = lean_array_push(x_47, x_39);
x_49 = lean_array_get_size(x_48);
x_50 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_51 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_50, x_16, x_48);
x_52 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_2);
x_56 = l_Lean_Json_mkObj(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_11);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_3);
x_2 = x_8;
x_3 = x_58;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_60 = lean_ctor_get(x_2, 1);
x_61 = lean_ctor_get(x_6, 0);
x_62 = lean_ctor_get(x_6, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_6);
x_63 = l_Lean_Lsp_RefIdent_toString(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_array_get_size(x_65);
x_67 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_68 = 0;
x_69 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_67, x_68, x_65);
x_70 = lean_array_get_size(x_69);
x_71 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_72 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437____spec__1(x_68, x_71, x_68, x_69);
x_73 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_75);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_2);
x_78 = l_Lean_Json_mkObj(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_63);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_3);
x_2 = x_60;
x_3 = x_80;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; size_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_82 = lean_ctor_get(x_64, 0);
lean_inc(x_82);
lean_dec(x_64);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 3);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 3);
lean_inc(x_92);
lean_dec(x_88);
x_93 = l_Lean_Lsp_instToJsonRefInfo___closed__4;
x_94 = lean_array_push(x_93, x_84);
x_95 = lean_array_push(x_94, x_85);
x_96 = lean_array_push(x_95, x_86);
x_97 = lean_array_push(x_96, x_87);
x_98 = lean_array_push(x_97, x_89);
x_99 = lean_array_push(x_98, x_90);
x_100 = lean_array_push(x_99, x_91);
x_101 = lean_array_push(x_100, x_92);
x_102 = lean_array_get_size(x_101);
x_103 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_104 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_103, x_68, x_101);
x_105 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_2);
x_109 = l_Lean_Json_mkObj(x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_63);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_3);
x_2 = x_60;
x_3 = x_111;
goto _start;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; size_t x_122; size_t x_123; lean_object* x_124; lean_object* x_125; size_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_113 = lean_ctor_get(x_2, 0);
x_114 = lean_ctor_get(x_2, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_2);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_117 = x_113;
} else {
 lean_dec_ref(x_113);
 x_117 = lean_box(0);
}
x_118 = l_Lean_Lsp_RefIdent_toString(x_115);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
lean_dec(x_116);
x_121 = lean_array_get_size(x_120);
x_122 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_123 = 0;
x_124 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_122, x_123, x_120);
x_125 = lean_array_get_size(x_124);
x_126 = lean_usize_of_nat(x_125);
lean_dec(x_125);
x_127 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437____spec__1(x_123, x_126, x_123, x_124);
x_128 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
if (lean_is_scalar(x_117)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_117;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
lean_inc(x_1);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_1);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_Lean_Json_mkObj(x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_118);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_3);
x_2 = x_114;
x_3 = x_136;
goto _start;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; size_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_138 = lean_ctor_get(x_119, 0);
lean_inc(x_138);
lean_dec(x_119);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 3);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_ctor_get(x_138, 1);
lean_inc(x_144);
lean_dec(x_138);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_144, 3);
lean_inc(x_148);
lean_dec(x_144);
x_149 = l_Lean_Lsp_instToJsonRefInfo___closed__4;
x_150 = lean_array_push(x_149, x_140);
x_151 = lean_array_push(x_150, x_141);
x_152 = lean_array_push(x_151, x_142);
x_153 = lean_array_push(x_152, x_143);
x_154 = lean_array_push(x_153, x_145);
x_155 = lean_array_push(x_154, x_146);
x_156 = lean_array_push(x_155, x_147);
x_157 = lean_array_push(x_156, x_148);
x_158 = lean_array_get_size(x_157);
x_159 = lean_usize_of_nat(x_158);
lean_dec(x_158);
x_160 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_159, x_123, x_157);
x_161 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_131);
x_165 = l_Lean_Json_mkObj(x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_118);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_3);
x_2 = x_114;
x_3 = x_167;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_JsonNumber_fromNat(x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_HashMap_toList___at_Lean_Lsp_instToJsonModuleRefs___spec__2(x_9);
x_11 = l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437____spec__2(x_7, x_10, x_7);
x_12 = l_Lean_Json_mkObj(x_11);
x_13 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__14;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_List_join___rarg(x_17);
x_19 = l_Lean_Json_mkObj(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437____spec__1(x_5, x_6, x_7, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1437_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanIleanInfoParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Internal(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instBEqRefIdent___closed__1 = _init_l_Lean_Lsp_instBEqRefIdent___closed__1();
lean_mark_persistent(l_Lean_Lsp_instBEqRefIdent___closed__1);
l_Lean_Lsp_instBEqRefIdent = _init_l_Lean_Lsp_instBEqRefIdent();
lean_mark_persistent(l_Lean_Lsp_instBEqRefIdent);
l_Lean_Lsp_instHashableRefIdent___closed__1 = _init_l_Lean_Lsp_instHashableRefIdent___closed__1();
lean_mark_persistent(l_Lean_Lsp_instHashableRefIdent___closed__1);
l_Lean_Lsp_instHashableRefIdent = _init_l_Lean_Lsp_instHashableRefIdent();
lean_mark_persistent(l_Lean_Lsp_instHashableRefIdent);
l_Lean_Lsp_instInhabitedRefIdent___closed__1 = _init_l_Lean_Lsp_instInhabitedRefIdent___closed__1();
lean_mark_persistent(l_Lean_Lsp_instInhabitedRefIdent___closed__1);
l_Lean_Lsp_instInhabitedRefIdent = _init_l_Lean_Lsp_instInhabitedRefIdent();
lean_mark_persistent(l_Lean_Lsp_instInhabitedRefIdent);
l_Lean_Lsp_RefIdent_toString___closed__1 = _init_l_Lean_Lsp_RefIdent_toString___closed__1();
lean_mark_persistent(l_Lean_Lsp_RefIdent_toString___closed__1);
l_Lean_Lsp_RefIdent_toString___closed__2 = _init_l_Lean_Lsp_RefIdent_toString___closed__2();
lean_mark_persistent(l_Lean_Lsp_RefIdent_toString___closed__2);
l_Lean_Lsp_RefIdent_toString___closed__3 = _init_l_Lean_Lsp_RefIdent_toString___closed__3();
lean_mark_persistent(l_Lean_Lsp_RefIdent_toString___closed__3);
l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__1 = _init_l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__1);
l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__2 = _init_l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Lsp_RefIdent_fromString___lambda__1___closed__2);
l_Lean_Lsp_RefIdent_fromString___closed__1 = _init_l_Lean_Lsp_RefIdent_fromString___closed__1();
lean_mark_persistent(l_Lean_Lsp_RefIdent_fromString___closed__1);
l_Lean_Lsp_RefIdent_fromString___closed__2 = _init_l_Lean_Lsp_RefIdent_fromString___closed__2();
lean_mark_persistent(l_Lean_Lsp_RefIdent_fromString___closed__2);
l_Lean_Lsp_instToJsonRefInfo___closed__1 = _init_l_Lean_Lsp_instToJsonRefInfo___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonRefInfo___closed__1);
l_Lean_Lsp_instToJsonRefInfo___closed__2 = _init_l_Lean_Lsp_instToJsonRefInfo___closed__2();
lean_mark_persistent(l_Lean_Lsp_instToJsonRefInfo___closed__2);
l_Lean_Lsp_instToJsonRefInfo___closed__3 = _init_l_Lean_Lsp_instToJsonRefInfo___closed__3();
lean_mark_persistent(l_Lean_Lsp_instToJsonRefInfo___closed__3);
l_Lean_Lsp_instToJsonRefInfo___closed__4 = _init_l_Lean_Lsp_instToJsonRefInfo___closed__4();
lean_mark_persistent(l_Lean_Lsp_instToJsonRefInfo___closed__4);
l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__1 = _init_l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__1();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__1);
l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__2 = _init_l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__2();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__2);
l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__3 = _init_l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__3();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__5___closed__1);
l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1___closed__1 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1___closed__1();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____spec__1___closed__1);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__1 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__1);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__2 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__2);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__3 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__3);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__4 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__4();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__4);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__5 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__5();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__5);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__6 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__6();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__6);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__7 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__7();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__7);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__8 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__8();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__8);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__9 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__9();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__9);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__10 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__10();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__10);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__11 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__11();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__11);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__12 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__12();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__12);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__13 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__13();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__13);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__14 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__14();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__14);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__15 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__15();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__15);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__16 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__16();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__16);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__17 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__17();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__17);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__18 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__18();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1252____closed__18);
l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__1 = _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__1);
l_Lean_Lsp_instFromJsonLeanIleanInfoParams = _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanIleanInfoParams);
l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__1 = _init_l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__1);
l_Lean_Lsp_instToJsonLeanIleanInfoParams = _init_l_Lean_Lsp_instToJsonLeanIleanInfoParams();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanIleanInfoParams);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
