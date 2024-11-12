// Lean compiler output
// Module: Lean.Data.Lsp.Internal
// Imports: Lean.Expr Lean.Data.Lsp.Basic
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
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__6;
static lean_object* l_Lean_Lsp_instHashableRefIdent___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedRefIdent;
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instFromJsonModuleRefs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instFromJsonModuleRefs___closed__3;
LEAN_EXPORT uint64_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_157_(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__3;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__4;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__5;
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1(size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Lsp_instToJsonModuleRefs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__1;
static lean_object* l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__2;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__3;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Lsp_instBEqRefIdent___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_44_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__4;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__5;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__4;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__2;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJsonRepr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr___closed__1;
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_1132____spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams___closed__1;
extern lean_object* l_Lean_instInhabitedJson;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268_(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams;
static lean_object* l_Lean_Lsp_instInhabitedRefIdent___closed__1;
static lean_object* l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr___closed__1;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_instInhabitedLocation;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_157____boxed(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__3;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__12;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(size_t, size_t, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Lsp_instFromJsonModuleRefs___spec__3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_instToJsonParentDecl;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_toJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_448_(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__4;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____lambda__1(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020_(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__2;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__9;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams;
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_458____spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__7;
static lean_object* l_Lean_Lsp_instInhabitedRefIdent___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__6___closed__1;
lean_object* l_List_flatMapTR_go___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_86____spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__18;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Lsp_instToJsonModuleRefs___spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Lsp_instFromJsonModuleRefs___spec__4(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2152____spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJsonRepr(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__3;
static lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2152____spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__13;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085_(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__15;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRefIdent;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__19;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs(lean_object*);
static lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Lsp_instToJsonModuleRefs___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__1;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_Lsp_RefInfo_instToJsonParentDecl___closed__1;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_RefIdent_instToJson___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__2(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721_(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__2;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__2;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRefIdent;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__6;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__14;
lean_object* l_Except_orElseLazy___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__8;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____lambda__1___boxed(lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__1;
lean_object* l_Lean_Json_Parser_any(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__17;
static lean_object* l_Lean_Lsp_instFromJsonModuleRefs___closed__2;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3(size_t, size_t, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Lsp_instFromJsonModuleRefs___spec__2(lean_object*);
static lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_44____boxed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2269_(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instFromJson;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6;
static lean_object* l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1683____spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_742_(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__6;
static lean_object* l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__1;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__16;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__9;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__8;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__6(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__2;
static lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams___closed__1;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__9;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1683____spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__1;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instToJson;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2152_(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__5;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__1;
static lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__3(size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__2(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__10;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__2;
static lean_object* l_Lean_Lsp_RefIdent_instFromJson___closed__1;
static lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914_(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_44_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_string_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_string_dec_eq(x_4, x_6);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_string_dec_eq(x_12, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_string_dec_eq(x_13, x_15);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_44____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_44_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_44____boxed), 2, 0);
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
LEAN_EXPORT uint64_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_157_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = 0;
x_5 = lean_string_hash(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = lean_string_hash(x_3);
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = 1;
x_12 = lean_string_hash(x_9);
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = lean_string_hash(x_10);
x_15 = lean_uint64_mix_hash(x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_157____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_157_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instHashableRefIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_157____boxed), 1, 0);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedRefIdent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_instInhabitedRefIdent___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedRefIdent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instInhabitedRefIdent___closed__2;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__2;
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("n", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__2;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_mk(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__3;
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Json_parseTagged(x_3, x_10, x_11, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_15 = l_Except_orElseLazy___rarg(x_12, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_19 = l_Except_orElseLazy___rarg(x_17, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_instInhabitedJson;
x_25 = l_outOfBounds___rarg(x_24);
x_26 = l_Lean_Json_getStr_x3f(x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_29 = l_Except_orElseLazy___rarg(x_26, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_33 = l_Except_orElseLazy___rarg(x_31, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_dec_lt(x_35, x_21);
lean_dec(x_21);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_20);
x_37 = l_outOfBounds___rarg(x_24);
x_38 = l_Lean_Json_getStr_x3f(x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_34);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_41 = l_Except_orElseLazy___rarg(x_38, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_45 = l_Except_orElseLazy___rarg(x_43, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_38, 0, x_48);
x_49 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_50 = l_Except_orElseLazy___rarg(x_38, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
lean_dec(x_38);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_34);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_55 = l_Except_orElseLazy___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fget(x_20, x_35);
lean_dec(x_20);
x_57 = l_Lean_Json_getStr_x3f(x_56);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
lean_dec(x_34);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_60 = l_Except_orElseLazy___rarg(x_57, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_64 = l_Except_orElseLazy___rarg(x_62, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_57);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_57, 0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_34);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_57, 0, x_67);
x_68 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_69 = l_Except_orElseLazy___rarg(x_57, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_57, 0);
lean_inc(x_70);
lean_dec(x_57);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_34);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_74 = l_Except_orElseLazy___rarg(x_72, x_73);
return x_74;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_array_fget(x_20, x_22);
x_76 = l_Lean_Json_getStr_x3f(x_75);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
lean_dec(x_21);
lean_dec(x_20);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_79 = l_Except_orElseLazy___rarg(x_76, x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_83 = l_Except_orElseLazy___rarg(x_81, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
lean_dec(x_76);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_dec_lt(x_85, x_21);
lean_dec(x_21);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_20);
x_87 = l_Lean_instInhabitedJson;
x_88 = l_outOfBounds___rarg(x_87);
x_89 = l_Lean_Json_getStr_x3f(x_88);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
lean_dec(x_84);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_92 = l_Except_orElseLazy___rarg(x_89, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_96 = l_Except_orElseLazy___rarg(x_94, x_95);
return x_96;
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_89, 0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_84);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_89, 0, x_99);
x_100 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_101 = l_Except_orElseLazy___rarg(x_89, x_100);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_89, 0);
lean_inc(x_102);
lean_dec(x_89);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_84);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_106 = l_Except_orElseLazy___rarg(x_104, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_array_fget(x_20, x_85);
lean_dec(x_20);
x_108 = l_Lean_Json_getStr_x3f(x_107);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
lean_dec(x_84);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_111 = l_Except_orElseLazy___rarg(x_108, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
lean_dec(x_108);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_115 = l_Except_orElseLazy___rarg(x_113, x_114);
return x_115;
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_108);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_108, 0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_84);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_108, 0, x_118);
x_119 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_120 = l_Except_orElseLazy___rarg(x_108, x_119);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_108, 0);
lean_inc(x_121);
lean_dec(x_108);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_84);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4;
x_125 = l_Except_orElseLazy___rarg(x_123, x_124);
return x_125;
}
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("m", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("i", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__2;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__6;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("f", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_box(0);
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__9;
x_4 = lean_unsigned_to_nat(2u);
x_5 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__8;
lean_inc(x_1);
x_6 = l_Lean_Json_parseTagged(x_1, x_3, x_4, x_5);
x_7 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__2;
x_8 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___boxed), 4, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_1);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Except_orElseLazy___rarg(x_6, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Except_orElseLazy___rarg(x_12, x_8);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_instInhabitedJson;
x_19 = l_outOfBounds___rarg(x_18);
x_20 = l_Lean_Json_getStr_x3f(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Except_orElseLazy___rarg(x_20, x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Except_orElseLazy___rarg(x_24, x_8);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_dec_lt(x_27, x_15);
lean_dec(x_15);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_14);
x_29 = l_outOfBounds___rarg(x_18);
x_30 = l_Lean_Json_getStr_x3f(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_26);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Except_orElseLazy___rarg(x_30, x_8);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Except_orElseLazy___rarg(x_34, x_8);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_30, 0, x_38);
x_39 = l_Except_orElseLazy___rarg(x_30, x_8);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Except_orElseLazy___rarg(x_42, x_8);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_array_fget(x_14, x_27);
lean_dec(x_14);
x_45 = l_Lean_Json_getStr_x3f(x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_26);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = l_Except_orElseLazy___rarg(x_45, x_8);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Except_orElseLazy___rarg(x_49, x_8);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_45);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_26);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_45, 0, x_53);
x_54 = l_Except_orElseLazy___rarg(x_45, x_8);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_26);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Except_orElseLazy___rarg(x_57, x_8);
return x_58;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_array_fget(x_14, x_16);
x_60 = l_Lean_Json_getStr_x3f(x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_15);
lean_dec(x_14);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Except_orElseLazy___rarg(x_60, x_8);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Except_orElseLazy___rarg(x_64, x_8);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
lean_dec(x_60);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_dec_lt(x_67, x_15);
lean_dec(x_15);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_14);
x_69 = l_Lean_instInhabitedJson;
x_70 = l_outOfBounds___rarg(x_69);
x_71 = l_Lean_Json_getStr_x3f(x_70);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
lean_dec(x_66);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Except_orElseLazy___rarg(x_71, x_8);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Except_orElseLazy___rarg(x_75, x_8);
return x_76;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_71);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_71, 0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_71, 0, x_79);
x_80 = l_Except_orElseLazy___rarg(x_71, x_8);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_66);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Except_orElseLazy___rarg(x_83, x_8);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_array_fget(x_14, x_67);
lean_dec(x_14);
x_86 = l_Lean_Json_getStr_x3f(x_85);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec(x_66);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = l_Except_orElseLazy___rarg(x_86, x_8);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Except_orElseLazy___rarg(x_90, x_8);
return x_91;
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_86);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_86, 0);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_66);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_86, 0, x_94);
x_95 = l_Except_orElseLazy___rarg(x_86, x_8);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_86, 0);
lean_inc(x_96);
lean_dec(x_86);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_66);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l_Except_orElseLazy___rarg(x_98, x_8);
return x_99;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_toJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_448_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__1;
lean_ctor_set(x_1, 1, x_5);
lean_ctor_set(x_1, 0, x_6);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Json_mkObj(x_12);
x_14 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__3;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_24 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Json_mkObj(x_28);
x_30 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__3;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
x_33 = l_Lean_Json_mkObj(x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_38);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_40 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__3;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Json_mkObj(x_44);
x_46 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__9;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
x_49 = l_Lean_Json_mkObj(x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_1);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_50);
x_53 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__1;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_51);
x_56 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__3;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Json_mkObj(x_60);
x_62 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__9;
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
x_65 = l_Lean_Json_mkObj(x_64);
return x_65;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_toJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_448_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJsonRepr(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJsonRepr(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268_(x_1);
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
x_8 = l_Lean_Lsp_RefIdent_fromJsonRepr(x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Lsp_RefIdent_fromJsonRepr(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_RefIdent_toJsonRepr(x_1);
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_toJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_448_(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instFromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_RefIdent_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_RefIdent_instFromJson___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instToJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_RefIdent_toJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_RefIdent_instToJson___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("range", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("selectionRange", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_742_(x_3);
x_11 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__2;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
x_14 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_742_(x_4);
x_15 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__3;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__4;
x_22 = l_List_flatMapTR_go___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_86____spec__1(x_20, x_21);
x_23 = l_Lean_Json_mkObj(x_22);
return x_23;
}
}
static lean_object* _init_l_Lean_Lsp_RefInfo_instToJsonParentDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefInfo_instToJsonParentDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_RefInfo_instToJsonParentDecl___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_RefInfo_instInhabitedLocation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_JsonNumber_fromNat(x_5);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Lean_JsonNumber_fromNat(x_10);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_box(0);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_16);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_10);
lean_ctor_set(x_9, 0, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_19, x_17);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec(x_5);
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_List_appendTR___rarg(x_20, x_17);
x_25 = lean_array_uset(x_7, x_2, x_24);
x_2 = x_23;
x_3 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 2);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set_tag(x_21, 3);
lean_ctor_set(x_21, 0, x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_17);
lean_ctor_set(x_33, 0, x_39);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_33);
lean_ctor_set(x_32, 0, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_32);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_41, x_17);
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_31, 1);
lean_inc(x_44);
lean_dec(x_31);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 1, x_17);
lean_ctor_set(x_44, 0, x_50);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 1, x_44);
lean_ctor_set(x_43, 0, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_43);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_52, x_17);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_21);
lean_ctor_set(x_54, 1, x_17);
x_55 = l_List_appendTR___rarg(x_54, x_42);
x_56 = l_List_appendTR___rarg(x_55, x_53);
x_57 = l_List_appendTR___rarg(x_20, x_56);
x_58 = lean_array_uset(x_7, x_2, x_57);
x_2 = x_23;
x_3 = x_58;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_43, 0);
x_61 = lean_ctor_get(x_43, 1);
x_62 = lean_ctor_get(x_44, 0);
x_63 = lean_ctor_get(x_44, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_44);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_17);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 1, x_64);
lean_ctor_set(x_43, 0, x_62);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_43);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_66, x_17);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_21);
lean_ctor_set(x_68, 1, x_17);
x_69 = l_List_appendTR___rarg(x_68, x_42);
x_70 = l_List_appendTR___rarg(x_69, x_67);
x_71 = l_List_appendTR___rarg(x_20, x_70);
x_72 = lean_array_uset(x_7, x_2, x_71);
x_2 = x_23;
x_3 = x_72;
goto _start;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_74 = lean_ctor_get(x_43, 0);
x_75 = lean_ctor_get(x_43, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_43);
x_76 = lean_ctor_get(x_44, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_44, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_78 = x_44;
} else {
 lean_dec_ref(x_44);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
 lean_ctor_set_tag(x_79, 1);
}
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_17);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_82, x_17);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_21);
lean_ctor_set(x_84, 1, x_17);
x_85 = l_List_appendTR___rarg(x_84, x_42);
x_86 = l_List_appendTR___rarg(x_85, x_83);
x_87 = l_List_appendTR___rarg(x_20, x_86);
x_88 = lean_array_uset(x_7, x_2, x_87);
x_2 = x_23;
x_3 = x_88;
goto _start;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_90 = lean_ctor_get(x_32, 0);
x_91 = lean_ctor_get(x_32, 1);
x_92 = lean_ctor_get(x_33, 0);
x_93 = lean_ctor_get(x_33, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_33);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_17);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_94);
lean_ctor_set(x_32, 0, x_92);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_32);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_96, x_17);
x_98 = lean_ctor_get(x_31, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_31, 1);
lean_inc(x_99);
lean_dec(x_31);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_105 = x_99;
} else {
 lean_dec_ref(x_99);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
 lean_ctor_set_tag(x_106, 1);
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_17);
if (lean_is_scalar(x_102)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_102;
 lean_ctor_set_tag(x_107, 1);
}
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_100);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_109, x_17);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_21);
lean_ctor_set(x_111, 1, x_17);
x_112 = l_List_appendTR___rarg(x_111, x_97);
x_113 = l_List_appendTR___rarg(x_112, x_110);
x_114 = l_List_appendTR___rarg(x_20, x_113);
x_115 = lean_array_uset(x_7, x_2, x_114);
x_2 = x_23;
x_3 = x_115;
goto _start;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_117 = lean_ctor_get(x_32, 0);
x_118 = lean_ctor_get(x_32, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_32);
x_119 = lean_ctor_get(x_33, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_33, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_121 = x_33;
} else {
 lean_dec_ref(x_33);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
 lean_ctor_set_tag(x_122, 1);
}
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_17);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_117);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_125, x_17);
x_127 = lean_ctor_get(x_31, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_31, 1);
lean_inc(x_128);
lean_dec(x_31);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_131 = x_127;
} else {
 lean_dec_ref(x_127);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_128, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_134 = x_128;
} else {
 lean_dec_ref(x_128);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_17);
if (lean_is_scalar(x_131)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_131;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_130);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_129);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_138, x_17);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_21);
lean_ctor_set(x_140, 1, x_17);
x_141 = l_List_appendTR___rarg(x_140, x_126);
x_142 = l_List_appendTR___rarg(x_141, x_139);
x_143 = l_List_appendTR___rarg(x_20, x_142);
x_144 = lean_array_uset(x_7, x_2, x_143);
x_2 = x_23;
x_3 = x_144;
goto _start;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_146 = lean_ctor_get(x_21, 0);
lean_inc(x_146);
lean_dec(x_21);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 2);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_150, 0, x_147);
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_148, 1);
lean_inc(x_152);
lean_dec(x_148);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_155 = x_151;
} else {
 lean_dec_ref(x_151);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_152, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_152, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_158 = x_152;
} else {
 lean_dec_ref(x_152);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
 lean_ctor_set_tag(x_159, 1);
}
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_17);
if (lean_is_scalar(x_155)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_155;
 lean_ctor_set_tag(x_160, 1);
}
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_162, x_17);
x_164 = lean_ctor_get(x_149, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_149, 1);
lean_inc(x_165);
lean_dec(x_149);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_168 = x_164;
} else {
 lean_dec_ref(x_164);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_165, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_171 = x_165;
} else {
 lean_dec_ref(x_165);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
 lean_ctor_set_tag(x_172, 1);
}
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_17);
if (lean_is_scalar(x_168)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_168;
 lean_ctor_set_tag(x_173, 1);
}
lean_ctor_set(x_173, 0, x_169);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_167);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_166);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_175, x_17);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_150);
lean_ctor_set(x_177, 1, x_17);
x_178 = l_List_appendTR___rarg(x_177, x_163);
x_179 = l_List_appendTR___rarg(x_178, x_176);
x_180 = l_List_appendTR___rarg(x_20, x_179);
x_181 = lean_array_uset(x_7, x_2, x_180);
x_2 = x_23;
x_3 = x_181;
goto _start;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; size_t x_193; size_t x_194; 
x_183 = lean_ctor_get(x_9, 0);
x_184 = lean_ctor_get(x_9, 1);
x_185 = lean_ctor_get(x_10, 0);
x_186 = lean_ctor_get(x_10, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_10);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_188);
lean_ctor_set(x_9, 0, x_185);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_184);
lean_ctor_set(x_189, 1, x_9);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_183);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_190, x_187);
x_192 = lean_ctor_get(x_5, 1);
lean_inc(x_192);
lean_dec(x_5);
x_193 = 1;
x_194 = lean_usize_add(x_2, x_193);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = l_List_appendTR___rarg(x_191, x_187);
x_196 = lean_array_uset(x_7, x_2, x_195);
x_2 = x_194;
x_3 = x_196;
goto _start;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_198 = lean_ctor_get(x_192, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_199 = x_192;
} else {
 lean_dec_ref(x_192);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_198, 2);
lean_inc(x_202);
lean_dec(x_198);
if (lean_is_scalar(x_199)) {
 x_203 = lean_alloc_ctor(3, 1, 0);
} else {
 x_203 = x_199;
 lean_ctor_set_tag(x_203, 3);
}
lean_ctor_set(x_203, 0, x_200);
x_204 = lean_ctor_get(x_201, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
lean_dec(x_201);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_208 = x_204;
} else {
 lean_dec_ref(x_204);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_205, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_205, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_211 = x_205;
} else {
 lean_dec_ref(x_205);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
 lean_ctor_set_tag(x_212, 1);
}
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_187);
if (lean_is_scalar(x_208)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_208;
 lean_ctor_set_tag(x_213, 1);
}
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_207);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_214);
x_216 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_215, x_187);
x_217 = lean_ctor_get(x_202, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_202, 1);
lean_inc(x_218);
lean_dec(x_202);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_221 = x_217;
} else {
 lean_dec_ref(x_217);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_218, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_218, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_224 = x_218;
} else {
 lean_dec_ref(x_218);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
 lean_ctor_set_tag(x_225, 1);
}
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_187);
if (lean_is_scalar(x_221)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_221;
 lean_ctor_set_tag(x_226, 1);
}
lean_ctor_set(x_226, 0, x_222);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_220);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_219);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_228, x_187);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_203);
lean_ctor_set(x_230, 1, x_187);
x_231 = l_List_appendTR___rarg(x_230, x_216);
x_232 = l_List_appendTR___rarg(x_231, x_229);
x_233 = l_List_appendTR___rarg(x_191, x_232);
x_234 = lean_array_uset(x_7, x_2, x_233);
x_2 = x_194;
x_3 = x_234;
goto _start;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; size_t x_248; size_t x_249; 
x_236 = lean_ctor_get(x_9, 0);
x_237 = lean_ctor_get(x_9, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_9);
x_238 = lean_ctor_get(x_10, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_10, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_240 = x_10;
} else {
 lean_dec_ref(x_10);
 x_240 = lean_box(0);
}
x_241 = lean_box(0);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_240;
 lean_ctor_set_tag(x_242, 1);
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_238);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_237);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_236);
lean_ctor_set(x_245, 1, x_244);
x_246 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_245, x_241);
x_247 = lean_ctor_get(x_5, 1);
lean_inc(x_247);
lean_dec(x_5);
x_248 = 1;
x_249 = lean_usize_add(x_2, x_248);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = l_List_appendTR___rarg(x_246, x_241);
x_251 = lean_array_uset(x_7, x_2, x_250);
x_2 = x_249;
x_3 = x_251;
goto _start;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_253 = lean_ctor_get(x_247, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 x_254 = x_247;
} else {
 lean_dec_ref(x_247);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_253, 2);
lean_inc(x_257);
lean_dec(x_253);
if (lean_is_scalar(x_254)) {
 x_258 = lean_alloc_ctor(3, 1, 0);
} else {
 x_258 = x_254;
 lean_ctor_set_tag(x_258, 3);
}
lean_ctor_set(x_258, 0, x_255);
x_259 = lean_ctor_get(x_256, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_256, 1);
lean_inc(x_260);
lean_dec(x_256);
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_259, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_263 = x_259;
} else {
 lean_dec_ref(x_259);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_260, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_260, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_266 = x_260;
} else {
 lean_dec_ref(x_260);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
 lean_ctor_set_tag(x_267, 1);
}
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_241);
if (lean_is_scalar(x_263)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_263;
 lean_ctor_set_tag(x_268, 1);
}
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_262);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_261);
lean_ctor_set(x_270, 1, x_269);
x_271 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_270, x_241);
x_272 = lean_ctor_get(x_257, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_257, 1);
lean_inc(x_273);
lean_dec(x_257);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_276 = x_272;
} else {
 lean_dec_ref(x_272);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_273, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_273, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_279 = x_273;
} else {
 lean_dec_ref(x_273);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
 lean_ctor_set_tag(x_280, 1);
}
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_241);
if (lean_is_scalar(x_276)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_276;
 lean_ctor_set_tag(x_281, 1);
}
lean_ctor_set(x_281, 0, x_277);
lean_ctor_set(x_281, 1, x_280);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_275);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_274);
lean_ctor_set(x_283, 1, x_282);
x_284 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_283, x_241);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_258);
lean_ctor_set(x_285, 1, x_241);
x_286 = l_List_appendTR___rarg(x_285, x_271);
x_287 = l_List_appendTR___rarg(x_286, x_284);
x_288 = l_List_appendTR___rarg(x_246, x_287);
x_289 = lean_array_uset(x_7, x_2, x_288);
x_2 = x_249;
x_3 = x_289;
goto _start;
}
}
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_array_mk(x_6);
x_10 = lean_array_size(x_9);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_10, x_1, x_9);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_15 = lean_array_uset(x_8, x_3, x_12);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonRefInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("usages", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonRefInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_size(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_4, x_5, x_3);
x_7 = lean_array_size(x_6);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__3(x_5, x_7, x_5, x_6);
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Json_mkObj(x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 0, x_27);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_21);
lean_ctor_set(x_20, 0, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_29, x_12);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_dec(x_18);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = l_List_appendTR___rarg(x_30, x_12);
x_33 = lean_array_mk(x_32);
x_34 = lean_array_size(x_33);
x_35 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_34, x_5, x_33);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_35);
x_36 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_2);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_13);
x_39 = l_Lean_Json_mkObj(x_38);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 2);
lean_inc(x_44);
lean_dec(x_41);
lean_ctor_set_tag(x_31, 3);
lean_ctor_set(x_31, 0, x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_12);
lean_ctor_set(x_46, 0, x_52);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 1, x_46);
lean_ctor_set(x_45, 0, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_45);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_54, x_12);
x_56 = lean_ctor_get(x_44, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_dec(x_44);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 1, x_12);
lean_ctor_set(x_57, 0, x_63);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_57);
lean_ctor_set(x_56, 0, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_56);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_65, x_12);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_31);
lean_ctor_set(x_67, 1, x_12);
x_68 = l_List_appendTR___rarg(x_67, x_55);
x_69 = l_List_appendTR___rarg(x_68, x_66);
x_70 = l_List_appendTR___rarg(x_30, x_69);
x_71 = lean_array_mk(x_70);
x_72 = lean_array_size(x_71);
x_73 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_72, x_5, x_71);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_73);
x_74 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_2);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_13);
x_77 = l_Lean_Json_mkObj(x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_78 = lean_ctor_get(x_56, 0);
x_79 = lean_ctor_get(x_56, 1);
x_80 = lean_ctor_get(x_57, 0);
x_81 = lean_ctor_get(x_57, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_57);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_12);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_82);
lean_ctor_set(x_56, 0, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_56);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_84, x_12);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_31);
lean_ctor_set(x_86, 1, x_12);
x_87 = l_List_appendTR___rarg(x_86, x_55);
x_88 = l_List_appendTR___rarg(x_87, x_85);
x_89 = l_List_appendTR___rarg(x_30, x_88);
x_90 = lean_array_mk(x_89);
x_91 = lean_array_size(x_90);
x_92 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_91, x_5, x_90);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_92);
x_93 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_2);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_13);
x_96 = l_Lean_Json_mkObj(x_95);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; size_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_97 = lean_ctor_get(x_56, 0);
x_98 = lean_ctor_get(x_56, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_56);
x_99 = lean_ctor_get(x_57, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_57, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_101 = x_57;
} else {
 lean_dec_ref(x_57);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
 lean_ctor_set_tag(x_102, 1);
}
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_12);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_97);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_105, x_12);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_31);
lean_ctor_set(x_107, 1, x_12);
x_108 = l_List_appendTR___rarg(x_107, x_55);
x_109 = l_List_appendTR___rarg(x_108, x_106);
x_110 = l_List_appendTR___rarg(x_30, x_109);
x_111 = lean_array_mk(x_110);
x_112 = lean_array_size(x_111);
x_113 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_112, x_5, x_111);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_113);
x_114 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_2);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_13);
x_117 = l_Lean_Json_mkObj(x_116);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; size_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_118 = lean_ctor_get(x_45, 0);
x_119 = lean_ctor_get(x_45, 1);
x_120 = lean_ctor_get(x_46, 0);
x_121 = lean_ctor_get(x_46, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_46);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_12);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 1, x_122);
lean_ctor_set(x_45, 0, x_120);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_45);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_124, x_12);
x_126 = lean_ctor_get(x_44, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_44, 1);
lean_inc(x_127);
lean_dec(x_44);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_133 = x_127;
} else {
 lean_dec_ref(x_127);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
 lean_ctor_set_tag(x_134, 1);
}
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_12);
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_130;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_131);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_129);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_128);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_137, x_12);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_31);
lean_ctor_set(x_139, 1, x_12);
x_140 = l_List_appendTR___rarg(x_139, x_125);
x_141 = l_List_appendTR___rarg(x_140, x_138);
x_142 = l_List_appendTR___rarg(x_30, x_141);
x_143 = lean_array_mk(x_142);
x_144 = lean_array_size(x_143);
x_145 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_144, x_5, x_143);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_145);
x_146 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_2);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_13);
x_149 = l_Lean_Json_mkObj(x_148);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; size_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_150 = lean_ctor_get(x_45, 0);
x_151 = lean_ctor_get(x_45, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_45);
x_152 = lean_ctor_get(x_46, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_46, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_154 = x_46;
} else {
 lean_dec_ref(x_46);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
 lean_ctor_set_tag(x_155, 1);
}
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_12);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_150);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_158, x_12);
x_160 = lean_ctor_get(x_44, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_44, 1);
lean_inc(x_161);
lean_dec(x_44);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_164 = x_160;
} else {
 lean_dec_ref(x_160);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_161, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_167 = x_161;
} else {
 lean_dec_ref(x_161);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
 lean_ctor_set_tag(x_168, 1);
}
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_12);
if (lean_is_scalar(x_164)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_164;
 lean_ctor_set_tag(x_169, 1);
}
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_163);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_162);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_171, x_12);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_31);
lean_ctor_set(x_173, 1, x_12);
x_174 = l_List_appendTR___rarg(x_173, x_159);
x_175 = l_List_appendTR___rarg(x_174, x_172);
x_176 = l_List_appendTR___rarg(x_30, x_175);
x_177 = lean_array_mk(x_176);
x_178 = lean_array_size(x_177);
x_179 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_178, x_5, x_177);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_179);
x_180 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_2);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_13);
x_183 = l_Lean_Json_mkObj(x_182);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; size_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_184 = lean_ctor_get(x_31, 0);
lean_inc(x_184);
lean_dec(x_31);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 2);
lean_inc(x_187);
lean_dec(x_184);
x_188 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_188, 0, x_185);
x_189 = lean_ctor_get(x_186, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
lean_dec(x_186);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_193 = x_189;
} else {
 lean_dec_ref(x_189);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_190, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_190, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_196 = x_190;
} else {
 lean_dec_ref(x_190);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
 lean_ctor_set_tag(x_197, 1);
}
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_12);
if (lean_is_scalar(x_193)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_193;
 lean_ctor_set_tag(x_198, 1);
}
lean_ctor_set(x_198, 0, x_194);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_192);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_191);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_200, x_12);
x_202 = lean_ctor_get(x_187, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_187, 1);
lean_inc(x_203);
lean_dec(x_187);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_206 = x_202;
} else {
 lean_dec_ref(x_202);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_203, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_203, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_209 = x_203;
} else {
 lean_dec_ref(x_203);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
 lean_ctor_set_tag(x_210, 1);
}
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_12);
if (lean_is_scalar(x_206)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_206;
 lean_ctor_set_tag(x_211, 1);
}
lean_ctor_set(x_211, 0, x_207);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_205);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_204);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_213, x_12);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_188);
lean_ctor_set(x_215, 1, x_12);
x_216 = l_List_appendTR___rarg(x_215, x_201);
x_217 = l_List_appendTR___rarg(x_216, x_214);
x_218 = l_List_appendTR___rarg(x_30, x_217);
x_219 = lean_array_mk(x_218);
x_220 = lean_array_size(x_219);
x_221 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_220, x_5, x_219);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_221);
x_222 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_2);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_13);
x_225 = l_Lean_Json_mkObj(x_224);
return x_225;
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_226 = lean_ctor_get(x_20, 0);
x_227 = lean_ctor_get(x_20, 1);
x_228 = lean_ctor_get(x_21, 0);
x_229 = lean_ctor_get(x_21, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_21);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_12);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_230);
lean_ctor_set(x_20, 0, x_228);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_227);
lean_ctor_set(x_231, 1, x_20);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_226);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_232, x_12);
x_234 = lean_ctor_get(x_18, 1);
lean_inc(x_234);
lean_dec(x_18);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; size_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_235 = l_List_appendTR___rarg(x_233, x_12);
x_236 = lean_array_mk(x_235);
x_237 = lean_array_size(x_236);
x_238 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_237, x_5, x_236);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_238);
x_239 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_2);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_13);
x_242 = l_Lean_Json_mkObj(x_241);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; size_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_243 = lean_ctor_get(x_234, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 x_244 = x_234;
} else {
 lean_dec_ref(x_234);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_243, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_243, 2);
lean_inc(x_247);
lean_dec(x_243);
if (lean_is_scalar(x_244)) {
 x_248 = lean_alloc_ctor(3, 1, 0);
} else {
 x_248 = x_244;
 lean_ctor_set_tag(x_248, 3);
}
lean_ctor_set(x_248, 0, x_245);
x_249 = lean_ctor_get(x_246, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
lean_dec(x_246);
x_251 = lean_ctor_get(x_249, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_253 = x_249;
} else {
 lean_dec_ref(x_249);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_250, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_250, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_256 = x_250;
} else {
 lean_dec_ref(x_250);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
 lean_ctor_set_tag(x_257, 1);
}
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_12);
if (lean_is_scalar(x_253)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_253;
 lean_ctor_set_tag(x_258, 1);
}
lean_ctor_set(x_258, 0, x_254);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_252);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_251);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_260, x_12);
x_262 = lean_ctor_get(x_247, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_247, 1);
lean_inc(x_263);
lean_dec(x_247);
x_264 = lean_ctor_get(x_262, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_266 = x_262;
} else {
 lean_dec_ref(x_262);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_269 = x_263;
} else {
 lean_dec_ref(x_263);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
 lean_ctor_set_tag(x_270, 1);
}
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_12);
if (lean_is_scalar(x_266)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_266;
 lean_ctor_set_tag(x_271, 1);
}
lean_ctor_set(x_271, 0, x_267);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_265);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_264);
lean_ctor_set(x_273, 1, x_272);
x_274 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_273, x_12);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_248);
lean_ctor_set(x_275, 1, x_12);
x_276 = l_List_appendTR___rarg(x_275, x_261);
x_277 = l_List_appendTR___rarg(x_276, x_274);
x_278 = l_List_appendTR___rarg(x_233, x_277);
x_279 = lean_array_mk(x_278);
x_280 = lean_array_size(x_279);
x_281 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_280, x_5, x_279);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_281);
x_282 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_2);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_13);
x_285 = l_Lean_Json_mkObj(x_284);
return x_285;
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_286 = lean_ctor_get(x_20, 0);
x_287 = lean_ctor_get(x_20, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_20);
x_288 = lean_ctor_get(x_21, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_21, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_290 = x_21;
} else {
 lean_dec_ref(x_21);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
 lean_ctor_set_tag(x_291, 1);
}
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_12);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_291);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_287);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_286);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_294, x_12);
x_296 = lean_ctor_get(x_18, 1);
lean_inc(x_296);
lean_dec(x_18);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; size_t x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_297 = l_List_appendTR___rarg(x_295, x_12);
x_298 = lean_array_mk(x_297);
x_299 = lean_array_size(x_298);
x_300 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_299, x_5, x_298);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_300);
x_301 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_2);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_13);
x_304 = l_Lean_Json_mkObj(x_303);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; size_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_305 = lean_ctor_get(x_296, 0);
lean_inc(x_305);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 x_306 = x_296;
} else {
 lean_dec_ref(x_296);
 x_306 = lean_box(0);
}
x_307 = lean_ctor_get(x_305, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_305, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_305, 2);
lean_inc(x_309);
lean_dec(x_305);
if (lean_is_scalar(x_306)) {
 x_310 = lean_alloc_ctor(3, 1, 0);
} else {
 x_310 = x_306;
 lean_ctor_set_tag(x_310, 3);
}
lean_ctor_set(x_310, 0, x_307);
x_311 = lean_ctor_get(x_308, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_308, 1);
lean_inc(x_312);
lean_dec(x_308);
x_313 = lean_ctor_get(x_311, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_315 = x_311;
} else {
 lean_dec_ref(x_311);
 x_315 = lean_box(0);
}
x_316 = lean_ctor_get(x_312, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_312, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_318 = x_312;
} else {
 lean_dec_ref(x_312);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
 lean_ctor_set_tag(x_319, 1);
}
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_12);
if (lean_is_scalar(x_315)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_315;
 lean_ctor_set_tag(x_320, 1);
}
lean_ctor_set(x_320, 0, x_316);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_314);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_313);
lean_ctor_set(x_322, 1, x_321);
x_323 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_322, x_12);
x_324 = lean_ctor_get(x_309, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_309, 1);
lean_inc(x_325);
lean_dec(x_309);
x_326 = lean_ctor_get(x_324, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_328 = x_324;
} else {
 lean_dec_ref(x_324);
 x_328 = lean_box(0);
}
x_329 = lean_ctor_get(x_325, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_325, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_331 = x_325;
} else {
 lean_dec_ref(x_325);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_331;
 lean_ctor_set_tag(x_332, 1);
}
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_12);
if (lean_is_scalar(x_328)) {
 x_333 = lean_alloc_ctor(1, 2, 0);
} else {
 x_333 = x_328;
 lean_ctor_set_tag(x_333, 1);
}
lean_ctor_set(x_333, 0, x_329);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_327);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_326);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_335, x_12);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_310);
lean_ctor_set(x_337, 1, x_12);
x_338 = l_List_appendTR___rarg(x_337, x_323);
x_339 = l_List_appendTR___rarg(x_338, x_336);
x_340 = l_List_appendTR___rarg(x_295, x_339);
x_341 = lean_array_mk(x_340);
x_342 = lean_array_size(x_341);
x_343 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_342, x_5, x_341);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_343);
x_344 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_2);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_13);
x_347 = l_Lean_Json_mkObj(x_346);
return x_347;
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_348 = lean_ctor_get(x_2, 0);
lean_inc(x_348);
lean_dec(x_2);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_ctor_get(x_350, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_350, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_354 = x_350;
} else {
 lean_dec_ref(x_350);
 x_354 = lean_box(0);
}
x_355 = lean_ctor_get(x_351, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_351, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_357 = x_351;
} else {
 lean_dec_ref(x_351);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_358 = x_357;
 lean_ctor_set_tag(x_358, 1);
}
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_12);
if (lean_is_scalar(x_354)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_354;
 lean_ctor_set_tag(x_359, 1);
}
lean_ctor_set(x_359, 0, x_355);
lean_ctor_set(x_359, 1, x_358);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_353);
lean_ctor_set(x_360, 1, x_359);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_352);
lean_ctor_set(x_361, 1, x_360);
x_362 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_361, x_12);
x_363 = lean_ctor_get(x_348, 1);
lean_inc(x_363);
lean_dec(x_348);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; size_t x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_364 = l_List_appendTR___rarg(x_362, x_12);
x_365 = lean_array_mk(x_364);
x_366 = lean_array_size(x_365);
x_367 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_366, x_5, x_365);
x_368 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_368, 0, x_367);
x_369 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_368);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_13);
x_372 = l_Lean_Json_mkObj(x_371);
return x_372;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; size_t x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_373 = lean_ctor_get(x_363, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_374 = x_363;
} else {
 lean_dec_ref(x_363);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_373, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_373, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_373, 2);
lean_inc(x_377);
lean_dec(x_373);
if (lean_is_scalar(x_374)) {
 x_378 = lean_alloc_ctor(3, 1, 0);
} else {
 x_378 = x_374;
 lean_ctor_set_tag(x_378, 3);
}
lean_ctor_set(x_378, 0, x_375);
x_379 = lean_ctor_get(x_376, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_376, 1);
lean_inc(x_380);
lean_dec(x_376);
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_379, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_383 = x_379;
} else {
 lean_dec_ref(x_379);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_380, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_380, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_386 = x_380;
} else {
 lean_dec_ref(x_380);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_387 = x_386;
 lean_ctor_set_tag(x_387, 1);
}
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_12);
if (lean_is_scalar(x_383)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_383;
 lean_ctor_set_tag(x_388, 1);
}
lean_ctor_set(x_388, 0, x_384);
lean_ctor_set(x_388, 1, x_387);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_382);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_381);
lean_ctor_set(x_390, 1, x_389);
x_391 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_390, x_12);
x_392 = lean_ctor_get(x_377, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_377, 1);
lean_inc(x_393);
lean_dec(x_377);
x_394 = lean_ctor_get(x_392, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_392, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_396 = x_392;
} else {
 lean_dec_ref(x_392);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_393, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_393, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_399 = x_393;
} else {
 lean_dec_ref(x_393);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_400 = x_399;
 lean_ctor_set_tag(x_400, 1);
}
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_12);
if (lean_is_scalar(x_396)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_396;
 lean_ctor_set_tag(x_401, 1);
}
lean_ctor_set(x_401, 0, x_397);
lean_ctor_set(x_401, 1, x_400);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_395);
lean_ctor_set(x_402, 1, x_401);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_394);
lean_ctor_set(x_403, 1, x_402);
x_404 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_403, x_12);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_378);
lean_ctor_set(x_405, 1, x_12);
x_406 = l_List_appendTR___rarg(x_405, x_391);
x_407 = l_List_appendTR___rarg(x_406, x_404);
x_408 = l_List_appendTR___rarg(x_362, x_407);
x_409 = lean_array_mk(x_408);
x_410 = lean_array_size(x_409);
x_411 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_410, x_5, x_409);
x_412 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_412, 0, x_411);
x_413 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_412);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_13);
x_416 = l_Lean_Json_mkObj(x_415);
return x_416;
}
}
}
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
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
lean_object* x_6; 
x_6 = lean_array_uget(x_3, x_2);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_6, x_7);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(80u);
x_15 = l_Lean_Json_pretty(x_6, x_14);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
case 4:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_uset(x_3, x_2, x_22);
x_24 = lean_array_size(x_21);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1683____spec__2(x_24, x_25, x_21);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = 1;
x_29 = lean_usize_add(x_2, x_28);
x_30 = lean_array_uset(x_23, x_2, x_27);
x_2 = x_29;
x_3 = x_30;
goto _start;
}
default: 
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_3);
x_32 = lean_unsigned_to_nat(80u);
lean_inc(x_6);
x_33 = l_Lean_Json_pretty(x_6, x_32);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_6, 0);
lean_dec(x_35);
x_36 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_37 = lean_string_append(x_36, x_33);
lean_dec(x_33);
x_38 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_39 = lean_string_append(x_37, x_38);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_39);
return x_6;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_6);
x_40 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_41 = lean_string_append(x_40, x_33);
lean_dec(x_33);
x_42 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_3, x_4);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(80u);
x_12 = l_Lean_Json_pretty(x_3, x_11);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
case 4:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_array_size(x_18);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2(x_19, x_20, x_18);
return x_21;
}
default: 
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(80u);
lean_inc(x_3);
x_23 = l_Lean_Json_pretty(x_3, x_22);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 0);
lean_dec(x_25);
x_26 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_27 = lean_string_append(x_26, x_23);
lean_dec(x_23);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_29 = lean_string_append(x_27, x_28);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
x_30 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_31 = lean_string_append(x_30, x_23);
lean_dec(x_23);
x_32 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected list of length 4, not ", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(4u);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fget(x_1, x_6);
x_8 = l_Lean_Json_getNat_x3f(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_3);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_array_fget(x_1, x_13);
x_15 = l_Lean_Json_getNat_x3f(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_array_fget(x_1, x_20);
x_22 = l_Lean_Json_getNat_x3f(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_array_fget(x_1, x_27);
x_29 = l_Lean_Json_getNat_x3f(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_265; uint8_t x_266; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_12);
lean_ctor_set(x_35, 1, x_19);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_265 = lean_unsigned_to_nat(13u);
x_266 = lean_nat_dec_eq(x_3, x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_3);
x_267 = lean_box(0);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_37);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set(x_29, 0, x_268);
return x_29;
}
else
{
uint8_t x_269; 
lean_free_object(x_29);
x_269 = lean_nat_dec_lt(x_4, x_3);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = l_Lean_instInhabitedJson;
x_271 = l_outOfBounds___rarg(x_270);
x_38 = x_271;
goto block_264;
}
else
{
lean_object* x_272; 
x_272 = lean_array_fget(x_1, x_4);
x_38 = x_272;
goto block_264;
}
}
block_264:
{
lean_object* x_39; 
x_39 = l_Lean_Json_getStr_x3f(x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_37);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_unsigned_to_nat(9u);
x_46 = lean_nat_dec_lt(x_3, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_39);
x_47 = lean_unsigned_to_nat(5u);
x_48 = lean_array_fget(x_1, x_47);
x_49 = l_Lean_Json_getNat_x3f(x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_unsigned_to_nat(6u);
x_55 = lean_array_fget(x_1, x_54);
x_56 = l_Lean_Json_getNat_x3f(x_55);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_53);
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_3);
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
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_unsigned_to_nat(7u);
x_62 = lean_array_fget(x_1, x_61);
x_63 = l_Lean_Json_getNat_x3f(x_62);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
lean_dec(x_60);
lean_dec(x_53);
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_unsigned_to_nat(8u);
x_69 = lean_array_fget(x_1, x_68);
x_70 = l_Lean_Json_getNat_x3f(x_69);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
lean_dec(x_67);
lean_dec(x_60);
lean_dec(x_53);
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_70, 0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_53);
lean_ctor_set(x_76, 1, x_60);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_unsigned_to_nat(13u);
x_80 = lean_nat_dec_lt(x_3, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_free_object(x_70);
lean_dec(x_3);
x_81 = lean_array_fget(x_1, x_45);
x_82 = l_Lean_Json_getNat_x3f(x_81);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_78);
lean_dec(x_44);
lean_dec(x_37);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_unsigned_to_nat(10u);
x_88 = lean_array_fget(x_1, x_87);
x_89 = l_Lean_Json_getNat_x3f(x_88);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
lean_dec(x_86);
lean_dec(x_78);
lean_dec(x_44);
lean_dec(x_37);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_unsigned_to_nat(11u);
x_95 = lean_array_fget(x_1, x_94);
x_96 = l_Lean_Json_getNat_x3f(x_95);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
lean_dec(x_93);
lean_dec(x_86);
lean_dec(x_78);
lean_dec(x_44);
lean_dec(x_37);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
return x_96;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_unsigned_to_nat(12u);
x_102 = lean_array_fget(x_1, x_101);
x_103 = l_Lean_Json_getNat_x3f(x_102);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
lean_dec(x_100);
lean_dec(x_93);
lean_dec(x_86);
lean_dec(x_78);
lean_dec(x_44);
lean_dec(x_37);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_103);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_103, 0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_86);
lean_ctor_set(x_109, 1, x_93);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_112, 0, x_44);
lean_ctor_set(x_112, 1, x_78);
lean_ctor_set(x_112, 2, x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_37);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_103, 0, x_114);
return x_103;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_103, 0);
lean_inc(x_115);
lean_dec(x_103);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_86);
lean_ctor_set(x_116, 1, x_93);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_100);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_44);
lean_ctor_set(x_119, 1, x_78);
lean_ctor_set(x_119, 2, x_118);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_37);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_78);
lean_dec(x_44);
lean_dec(x_37);
x_123 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_124 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1;
x_125 = lean_string_append(x_124, x_123);
lean_dec(x_123);
x_126 = l_Lean_Lsp_instInhabitedRefIdent___closed__1;
x_127 = lean_string_append(x_125, x_126);
lean_ctor_set_tag(x_70, 0);
lean_ctor_set(x_70, 0, x_127);
return x_70;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_128 = lean_ctor_get(x_70, 0);
lean_inc(x_128);
lean_dec(x_70);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_53);
lean_ctor_set(x_129, 1, x_60);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_67);
lean_ctor_set(x_130, 1, x_128);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_unsigned_to_nat(13u);
x_133 = lean_nat_dec_lt(x_3, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_3);
x_134 = lean_array_fget(x_1, x_45);
x_135 = l_Lean_Json_getNat_x3f(x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_131);
lean_dec(x_44);
lean_dec(x_37);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_135, 0);
lean_inc(x_139);
lean_dec(x_135);
x_140 = lean_unsigned_to_nat(10u);
x_141 = lean_array_fget(x_1, x_140);
x_142 = l_Lean_Json_getNat_x3f(x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_139);
lean_dec(x_131);
lean_dec(x_44);
lean_dec(x_37);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
lean_dec(x_142);
x_147 = lean_unsigned_to_nat(11u);
x_148 = lean_array_fget(x_1, x_147);
x_149 = l_Lean_Json_getNat_x3f(x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_146);
lean_dec(x_139);
lean_dec(x_131);
lean_dec(x_44);
lean_dec(x_37);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 1, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_150);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_149, 0);
lean_inc(x_153);
lean_dec(x_149);
x_154 = lean_unsigned_to_nat(12u);
x_155 = lean_array_fget(x_1, x_154);
x_156 = l_Lean_Json_getNat_x3f(x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_153);
lean_dec(x_146);
lean_dec(x_139);
lean_dec(x_131);
lean_dec(x_44);
lean_dec(x_37);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(0, 1, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_157);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_160 = lean_ctor_get(x_156, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_161 = x_156;
} else {
 lean_dec_ref(x_156);
 x_161 = lean_box(0);
}
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_139);
lean_ctor_set(x_162, 1, x_146);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_153);
lean_ctor_set(x_163, 1, x_160);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_44);
lean_ctor_set(x_165, 1, x_131);
lean_ctor_set(x_165, 2, x_164);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_37);
lean_ctor_set(x_167, 1, x_166);
if (lean_is_scalar(x_161)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_161;
}
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_131);
lean_dec(x_44);
lean_dec(x_37);
x_169 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_170 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1;
x_171 = lean_string_append(x_170, x_169);
lean_dec(x_169);
x_172 = l_Lean_Lsp_instInhabitedRefIdent___closed__1;
x_173 = lean_string_append(x_171, x_172);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_173);
return x_174;
}
}
}
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_44);
lean_dec(x_37);
x_175 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_176 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1;
x_177 = lean_string_append(x_176, x_175);
lean_dec(x_175);
x_178 = l_Lean_Lsp_instInhabitedRefIdent___closed__1;
x_179 = lean_string_append(x_177, x_178);
lean_ctor_set_tag(x_39, 0);
lean_ctor_set(x_39, 0, x_179);
return x_39;
}
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_39, 0);
lean_inc(x_180);
lean_dec(x_39);
x_181 = lean_unsigned_to_nat(9u);
x_182 = lean_nat_dec_lt(x_3, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_unsigned_to_nat(5u);
x_184 = lean_array_fget(x_1, x_183);
x_185 = l_Lean_Json_getNat_x3f(x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_180);
lean_dec(x_37);
lean_dec(x_3);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(0, 1, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_186);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_185, 0);
lean_inc(x_189);
lean_dec(x_185);
x_190 = lean_unsigned_to_nat(6u);
x_191 = lean_array_fget(x_1, x_190);
x_192 = l_Lean_Json_getNat_x3f(x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_189);
lean_dec(x_180);
lean_dec(x_37);
lean_dec(x_3);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(0, 1, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_193);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
lean_dec(x_192);
x_197 = lean_unsigned_to_nat(7u);
x_198 = lean_array_fget(x_1, x_197);
x_199 = l_Lean_Json_getNat_x3f(x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_196);
lean_dec(x_189);
lean_dec(x_180);
lean_dec(x_37);
lean_dec(x_3);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 x_201 = x_199;
} else {
 lean_dec_ref(x_199);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 1, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_200);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_199, 0);
lean_inc(x_203);
lean_dec(x_199);
x_204 = lean_unsigned_to_nat(8u);
x_205 = lean_array_fget(x_1, x_204);
x_206 = l_Lean_Json_getNat_x3f(x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_203);
lean_dec(x_196);
lean_dec(x_189);
lean_dec(x_180);
lean_dec(x_37);
lean_dec(x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(0, 1, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_207);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_210 = lean_ctor_get(x_206, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_211 = x_206;
} else {
 lean_dec_ref(x_206);
 x_211 = lean_box(0);
}
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_189);
lean_ctor_set(x_212, 1, x_196);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_203);
lean_ctor_set(x_213, 1, x_210);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_unsigned_to_nat(13u);
x_216 = lean_nat_dec_lt(x_3, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_211);
lean_dec(x_3);
x_217 = lean_array_fget(x_1, x_181);
x_218 = l_Lean_Json_getNat_x3f(x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_214);
lean_dec(x_180);
lean_dec(x_37);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_220 = x_218;
} else {
 lean_dec_ref(x_218);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 1, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_219);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_218, 0);
lean_inc(x_222);
lean_dec(x_218);
x_223 = lean_unsigned_to_nat(10u);
x_224 = lean_array_fget(x_1, x_223);
x_225 = l_Lean_Json_getNat_x3f(x_224);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_222);
lean_dec(x_214);
lean_dec(x_180);
lean_dec(x_37);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 x_227 = x_225;
} else {
 lean_dec_ref(x_225);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 1, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_226);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_225, 0);
lean_inc(x_229);
lean_dec(x_225);
x_230 = lean_unsigned_to_nat(11u);
x_231 = lean_array_fget(x_1, x_230);
x_232 = l_Lean_Json_getNat_x3f(x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_229);
lean_dec(x_222);
lean_dec(x_214);
lean_dec(x_180);
lean_dec(x_37);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 x_234 = x_232;
} else {
 lean_dec_ref(x_232);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(0, 1, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_233);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_232, 0);
lean_inc(x_236);
lean_dec(x_232);
x_237 = lean_unsigned_to_nat(12u);
x_238 = lean_array_fget(x_1, x_237);
x_239 = l_Lean_Json_getNat_x3f(x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_236);
lean_dec(x_229);
lean_dec(x_222);
lean_dec(x_214);
lean_dec(x_180);
lean_dec(x_37);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_241 = x_239;
} else {
 lean_dec_ref(x_239);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(0, 1, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_240);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_244 = x_239;
} else {
 lean_dec_ref(x_239);
 x_244 = lean_box(0);
}
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_222);
lean_ctor_set(x_245, 1, x_229);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_236);
lean_ctor_set(x_246, 1, x_243);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_248, 0, x_180);
lean_ctor_set(x_248, 1, x_214);
lean_ctor_set(x_248, 2, x_247);
x_249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_249, 0, x_248);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_37);
lean_ctor_set(x_250, 1, x_249);
if (lean_is_scalar(x_244)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_244;
}
lean_ctor_set(x_251, 0, x_250);
return x_251;
}
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_214);
lean_dec(x_180);
lean_dec(x_37);
x_252 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_253 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1;
x_254 = lean_string_append(x_253, x_252);
lean_dec(x_252);
x_255 = l_Lean_Lsp_instInhabitedRefIdent___closed__1;
x_256 = lean_string_append(x_254, x_255);
if (lean_is_scalar(x_211)) {
 x_257 = lean_alloc_ctor(0, 1, 0);
} else {
 x_257 = x_211;
 lean_ctor_set_tag(x_257, 0);
}
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
}
}
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_180);
lean_dec(x_37);
x_258 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_259 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1;
x_260 = lean_string_append(x_259, x_258);
lean_dec(x_258);
x_261 = l_Lean_Lsp_instInhabitedRefIdent___closed__1;
x_262 = lean_string_append(x_260, x_261);
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_262);
return x_263;
}
}
}
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_368; uint8_t x_369; 
x_273 = lean_ctor_get(x_29, 0);
lean_inc(x_273);
lean_dec(x_29);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_12);
lean_ctor_set(x_274, 1, x_19);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_26);
lean_ctor_set(x_275, 1, x_273);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_368 = lean_unsigned_to_nat(13u);
x_369 = lean_nat_dec_eq(x_3, x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_3);
x_370 = lean_box(0);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_276);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_372, 0, x_371);
return x_372;
}
else
{
uint8_t x_373; 
x_373 = lean_nat_dec_lt(x_4, x_3);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; 
x_374 = l_Lean_instInhabitedJson;
x_375 = l_outOfBounds___rarg(x_374);
x_277 = x_375;
goto block_367;
}
else
{
lean_object* x_376; 
x_376 = lean_array_fget(x_1, x_4);
x_277 = x_376;
goto block_367;
}
}
block_367:
{
lean_object* x_278; 
x_278 = l_Lean_Json_getStr_x3f(x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_276);
lean_dec(x_3);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 x_280 = x_278;
} else {
 lean_dec_ref(x_278);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(0, 1, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_279);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_282 = lean_ctor_get(x_278, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 x_283 = x_278;
} else {
 lean_dec_ref(x_278);
 x_283 = lean_box(0);
}
x_284 = lean_unsigned_to_nat(9u);
x_285 = lean_nat_dec_lt(x_3, x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_283);
x_286 = lean_unsigned_to_nat(5u);
x_287 = lean_array_fget(x_1, x_286);
x_288 = l_Lean_Json_getNat_x3f(x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_282);
lean_dec(x_276);
lean_dec(x_3);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 x_290 = x_288;
} else {
 lean_dec_ref(x_288);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(0, 1, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_289);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_288, 0);
lean_inc(x_292);
lean_dec(x_288);
x_293 = lean_unsigned_to_nat(6u);
x_294 = lean_array_fget(x_1, x_293);
x_295 = l_Lean_Json_getNat_x3f(x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_292);
lean_dec(x_282);
lean_dec(x_276);
lean_dec(x_3);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_297 = x_295;
} else {
 lean_dec_ref(x_295);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(0, 1, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_296);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_299 = lean_ctor_get(x_295, 0);
lean_inc(x_299);
lean_dec(x_295);
x_300 = lean_unsigned_to_nat(7u);
x_301 = lean_array_fget(x_1, x_300);
x_302 = l_Lean_Json_getNat_x3f(x_301);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_299);
lean_dec(x_292);
lean_dec(x_282);
lean_dec(x_276);
lean_dec(x_3);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 x_304 = x_302;
} else {
 lean_dec_ref(x_302);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(0, 1, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_303);
return x_305;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_302, 0);
lean_inc(x_306);
lean_dec(x_302);
x_307 = lean_unsigned_to_nat(8u);
x_308 = lean_array_fget(x_1, x_307);
x_309 = l_Lean_Json_getNat_x3f(x_308);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_306);
lean_dec(x_299);
lean_dec(x_292);
lean_dec(x_282);
lean_dec(x_276);
lean_dec(x_3);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_311 = x_309;
} else {
 lean_dec_ref(x_309);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(0, 1, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_310);
return x_312;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_313 = lean_ctor_get(x_309, 0);
lean_inc(x_313);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_314 = x_309;
} else {
 lean_dec_ref(x_309);
 x_314 = lean_box(0);
}
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_292);
lean_ctor_set(x_315, 1, x_299);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_306);
lean_ctor_set(x_316, 1, x_313);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_unsigned_to_nat(13u);
x_319 = lean_nat_dec_lt(x_3, x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_314);
lean_dec(x_3);
x_320 = lean_array_fget(x_1, x_284);
x_321 = l_Lean_Json_getNat_x3f(x_320);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_317);
lean_dec(x_282);
lean_dec(x_276);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 x_323 = x_321;
} else {
 lean_dec_ref(x_321);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(0, 1, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_322);
return x_324;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_ctor_get(x_321, 0);
lean_inc(x_325);
lean_dec(x_321);
x_326 = lean_unsigned_to_nat(10u);
x_327 = lean_array_fget(x_1, x_326);
x_328 = l_Lean_Json_getNat_x3f(x_327);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_325);
lean_dec(x_317);
lean_dec(x_282);
lean_dec(x_276);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_330 = x_328;
} else {
 lean_dec_ref(x_328);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 1, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_329);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_328, 0);
lean_inc(x_332);
lean_dec(x_328);
x_333 = lean_unsigned_to_nat(11u);
x_334 = lean_array_fget(x_1, x_333);
x_335 = l_Lean_Json_getNat_x3f(x_334);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_332);
lean_dec(x_325);
lean_dec(x_317);
lean_dec(x_282);
lean_dec(x_276);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_337 = x_335;
} else {
 lean_dec_ref(x_335);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(0, 1, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_336);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_339 = lean_ctor_get(x_335, 0);
lean_inc(x_339);
lean_dec(x_335);
x_340 = lean_unsigned_to_nat(12u);
x_341 = lean_array_fget(x_1, x_340);
x_342 = l_Lean_Json_getNat_x3f(x_341);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_339);
lean_dec(x_332);
lean_dec(x_325);
lean_dec(x_317);
lean_dec(x_282);
lean_dec(x_276);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 x_344 = x_342;
} else {
 lean_dec_ref(x_342);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(0, 1, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_343);
return x_345;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_346 = lean_ctor_get(x_342, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 x_347 = x_342;
} else {
 lean_dec_ref(x_342);
 x_347 = lean_box(0);
}
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_325);
lean_ctor_set(x_348, 1, x_332);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_339);
lean_ctor_set(x_349, 1, x_346);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_351, 0, x_282);
lean_ctor_set(x_351, 1, x_317);
lean_ctor_set(x_351, 2, x_350);
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_351);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_276);
lean_ctor_set(x_353, 1, x_352);
if (lean_is_scalar(x_347)) {
 x_354 = lean_alloc_ctor(1, 1, 0);
} else {
 x_354 = x_347;
}
lean_ctor_set(x_354, 0, x_353);
return x_354;
}
}
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_317);
lean_dec(x_282);
lean_dec(x_276);
x_355 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_356 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1;
x_357 = lean_string_append(x_356, x_355);
lean_dec(x_355);
x_358 = l_Lean_Lsp_instInhabitedRefIdent___closed__1;
x_359 = lean_string_append(x_357, x_358);
if (lean_is_scalar(x_314)) {
 x_360 = lean_alloc_ctor(0, 1, 0);
} else {
 x_360 = x_314;
 lean_ctor_set_tag(x_360, 0);
}
lean_ctor_set(x_360, 0, x_359);
return x_360;
}
}
}
}
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_282);
lean_dec(x_276);
x_361 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_362 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1;
x_363 = lean_string_append(x_362, x_361);
lean_dec(x_361);
x_364 = l_Lean_Lsp_instInhabitedRefIdent___closed__1;
x_365 = lean_string_append(x_363, x_364);
if (lean_is_scalar(x_283)) {
 x_366 = lean_alloc_ctor(0, 1, 0);
} else {
 x_366 = x_283;
 lean_ctor_set_tag(x_366, 0);
}
lean_ctor_set(x_366, 0, x_365);
return x_366;
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
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_377 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_378 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1;
x_379 = lean_string_append(x_378, x_377);
lean_dec(x_377);
x_380 = l_Lean_Lsp_instInhabitedRefIdent___closed__1;
x_381 = lean_string_append(x_379, x_380);
x_382 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_382, 0, x_381);
return x_382;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected list of length 4 or 13, not {l.size}", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_array_get_size(x_6);
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(13u);
x_13 = lean_nat_dec_eq(x_9, x_12);
lean_dec(x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_6);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__2;
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(x_6, x_15);
lean_dec(x_6);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_8, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
x_25 = lean_box(0);
x_26 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(x_6, x_25);
lean_dec(x_6);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_8);
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
lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = 1;
x_32 = lean_usize_add(x_2, x_31);
x_33 = lean_array_uset(x_8, x_2, x_30);
x_2 = x_32;
x_3 = x_33;
goto _start;
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
x_4 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRefInfo___spec__1(x_1, x_3);
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
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_array_size(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3(x_9, x_10, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
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
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1683____spec__1(x_1, x_2);
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
lean_object* x_7; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_1, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(13u);
x_16 = lean_nat_dec_eq(x_12, x_15);
lean_dec(x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_1);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__2;
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(x_11, x_18);
lean_dec(x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_free_object(x_7);
lean_dec(x_1);
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
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
lean_ctor_set(x_7, 0, x_23);
x_24 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_1, x_7);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
x_25 = lean_box(0);
x_26 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(x_11, x_25);
lean_dec(x_11);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_free_object(x_7);
lean_dec(x_1);
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
lean_ctor_set(x_7, 0, x_30);
x_31 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_1, x_7);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_7, 0);
lean_inc(x_32);
lean_dec(x_7);
x_33 = lean_array_get_size(x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_unsigned_to_nat(13u);
x_37 = lean_nat_dec_eq(x_33, x_36);
lean_dec(x_33);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_32);
lean_dec(x_1);
x_38 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__2;
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(x_32, x_39);
lean_dec(x_32);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_33);
x_47 = lean_box(0);
x_48 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(x_32, x_47);
lean_dec(x_32);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_1, x_53);
return x_54;
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
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3(x_4, x_5, x_3);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_array_mk(x_6);
x_10 = lean_array_size(x_9);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_10, x_1, x_9);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_15 = lean_array_uset(x_8, x_3, x_12);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Lsp_instToJsonModuleRefs___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = l_Lean_Lsp_RefIdent_toJson(x_8);
x_11 = l_Lean_Json_compress(x_10);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_array_size(x_13);
x_15 = 0;
x_16 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_14, x_15, x_13);
x_17 = lean_array_size(x_16);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1(x_15, x_17, x_15, x_16);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
lean_ctor_set(x_5, 1, x_19);
lean_ctor_set(x_5, 0, x_20);
x_21 = lean_box(0);
lean_ctor_set(x_1, 1, x_21);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
x_24 = l_Lean_Json_mkObj(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_2);
x_1 = x_7;
x_2 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 0, x_38);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_32);
lean_ctor_set(x_31, 0, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_31);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_40, x_21);
x_42 = lean_ctor_get(x_29, 1);
lean_inc(x_42);
lean_dec(x_29);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = l_List_appendTR___rarg(x_41, x_21);
x_44 = lean_array_mk(x_43);
x_45 = lean_array_size(x_44);
x_46 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_45, x_15, x_44);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 0, x_46);
x_47 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_12);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_1);
x_50 = l_Lean_Json_mkObj(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_11);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_2);
x_1 = x_7;
x_2 = x_52;
goto _start;
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_42);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 2);
lean_inc(x_58);
lean_dec(x_55);
lean_ctor_set_tag(x_42, 3);
lean_ctor_set(x_42, 0, x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
x_65 = lean_ctor_get(x_60, 0);
x_66 = lean_ctor_get(x_60, 1);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 1, x_21);
lean_ctor_set(x_60, 0, x_66);
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 1, x_60);
lean_ctor_set(x_59, 0, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_59);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_68, x_21);
x_70 = lean_ctor_get(x_58, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_58, 1);
lean_inc(x_71);
lean_dec(x_58);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
x_76 = lean_ctor_get(x_71, 0);
x_77 = lean_ctor_get(x_71, 1);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_21);
lean_ctor_set(x_71, 0, x_77);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 1, x_71);
lean_ctor_set(x_70, 0, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_70);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_79, x_21);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_42);
lean_ctor_set(x_81, 1, x_21);
x_82 = l_List_appendTR___rarg(x_81, x_69);
x_83 = l_List_appendTR___rarg(x_82, x_80);
x_84 = l_List_appendTR___rarg(x_41, x_83);
x_85 = lean_array_mk(x_84);
x_86 = lean_array_size(x_85);
x_87 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_86, x_15, x_85);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 0, x_87);
x_88 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_12);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_1);
x_91 = l_Lean_Json_mkObj(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_11);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_2);
x_1 = x_7;
x_2 = x_93;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_95 = lean_ctor_get(x_70, 0);
x_96 = lean_ctor_get(x_70, 1);
x_97 = lean_ctor_get(x_71, 0);
x_98 = lean_ctor_get(x_71, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_71);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_21);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 1, x_99);
lean_ctor_set(x_70, 0, x_97);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_70);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_95);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_101, x_21);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_42);
lean_ctor_set(x_103, 1, x_21);
x_104 = l_List_appendTR___rarg(x_103, x_69);
x_105 = l_List_appendTR___rarg(x_104, x_102);
x_106 = l_List_appendTR___rarg(x_41, x_105);
x_107 = lean_array_mk(x_106);
x_108 = lean_array_size(x_107);
x_109 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_108, x_15, x_107);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 0, x_109);
x_110 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_12);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_1);
x_113 = l_Lean_Json_mkObj(x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_11);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_2);
x_1 = x_7;
x_2 = x_115;
goto _start;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_117 = lean_ctor_get(x_70, 0);
x_118 = lean_ctor_get(x_70, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_70);
x_119 = lean_ctor_get(x_71, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_71, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_121 = x_71;
} else {
 lean_dec_ref(x_71);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
 lean_ctor_set_tag(x_122, 1);
}
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_21);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_117);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_125, x_21);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_42);
lean_ctor_set(x_127, 1, x_21);
x_128 = l_List_appendTR___rarg(x_127, x_69);
x_129 = l_List_appendTR___rarg(x_128, x_126);
x_130 = l_List_appendTR___rarg(x_41, x_129);
x_131 = lean_array_mk(x_130);
x_132 = lean_array_size(x_131);
x_133 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_132, x_15, x_131);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 0, x_133);
x_134 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_12);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_1);
x_137 = l_Lean_Json_mkObj(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_11);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_2);
x_1 = x_7;
x_2 = x_139;
goto _start;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; size_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_141 = lean_ctor_get(x_59, 0);
x_142 = lean_ctor_get(x_59, 1);
x_143 = lean_ctor_get(x_60, 0);
x_144 = lean_ctor_get(x_60, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_60);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_21);
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 1, x_145);
lean_ctor_set(x_59, 0, x_143);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_142);
lean_ctor_set(x_146, 1, x_59);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_141);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_147, x_21);
x_149 = lean_ctor_get(x_58, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_58, 1);
lean_inc(x_150);
lean_dec(x_58);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_150, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_156 = x_150;
} else {
 lean_dec_ref(x_150);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
 lean_ctor_set_tag(x_157, 1);
}
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_21);
if (lean_is_scalar(x_153)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_153;
 lean_ctor_set_tag(x_158, 1);
}
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_152);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_151);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_160, x_21);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_42);
lean_ctor_set(x_162, 1, x_21);
x_163 = l_List_appendTR___rarg(x_162, x_148);
x_164 = l_List_appendTR___rarg(x_163, x_161);
x_165 = l_List_appendTR___rarg(x_41, x_164);
x_166 = lean_array_mk(x_165);
x_167 = lean_array_size(x_166);
x_168 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_167, x_15, x_166);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 0, x_168);
x_169 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_12);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_1);
x_172 = l_Lean_Json_mkObj(x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_11);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_2);
x_1 = x_7;
x_2 = x_174;
goto _start;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; size_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_176 = lean_ctor_get(x_59, 0);
x_177 = lean_ctor_get(x_59, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_59);
x_178 = lean_ctor_get(x_60, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_60, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_180 = x_60;
} else {
 lean_dec_ref(x_60);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
 lean_ctor_set_tag(x_181, 1);
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_21);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_177);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_176);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_184, x_21);
x_186 = lean_ctor_get(x_58, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_58, 1);
lean_inc(x_187);
lean_dec(x_58);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_190 = x_186;
} else {
 lean_dec_ref(x_186);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_187, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_193 = x_187;
} else {
 lean_dec_ref(x_187);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
 lean_ctor_set_tag(x_194, 1);
}
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_21);
if (lean_is_scalar(x_190)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_190;
 lean_ctor_set_tag(x_195, 1);
}
lean_ctor_set(x_195, 0, x_191);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_189);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_188);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_197, x_21);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_42);
lean_ctor_set(x_199, 1, x_21);
x_200 = l_List_appendTR___rarg(x_199, x_185);
x_201 = l_List_appendTR___rarg(x_200, x_198);
x_202 = l_List_appendTR___rarg(x_41, x_201);
x_203 = lean_array_mk(x_202);
x_204 = lean_array_size(x_203);
x_205 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_204, x_15, x_203);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 0, x_205);
x_206 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_12);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_1);
x_209 = l_Lean_Json_mkObj(x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_11);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_2);
x_1 = x_7;
x_2 = x_211;
goto _start;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; size_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_213 = lean_ctor_get(x_42, 0);
lean_inc(x_213);
lean_dec(x_42);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_213, 2);
lean_inc(x_216);
lean_dec(x_213);
x_217 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_217, 0, x_214);
x_218 = lean_ctor_get(x_215, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_215, 1);
lean_inc(x_219);
lean_dec(x_215);
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_222 = x_218;
} else {
 lean_dec_ref(x_218);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_219, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_225 = x_219;
} else {
 lean_dec_ref(x_219);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
 lean_ctor_set_tag(x_226, 1);
}
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_21);
if (lean_is_scalar(x_222)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_222;
 lean_ctor_set_tag(x_227, 1);
}
lean_ctor_set(x_227, 0, x_223);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_220);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_229, x_21);
x_231 = lean_ctor_get(x_216, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_216, 1);
lean_inc(x_232);
lean_dec(x_216);
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_235 = x_231;
} else {
 lean_dec_ref(x_231);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_232, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_232, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_238 = x_232;
} else {
 lean_dec_ref(x_232);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
 lean_ctor_set_tag(x_239, 1);
}
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_21);
if (lean_is_scalar(x_235)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_235;
 lean_ctor_set_tag(x_240, 1);
}
lean_ctor_set(x_240, 0, x_236);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_234);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_233);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_242, x_21);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_217);
lean_ctor_set(x_244, 1, x_21);
x_245 = l_List_appendTR___rarg(x_244, x_230);
x_246 = l_List_appendTR___rarg(x_245, x_243);
x_247 = l_List_appendTR___rarg(x_41, x_246);
x_248 = lean_array_mk(x_247);
x_249 = lean_array_size(x_248);
x_250 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_249, x_15, x_248);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 0, x_250);
x_251 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_12);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_1);
x_254 = l_Lean_Json_mkObj(x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_11);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_2);
x_1 = x_7;
x_2 = x_256;
goto _start;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_258 = lean_ctor_get(x_31, 0);
x_259 = lean_ctor_get(x_31, 1);
x_260 = lean_ctor_get(x_32, 0);
x_261 = lean_ctor_get(x_32, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_32);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_21);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_262);
lean_ctor_set(x_31, 0, x_260);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_259);
lean_ctor_set(x_263, 1, x_31);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_258);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_264, x_21);
x_266 = lean_ctor_get(x_29, 1);
lean_inc(x_266);
lean_dec(x_29);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; size_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_267 = l_List_appendTR___rarg(x_265, x_21);
x_268 = lean_array_mk(x_267);
x_269 = lean_array_size(x_268);
x_270 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_269, x_15, x_268);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 0, x_270);
x_271 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_12);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_1);
x_274 = l_Lean_Json_mkObj(x_273);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_11);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_2);
x_1 = x_7;
x_2 = x_276;
goto _start;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; size_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_278 = lean_ctor_get(x_266, 0);
lean_inc(x_278);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 x_279 = x_266;
} else {
 lean_dec_ref(x_266);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_278, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
x_282 = lean_ctor_get(x_278, 2);
lean_inc(x_282);
lean_dec(x_278);
if (lean_is_scalar(x_279)) {
 x_283 = lean_alloc_ctor(3, 1, 0);
} else {
 x_283 = x_279;
 lean_ctor_set_tag(x_283, 3);
}
lean_ctor_set(x_283, 0, x_280);
x_284 = lean_ctor_get(x_281, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_281, 1);
lean_inc(x_285);
lean_dec(x_281);
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_284, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_288 = x_284;
} else {
 lean_dec_ref(x_284);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_285, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_285, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_291 = x_285;
} else {
 lean_dec_ref(x_285);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
 lean_ctor_set_tag(x_292, 1);
}
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_21);
if (lean_is_scalar(x_288)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_288;
 lean_ctor_set_tag(x_293, 1);
}
lean_ctor_set(x_293, 0, x_289);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_287);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_286);
lean_ctor_set(x_295, 1, x_294);
x_296 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_295, x_21);
x_297 = lean_ctor_get(x_282, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_282, 1);
lean_inc(x_298);
lean_dec(x_282);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_297, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_301 = x_297;
} else {
 lean_dec_ref(x_297);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_298, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_298, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_304 = x_298;
} else {
 lean_dec_ref(x_298);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
 lean_ctor_set_tag(x_305, 1);
}
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_21);
if (lean_is_scalar(x_301)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_301;
 lean_ctor_set_tag(x_306, 1);
}
lean_ctor_set(x_306, 0, x_302);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_300);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_299);
lean_ctor_set(x_308, 1, x_307);
x_309 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_308, x_21);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_283);
lean_ctor_set(x_310, 1, x_21);
x_311 = l_List_appendTR___rarg(x_310, x_296);
x_312 = l_List_appendTR___rarg(x_311, x_309);
x_313 = l_List_appendTR___rarg(x_265, x_312);
x_314 = lean_array_mk(x_313);
x_315 = lean_array_size(x_314);
x_316 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_315, x_15, x_314);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 0, x_316);
x_317 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_12);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_1);
x_320 = l_Lean_Json_mkObj(x_319);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_11);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_2);
x_1 = x_7;
x_2 = x_322;
goto _start;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_324 = lean_ctor_get(x_31, 0);
x_325 = lean_ctor_get(x_31, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_31);
x_326 = lean_ctor_get(x_32, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_32, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_328 = x_32;
} else {
 lean_dec_ref(x_32);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
 lean_ctor_set_tag(x_329, 1);
}
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_21);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_326);
lean_ctor_set(x_330, 1, x_329);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_325);
lean_ctor_set(x_331, 1, x_330);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_324);
lean_ctor_set(x_332, 1, x_331);
x_333 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_332, x_21);
x_334 = lean_ctor_get(x_29, 1);
lean_inc(x_334);
lean_dec(x_29);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; size_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_335 = l_List_appendTR___rarg(x_333, x_21);
x_336 = lean_array_mk(x_335);
x_337 = lean_array_size(x_336);
x_338 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_337, x_15, x_336);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 0, x_338);
x_339 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_12);
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_1);
x_342 = l_Lean_Json_mkObj(x_341);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_11);
lean_ctor_set(x_343, 1, x_342);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_2);
x_1 = x_7;
x_2 = x_344;
goto _start;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; size_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_346 = lean_ctor_get(x_334, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 x_347 = x_334;
} else {
 lean_dec_ref(x_334);
 x_347 = lean_box(0);
}
x_348 = lean_ctor_get(x_346, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_346, 2);
lean_inc(x_350);
lean_dec(x_346);
if (lean_is_scalar(x_347)) {
 x_351 = lean_alloc_ctor(3, 1, 0);
} else {
 x_351 = x_347;
 lean_ctor_set_tag(x_351, 3);
}
lean_ctor_set(x_351, 0, x_348);
x_352 = lean_ctor_get(x_349, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 1);
lean_inc(x_353);
lean_dec(x_349);
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_352, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_356 = x_352;
} else {
 lean_dec_ref(x_352);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_353, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_353, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_359 = x_353;
} else {
 lean_dec_ref(x_353);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
 lean_ctor_set_tag(x_360, 1);
}
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_21);
if (lean_is_scalar(x_356)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_356;
 lean_ctor_set_tag(x_361, 1);
}
lean_ctor_set(x_361, 0, x_357);
lean_ctor_set(x_361, 1, x_360);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_355);
lean_ctor_set(x_362, 1, x_361);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_354);
lean_ctor_set(x_363, 1, x_362);
x_364 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_363, x_21);
x_365 = lean_ctor_get(x_350, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_350, 1);
lean_inc(x_366);
lean_dec(x_350);
x_367 = lean_ctor_get(x_365, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_369 = x_365;
} else {
 lean_dec_ref(x_365);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_366, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_366, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_372 = x_366;
} else {
 lean_dec_ref(x_366);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 2, 0);
} else {
 x_373 = x_372;
 lean_ctor_set_tag(x_373, 1);
}
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_21);
if (lean_is_scalar(x_369)) {
 x_374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_374 = x_369;
 lean_ctor_set_tag(x_374, 1);
}
lean_ctor_set(x_374, 0, x_370);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_368);
lean_ctor_set(x_375, 1, x_374);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_367);
lean_ctor_set(x_376, 1, x_375);
x_377 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_376, x_21);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_351);
lean_ctor_set(x_378, 1, x_21);
x_379 = l_List_appendTR___rarg(x_378, x_364);
x_380 = l_List_appendTR___rarg(x_379, x_377);
x_381 = l_List_appendTR___rarg(x_333, x_380);
x_382 = lean_array_mk(x_381);
x_383 = lean_array_size(x_382);
x_384 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_383, x_15, x_382);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 0, x_384);
x_385 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_12);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_1);
x_388 = l_Lean_Json_mkObj(x_387);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_11);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_2);
x_1 = x_7;
x_2 = x_390;
goto _start;
}
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_392 = lean_ctor_get(x_12, 0);
lean_inc(x_392);
lean_dec(x_12);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = lean_ctor_get(x_394, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_394, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_398 = x_394;
} else {
 lean_dec_ref(x_394);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_395, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_395, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_401 = x_395;
} else {
 lean_dec_ref(x_395);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_402 = x_401;
 lean_ctor_set_tag(x_402, 1);
}
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_21);
if (lean_is_scalar(x_398)) {
 x_403 = lean_alloc_ctor(1, 2, 0);
} else {
 x_403 = x_398;
 lean_ctor_set_tag(x_403, 1);
}
lean_ctor_set(x_403, 0, x_399);
lean_ctor_set(x_403, 1, x_402);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_397);
lean_ctor_set(x_404, 1, x_403);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_396);
lean_ctor_set(x_405, 1, x_404);
x_406 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_405, x_21);
x_407 = lean_ctor_get(x_392, 1);
lean_inc(x_407);
lean_dec(x_392);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; size_t x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_408 = l_List_appendTR___rarg(x_406, x_21);
x_409 = lean_array_mk(x_408);
x_410 = lean_array_size(x_409);
x_411 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_410, x_15, x_409);
x_412 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_412, 0, x_411);
x_413 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_412);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_1);
x_416 = l_Lean_Json_mkObj(x_415);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_11);
lean_ctor_set(x_417, 1, x_416);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_2);
x_1 = x_7;
x_2 = x_418;
goto _start;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; size_t x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_420 = lean_ctor_get(x_407, 0);
lean_inc(x_420);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_421 = x_407;
} else {
 lean_dec_ref(x_407);
 x_421 = lean_box(0);
}
x_422 = lean_ctor_get(x_420, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_420, 2);
lean_inc(x_424);
lean_dec(x_420);
if (lean_is_scalar(x_421)) {
 x_425 = lean_alloc_ctor(3, 1, 0);
} else {
 x_425 = x_421;
 lean_ctor_set_tag(x_425, 3);
}
lean_ctor_set(x_425, 0, x_422);
x_426 = lean_ctor_get(x_423, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_423, 1);
lean_inc(x_427);
lean_dec(x_423);
x_428 = lean_ctor_get(x_426, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_426, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_430 = x_426;
} else {
 lean_dec_ref(x_426);
 x_430 = lean_box(0);
}
x_431 = lean_ctor_get(x_427, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_427, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_433 = x_427;
} else {
 lean_dec_ref(x_427);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_434 = x_433;
 lean_ctor_set_tag(x_434, 1);
}
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_21);
if (lean_is_scalar(x_430)) {
 x_435 = lean_alloc_ctor(1, 2, 0);
} else {
 x_435 = x_430;
 lean_ctor_set_tag(x_435, 1);
}
lean_ctor_set(x_435, 0, x_431);
lean_ctor_set(x_435, 1, x_434);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_429);
lean_ctor_set(x_436, 1, x_435);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_428);
lean_ctor_set(x_437, 1, x_436);
x_438 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_437, x_21);
x_439 = lean_ctor_get(x_424, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_424, 1);
lean_inc(x_440);
lean_dec(x_424);
x_441 = lean_ctor_get(x_439, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_439, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_443 = x_439;
} else {
 lean_dec_ref(x_439);
 x_443 = lean_box(0);
}
x_444 = lean_ctor_get(x_440, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_440, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_446 = x_440;
} else {
 lean_dec_ref(x_440);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 2, 0);
} else {
 x_447 = x_446;
 lean_ctor_set_tag(x_447, 1);
}
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_21);
if (lean_is_scalar(x_443)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_443;
 lean_ctor_set_tag(x_448, 1);
}
lean_ctor_set(x_448, 0, x_444);
lean_ctor_set(x_448, 1, x_447);
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_442);
lean_ctor_set(x_449, 1, x_448);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_441);
lean_ctor_set(x_450, 1, x_449);
x_451 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_450, x_21);
x_452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_452, 0, x_425);
lean_ctor_set(x_452, 1, x_21);
x_453 = l_List_appendTR___rarg(x_452, x_438);
x_454 = l_List_appendTR___rarg(x_453, x_451);
x_455 = l_List_appendTR___rarg(x_406, x_454);
x_456 = lean_array_mk(x_455);
x_457 = lean_array_size(x_456);
x_458 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_457, x_15, x_456);
x_459 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_459, 0, x_458);
x_460 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_459);
x_462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_1);
x_463 = l_Lean_Json_mkObj(x_462);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_11);
lean_ctor_set(x_464, 1, x_463);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_2);
x_1 = x_7;
x_2 = x_465;
goto _start;
}
}
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; size_t x_474; size_t x_475; lean_object* x_476; size_t x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_467 = lean_ctor_get(x_1, 1);
x_468 = lean_ctor_get(x_5, 0);
x_469 = lean_ctor_get(x_5, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_5);
x_470 = l_Lean_Lsp_RefIdent_toJson(x_468);
x_471 = l_Lean_Json_compress(x_470);
x_472 = lean_ctor_get(x_469, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_469, 1);
lean_inc(x_473);
lean_dec(x_469);
x_474 = lean_array_size(x_473);
x_475 = 0;
x_476 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_474, x_475, x_473);
x_477 = lean_array_size(x_476);
x_478 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1(x_475, x_477, x_475, x_476);
x_479 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_479, 0, x_478);
x_480 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_479);
x_482 = lean_box(0);
lean_ctor_set(x_1, 1, x_482);
lean_ctor_set(x_1, 0, x_481);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_483 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_1);
x_485 = l_Lean_Json_mkObj(x_484);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_471);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_2);
x_1 = x_467;
x_2 = x_487;
goto _start;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_489 = lean_ctor_get(x_472, 0);
lean_inc(x_489);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 x_490 = x_472;
} else {
 lean_dec_ref(x_472);
 x_490 = lean_box(0);
}
x_491 = lean_ctor_get(x_489, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec(x_491);
x_494 = lean_ctor_get(x_492, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_492, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_496 = x_492;
} else {
 lean_dec_ref(x_492);
 x_496 = lean_box(0);
}
x_497 = lean_ctor_get(x_493, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_493, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_499 = x_493;
} else {
 lean_dec_ref(x_493);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
 lean_ctor_set_tag(x_500, 1);
}
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_482);
if (lean_is_scalar(x_496)) {
 x_501 = lean_alloc_ctor(1, 2, 0);
} else {
 x_501 = x_496;
 lean_ctor_set_tag(x_501, 1);
}
lean_ctor_set(x_501, 0, x_497);
lean_ctor_set(x_501, 1, x_500);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_495);
lean_ctor_set(x_502, 1, x_501);
x_503 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_503, 0, x_494);
lean_ctor_set(x_503, 1, x_502);
x_504 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_503, x_482);
x_505 = lean_ctor_get(x_489, 1);
lean_inc(x_505);
lean_dec(x_489);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; size_t x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_506 = l_List_appendTR___rarg(x_504, x_482);
x_507 = lean_array_mk(x_506);
x_508 = lean_array_size(x_507);
x_509 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_508, x_475, x_507);
if (lean_is_scalar(x_490)) {
 x_510 = lean_alloc_ctor(4, 1, 0);
} else {
 x_510 = x_490;
 lean_ctor_set_tag(x_510, 4);
}
lean_ctor_set(x_510, 0, x_509);
x_511 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_510);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_1);
x_514 = l_Lean_Json_mkObj(x_513);
x_515 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_515, 0, x_471);
lean_ctor_set(x_515, 1, x_514);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_2);
x_1 = x_467;
x_2 = x_516;
goto _start;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; size_t x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_518 = lean_ctor_get(x_505, 0);
lean_inc(x_518);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 x_519 = x_505;
} else {
 lean_dec_ref(x_505);
 x_519 = lean_box(0);
}
x_520 = lean_ctor_get(x_518, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_518, 1);
lean_inc(x_521);
x_522 = lean_ctor_get(x_518, 2);
lean_inc(x_522);
lean_dec(x_518);
if (lean_is_scalar(x_519)) {
 x_523 = lean_alloc_ctor(3, 1, 0);
} else {
 x_523 = x_519;
 lean_ctor_set_tag(x_523, 3);
}
lean_ctor_set(x_523, 0, x_520);
x_524 = lean_ctor_get(x_521, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_521, 1);
lean_inc(x_525);
lean_dec(x_521);
x_526 = lean_ctor_get(x_524, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_524, 1);
lean_inc(x_527);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_528 = x_524;
} else {
 lean_dec_ref(x_524);
 x_528 = lean_box(0);
}
x_529 = lean_ctor_get(x_525, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_525, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 lean_ctor_release(x_525, 1);
 x_531 = x_525;
} else {
 lean_dec_ref(x_525);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_532 = x_531;
 lean_ctor_set_tag(x_532, 1);
}
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_482);
if (lean_is_scalar(x_528)) {
 x_533 = lean_alloc_ctor(1, 2, 0);
} else {
 x_533 = x_528;
 lean_ctor_set_tag(x_533, 1);
}
lean_ctor_set(x_533, 0, x_529);
lean_ctor_set(x_533, 1, x_532);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_527);
lean_ctor_set(x_534, 1, x_533);
x_535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_535, 0, x_526);
lean_ctor_set(x_535, 1, x_534);
x_536 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_535, x_482);
x_537 = lean_ctor_get(x_522, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_522, 1);
lean_inc(x_538);
lean_dec(x_522);
x_539 = lean_ctor_get(x_537, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_537, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 lean_ctor_release(x_537, 1);
 x_541 = x_537;
} else {
 lean_dec_ref(x_537);
 x_541 = lean_box(0);
}
x_542 = lean_ctor_get(x_538, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_538, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_544 = x_538;
} else {
 lean_dec_ref(x_538);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 2, 0);
} else {
 x_545 = x_544;
 lean_ctor_set_tag(x_545, 1);
}
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_482);
if (lean_is_scalar(x_541)) {
 x_546 = lean_alloc_ctor(1, 2, 0);
} else {
 x_546 = x_541;
 lean_ctor_set_tag(x_546, 1);
}
lean_ctor_set(x_546, 0, x_542);
lean_ctor_set(x_546, 1, x_545);
x_547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_547, 0, x_540);
lean_ctor_set(x_547, 1, x_546);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_539);
lean_ctor_set(x_548, 1, x_547);
x_549 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_548, x_482);
x_550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_550, 0, x_523);
lean_ctor_set(x_550, 1, x_482);
x_551 = l_List_appendTR___rarg(x_550, x_536);
x_552 = l_List_appendTR___rarg(x_551, x_549);
x_553 = l_List_appendTR___rarg(x_504, x_552);
x_554 = lean_array_mk(x_553);
x_555 = lean_array_size(x_554);
x_556 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_555, x_475, x_554);
if (lean_is_scalar(x_490)) {
 x_557 = lean_alloc_ctor(4, 1, 0);
} else {
 x_557 = x_490;
 lean_ctor_set_tag(x_557, 4);
}
lean_ctor_set(x_557, 0, x_556);
x_558 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_557);
x_560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_560, 0, x_559);
lean_ctor_set(x_560, 1, x_1);
x_561 = l_Lean_Json_mkObj(x_560);
x_562 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_562, 0, x_471);
lean_ctor_set(x_562, 1, x_561);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_2);
x_1 = x_467;
x_2 = x_563;
goto _start;
}
}
}
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; size_t x_574; size_t x_575; lean_object* x_576; size_t x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_565 = lean_ctor_get(x_1, 0);
x_566 = lean_ctor_get(x_1, 1);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_1);
x_567 = lean_ctor_get(x_565, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_565, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_569 = x_565;
} else {
 lean_dec_ref(x_565);
 x_569 = lean_box(0);
}
x_570 = l_Lean_Lsp_RefIdent_toJson(x_567);
x_571 = l_Lean_Json_compress(x_570);
x_572 = lean_ctor_get(x_568, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_568, 1);
lean_inc(x_573);
lean_dec(x_568);
x_574 = lean_array_size(x_573);
x_575 = 0;
x_576 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_574, x_575, x_573);
x_577 = lean_array_size(x_576);
x_578 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonModuleRefs___spec__1(x_575, x_577, x_575, x_576);
x_579 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_579, 0, x_578);
x_580 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
if (lean_is_scalar(x_569)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_569;
}
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_579);
x_582 = lean_box(0);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_584 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_584);
lean_ctor_set(x_585, 1, x_583);
x_586 = l_Lean_Json_mkObj(x_585);
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_571);
lean_ctor_set(x_587, 1, x_586);
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_2);
x_1 = x_566;
x_2 = x_588;
goto _start;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_590 = lean_ctor_get(x_572, 0);
lean_inc(x_590);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 x_591 = x_572;
} else {
 lean_dec_ref(x_572);
 x_591 = lean_box(0);
}
x_592 = lean_ctor_get(x_590, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
lean_dec(x_592);
x_595 = lean_ctor_get(x_593, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_593, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_597 = x_593;
} else {
 lean_dec_ref(x_593);
 x_597 = lean_box(0);
}
x_598 = lean_ctor_get(x_594, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_594, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_600 = x_594;
} else {
 lean_dec_ref(x_594);
 x_600 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_601 = x_600;
 lean_ctor_set_tag(x_601, 1);
}
lean_ctor_set(x_601, 0, x_599);
lean_ctor_set(x_601, 1, x_582);
if (lean_is_scalar(x_597)) {
 x_602 = lean_alloc_ctor(1, 2, 0);
} else {
 x_602 = x_597;
 lean_ctor_set_tag(x_602, 1);
}
lean_ctor_set(x_602, 0, x_598);
lean_ctor_set(x_602, 1, x_601);
x_603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_603, 0, x_596);
lean_ctor_set(x_603, 1, x_602);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_595);
lean_ctor_set(x_604, 1, x_603);
x_605 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_604, x_582);
x_606 = lean_ctor_get(x_590, 1);
lean_inc(x_606);
lean_dec(x_590);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; size_t x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_607 = l_List_appendTR___rarg(x_605, x_582);
x_608 = lean_array_mk(x_607);
x_609 = lean_array_size(x_608);
x_610 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_609, x_575, x_608);
if (lean_is_scalar(x_591)) {
 x_611 = lean_alloc_ctor(4, 1, 0);
} else {
 x_611 = x_591;
 lean_ctor_set_tag(x_611, 4);
}
lean_ctor_set(x_611, 0, x_610);
x_612 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_611);
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_583);
x_615 = l_Lean_Json_mkObj(x_614);
x_616 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_616, 0, x_571);
lean_ctor_set(x_616, 1, x_615);
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_2);
x_1 = x_566;
x_2 = x_617;
goto _start;
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; size_t x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_619 = lean_ctor_get(x_606, 0);
lean_inc(x_619);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 x_620 = x_606;
} else {
 lean_dec_ref(x_606);
 x_620 = lean_box(0);
}
x_621 = lean_ctor_get(x_619, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_619, 1);
lean_inc(x_622);
x_623 = lean_ctor_get(x_619, 2);
lean_inc(x_623);
lean_dec(x_619);
if (lean_is_scalar(x_620)) {
 x_624 = lean_alloc_ctor(3, 1, 0);
} else {
 x_624 = x_620;
 lean_ctor_set_tag(x_624, 3);
}
lean_ctor_set(x_624, 0, x_621);
x_625 = lean_ctor_get(x_622, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_622, 1);
lean_inc(x_626);
lean_dec(x_622);
x_627 = lean_ctor_get(x_625, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_625, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_629 = x_625;
} else {
 lean_dec_ref(x_625);
 x_629 = lean_box(0);
}
x_630 = lean_ctor_get(x_626, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_626, 1);
lean_inc(x_631);
if (lean_is_exclusive(x_626)) {
 lean_ctor_release(x_626, 0);
 lean_ctor_release(x_626, 1);
 x_632 = x_626;
} else {
 lean_dec_ref(x_626);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(1, 2, 0);
} else {
 x_633 = x_632;
 lean_ctor_set_tag(x_633, 1);
}
lean_ctor_set(x_633, 0, x_631);
lean_ctor_set(x_633, 1, x_582);
if (lean_is_scalar(x_629)) {
 x_634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_634 = x_629;
 lean_ctor_set_tag(x_634, 1);
}
lean_ctor_set(x_634, 0, x_630);
lean_ctor_set(x_634, 1, x_633);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_628);
lean_ctor_set(x_635, 1, x_634);
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_627);
lean_ctor_set(x_636, 1, x_635);
x_637 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_636, x_582);
x_638 = lean_ctor_get(x_623, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_623, 1);
lean_inc(x_639);
lean_dec(x_623);
x_640 = lean_ctor_get(x_638, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_638, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 lean_ctor_release(x_638, 1);
 x_642 = x_638;
} else {
 lean_dec_ref(x_638);
 x_642 = lean_box(0);
}
x_643 = lean_ctor_get(x_639, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_639, 1);
lean_inc(x_644);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_645 = x_639;
} else {
 lean_dec_ref(x_639);
 x_645 = lean_box(0);
}
if (lean_is_scalar(x_645)) {
 x_646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_646 = x_645;
 lean_ctor_set_tag(x_646, 1);
}
lean_ctor_set(x_646, 0, x_644);
lean_ctor_set(x_646, 1, x_582);
if (lean_is_scalar(x_642)) {
 x_647 = lean_alloc_ctor(1, 2, 0);
} else {
 x_647 = x_642;
 lean_ctor_set_tag(x_647, 1);
}
lean_ctor_set(x_647, 0, x_643);
lean_ctor_set(x_647, 1, x_646);
x_648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_648, 0, x_641);
lean_ctor_set(x_648, 1, x_647);
x_649 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_649, 0, x_640);
lean_ctor_set(x_649, 1, x_648);
x_650 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_649, x_582);
x_651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_651, 0, x_624);
lean_ctor_set(x_651, 1, x_582);
x_652 = l_List_appendTR___rarg(x_651, x_637);
x_653 = l_List_appendTR___rarg(x_652, x_650);
x_654 = l_List_appendTR___rarg(x_605, x_653);
x_655 = lean_array_mk(x_654);
x_656 = lean_array_size(x_655);
x_657 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_656, x_575, x_655);
if (lean_is_scalar(x_591)) {
 x_658 = lean_alloc_ctor(4, 1, 0);
} else {
 x_658 = x_591;
 lean_ctor_set_tag(x_658, 4);
}
lean_ctor_set(x_658, 0, x_657);
x_659 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_660 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_658);
x_661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_583);
x_662 = l_Lean_Json_mkObj(x_661);
x_663 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_663, 0, x_571);
lean_ctor_set(x_663, 1, x_662);
x_664 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_2);
x_1 = x_566;
x_2 = x_664;
goto _start;
}
}
}
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
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__2(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonModuleRefs___spec__3(x_2, x_2);
x_8 = l_Lean_Json_mkObj(x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonModuleRefs___spec__3(x_2, x_2);
x_11 = l_Lean_Json_mkObj(x_10);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Lsp_instToJsonModuleRefs___spec__4(x_3, x_12, x_13, x_2);
x_15 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonModuleRefs___spec__3(x_14, x_2);
x_16 = l_Lean_Json_mkObj(x_15);
return x_16;
}
}
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Lsp_instToJsonModuleRefs___spec__2(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instToJsonModuleRefs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_44_(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Lsp_instFromJsonModuleRefs___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_157_(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_157_(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Lsp_instFromJsonModuleRefs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Lsp_instFromJsonModuleRefs___spec__4(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Lsp_instFromJsonModuleRefs___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Lsp_instFromJsonModuleRefs___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_44_(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__5(x_1, x_2, x_8);
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
x_14 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_beqRefIdent____x40_Lean_Data_Lsp_Internal___hyg_44_(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__5(x_1, x_2, x_13);
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
static lean_object* _init_l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__6(x_1, x_4);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__6___closed__1;
x_14 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_13, x_5);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_7);
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
lean_dec(x_14);
x_19 = l_Lean_Lsp_RefIdent_fromJson_x3f(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
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
lean_object* x_23; lean_object* x_24; lean_object* x_100; lean_object* x_101; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_100 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
lean_inc(x_6);
x_101 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1683____spec__1(x_6, x_100);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
return x_101;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_101, 0);
lean_inc(x_105);
lean_dec(x_101);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_box(0);
x_107 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_6, x_106);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
return x_107;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_107, 0);
lean_inc(x_111);
lean_dec(x_107);
x_24 = x_111;
goto block_99;
}
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_105);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_105, 0);
x_114 = lean_array_get_size(x_113);
x_115 = lean_unsigned_to_nat(4u);
x_116 = lean_nat_dec_eq(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_unsigned_to_nat(13u);
x_118 = lean_nat_dec_eq(x_114, x_117);
lean_dec(x_114);
if (x_118 == 0)
{
lean_object* x_119; 
lean_free_object(x_105);
lean_dec(x_113);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_119 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__2;
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_box(0);
x_121 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(x_113, x_120);
lean_dec(x_113);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_free_object(x_105);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
return x_121;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_121, 0);
lean_inc(x_125);
lean_dec(x_121);
lean_ctor_set(x_105, 0, x_125);
x_126 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_6, x_105);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
return x_126;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
else
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
lean_dec(x_126);
x_24 = x_130;
goto block_99;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_114);
x_131 = lean_box(0);
x_132 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(x_113, x_131);
lean_dec(x_113);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
lean_free_object(x_105);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
return x_132;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_132, 0);
lean_inc(x_136);
lean_dec(x_132);
lean_ctor_set(x_105, 0, x_136);
x_137 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_6, x_105);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
else
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_137, 0);
lean_inc(x_141);
lean_dec(x_137);
x_24 = x_141;
goto block_99;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_105, 0);
lean_inc(x_142);
lean_dec(x_105);
x_143 = lean_array_get_size(x_142);
x_144 = lean_unsigned_to_nat(4u);
x_145 = lean_nat_dec_eq(x_143, x_144);
if (x_145 == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_unsigned_to_nat(13u);
x_147 = lean_nat_dec_eq(x_143, x_146);
lean_dec(x_143);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_142);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_148 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__2;
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_box(0);
x_150 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(x_142, x_149);
lean_dec(x_142);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_150, 0);
lean_inc(x_154);
lean_dec(x_150);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_6, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(0, 1, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_157);
return x_159;
}
else
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_156, 0);
lean_inc(x_160);
lean_dec(x_156);
x_24 = x_160;
goto block_99;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_143);
x_161 = lean_box(0);
x_162 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1(x_142, x_161);
lean_dec(x_142);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(0, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_163);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
lean_dec(x_162);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = l_Lean_Lsp_instFromJsonRefInfo___lambda__1(x_6, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_7);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 1, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_169);
return x_171;
}
else
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
lean_dec(x_168);
x_24 = x_172;
goto block_99;
}
}
}
}
}
}
block_99:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
x_28 = lean_array_get_size(x_27);
x_29 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_157_(x_23);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_27, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(x_23, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_26, x_43);
lean_dec(x_26);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_24);
lean_ctor_set(x_45, 2, x_41);
x_46 = lean_array_uset(x_27, x_40, x_45);
x_47 = lean_unsigned_to_nat(4u);
x_48 = lean_nat_mul(x_44, x_47);
x_49 = lean_unsigned_to_nat(3u);
x_50 = lean_nat_div(x_48, x_49);
lean_dec(x_48);
x_51 = lean_array_get_size(x_46);
x_52 = lean_nat_dec_le(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Lsp_instFromJsonModuleRefs___spec__2(x_46);
lean_ctor_set(x_12, 1, x_53);
lean_ctor_set(x_12, 0, x_44);
x_1 = x_12;
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_12, 1, x_46);
lean_ctor_set(x_12, 0, x_44);
x_1 = x_12;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_box(0);
x_57 = lean_array_uset(x_27, x_40, x_56);
x_58 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__5(x_23, x_24, x_41);
x_59 = lean_array_uset(x_57, x_40, x_58);
lean_ctor_set(x_12, 1, x_59);
x_1 = x_12;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; size_t x_71; size_t x_72; size_t x_73; size_t x_74; size_t x_75; lean_object* x_76; uint8_t x_77; 
x_61 = lean_ctor_get(x_12, 0);
x_62 = lean_ctor_get(x_12, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_12);
x_63 = lean_array_get_size(x_62);
x_64 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_hashRefIdent____x40_Lean_Data_Lsp_Internal___hyg_157_(x_23);
x_65 = 32;
x_66 = lean_uint64_shift_right(x_64, x_65);
x_67 = lean_uint64_xor(x_64, x_66);
x_68 = 16;
x_69 = lean_uint64_shift_right(x_67, x_68);
x_70 = lean_uint64_xor(x_67, x_69);
x_71 = lean_uint64_to_usize(x_70);
x_72 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_73 = 1;
x_74 = lean_usize_sub(x_72, x_73);
x_75 = lean_usize_land(x_71, x_74);
x_76 = lean_array_uget(x_62, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(x_23, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_61, x_78);
lean_dec(x_61);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_23);
lean_ctor_set(x_80, 1, x_24);
lean_ctor_set(x_80, 2, x_76);
x_81 = lean_array_uset(x_62, x_75, x_80);
x_82 = lean_unsigned_to_nat(4u);
x_83 = lean_nat_mul(x_79, x_82);
x_84 = lean_unsigned_to_nat(3u);
x_85 = lean_nat_div(x_83, x_84);
lean_dec(x_83);
x_86 = lean_array_get_size(x_81);
x_87 = lean_nat_dec_le(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Lsp_instFromJsonModuleRefs___spec__2(x_81);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_88);
x_1 = x_89;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_79);
lean_ctor_set(x_91, 1, x_81);
x_1 = x_91;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_box(0);
x_94 = lean_array_uset(x_62, x_75, x_93);
x_95 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Lsp_instFromJsonModuleRefs___spec__5(x_23, x_24, x_76);
x_96 = lean_array_uset(x_94, x_75, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_61);
lean_ctor_set(x_97, 1, x_96);
x_1 = x_97;
x_2 = x_7;
goto _start;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonModuleRefs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonModuleRefs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Lsp_instFromJsonModuleRefs___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonModuleRefs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Lsp_instFromJsonModuleRefs___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs(lean_object* x_1) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Lsp_instFromJsonModuleRefs___closed__3;
x_8 = l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__6(x_7, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Lsp_instFromJsonModuleRefs___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getObj_x3f(x_3);
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
x_9 = l_Lean_Lsp_instFromJsonModuleRefs___closed__3;
x_10 = l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__6(x_9, x_8);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("version", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lsp", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LeanIleanInfoParams", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__2;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__3;
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__5;
x_2 = 1;
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__7;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__11() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__10;
x_2 = 1;
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__9;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__11;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__12;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("references", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__17() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__16;
x_2 = 1;
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__9;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__17;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__18;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__1;
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_458____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__14;
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
x_9 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__14;
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
x_13 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__15;
x_14 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____spec__1(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__19;
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
x_20 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__19;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914_), 1, 0);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(size_t x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_array_mk(x_6);
x_10 = lean_array_size(x_9);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_10, x_1, x_9);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_15 = lean_array_uset(x_8, x_3, x_12);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Lean_Lsp_RefIdent_toJson(x_9);
x_12 = l_Lean_Json_compress(x_11);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_array_size(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_15, x_16, x_14);
x_18 = lean_array_size(x_17);
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(x_16, x_18, x_16, x_17);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_6, 0, x_21);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_24 = l_Lean_Json_mkObj(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
x_2 = x_8;
x_3 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
x_39 = lean_box(0);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_39);
lean_ctor_set(x_32, 0, x_38);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_32);
lean_ctor_set(x_31, 0, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_41, x_39);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = l_List_appendTR___rarg(x_42, x_39);
x_45 = lean_array_mk(x_44);
x_46 = lean_array_size(x_45);
x_47 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_46, x_16, x_45);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_47);
x_48 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_13);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_2);
x_51 = l_Lean_Json_mkObj(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
x_2 = x_8;
x_3 = x_53;
goto _start;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_43);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_43, 0);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 2);
lean_inc(x_59);
lean_dec(x_56);
lean_ctor_set_tag(x_43, 3);
lean_ctor_set(x_43, 0, x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 1, x_39);
lean_ctor_set(x_61, 0, x_67);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 1, x_61);
lean_ctor_set(x_60, 0, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_60);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_69, x_39);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
lean_dec(x_59);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_ctor_get(x_71, 1);
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_ctor_get(x_72, 1);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_39);
lean_ctor_set(x_72, 0, x_78);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_72);
lean_ctor_set(x_71, 0, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_71);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_80, x_39);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_43);
lean_ctor_set(x_82, 1, x_39);
x_83 = l_List_appendTR___rarg(x_82, x_70);
x_84 = l_List_appendTR___rarg(x_83, x_81);
x_85 = l_List_appendTR___rarg(x_42, x_84);
x_86 = lean_array_mk(x_85);
x_87 = lean_array_size(x_86);
x_88 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_87, x_16, x_86);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_88);
x_89 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_13);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_2);
x_92 = l_Lean_Json_mkObj(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_12);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_3);
x_2 = x_8;
x_3 = x_94;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_96 = lean_ctor_get(x_71, 0);
x_97 = lean_ctor_get(x_71, 1);
x_98 = lean_ctor_get(x_72, 0);
x_99 = lean_ctor_get(x_72, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_72);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_39);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_100);
lean_ctor_set(x_71, 0, x_98);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_71);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_102, x_39);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_43);
lean_ctor_set(x_104, 1, x_39);
x_105 = l_List_appendTR___rarg(x_104, x_70);
x_106 = l_List_appendTR___rarg(x_105, x_103);
x_107 = l_List_appendTR___rarg(x_42, x_106);
x_108 = lean_array_mk(x_107);
x_109 = lean_array_size(x_108);
x_110 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_109, x_16, x_108);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_110);
x_111 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_13);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_2);
x_114 = l_Lean_Json_mkObj(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_12);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_3);
x_2 = x_8;
x_3 = x_116;
goto _start;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; size_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_118 = lean_ctor_get(x_71, 0);
x_119 = lean_ctor_get(x_71, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_71);
x_120 = lean_ctor_get(x_72, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_72, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_122 = x_72;
} else {
 lean_dec_ref(x_72);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
 lean_ctor_set_tag(x_123, 1);
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_39);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_118);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_126, x_39);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_43);
lean_ctor_set(x_128, 1, x_39);
x_129 = l_List_appendTR___rarg(x_128, x_70);
x_130 = l_List_appendTR___rarg(x_129, x_127);
x_131 = l_List_appendTR___rarg(x_42, x_130);
x_132 = lean_array_mk(x_131);
x_133 = lean_array_size(x_132);
x_134 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_133, x_16, x_132);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_134);
x_135 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_13);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_2);
x_138 = l_Lean_Json_mkObj(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_12);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_3);
x_2 = x_8;
x_3 = x_140;
goto _start;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; size_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_142 = lean_ctor_get(x_60, 0);
x_143 = lean_ctor_get(x_60, 1);
x_144 = lean_ctor_get(x_61, 0);
x_145 = lean_ctor_get(x_61, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_61);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_39);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 1, x_146);
lean_ctor_set(x_60, 0, x_144);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_60);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_148, x_39);
x_150 = lean_ctor_get(x_59, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_59, 1);
lean_inc(x_151);
lean_dec(x_59);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_154 = x_150;
} else {
 lean_dec_ref(x_150);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_157 = x_151;
} else {
 lean_dec_ref(x_151);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
 lean_ctor_set_tag(x_158, 1);
}
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_39);
if (lean_is_scalar(x_154)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_154;
 lean_ctor_set_tag(x_159, 1);
}
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_153);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_152);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_161, x_39);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_43);
lean_ctor_set(x_163, 1, x_39);
x_164 = l_List_appendTR___rarg(x_163, x_149);
x_165 = l_List_appendTR___rarg(x_164, x_162);
x_166 = l_List_appendTR___rarg(x_42, x_165);
x_167 = lean_array_mk(x_166);
x_168 = lean_array_size(x_167);
x_169 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_168, x_16, x_167);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_169);
x_170 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_13);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_2);
x_173 = l_Lean_Json_mkObj(x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_12);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_3);
x_2 = x_8;
x_3 = x_175;
goto _start;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; size_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_177 = lean_ctor_get(x_60, 0);
x_178 = lean_ctor_get(x_60, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_60);
x_179 = lean_ctor_get(x_61, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_61, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_181 = x_61;
} else {
 lean_dec_ref(x_61);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
 lean_ctor_set_tag(x_182, 1);
}
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_39);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_177);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_185, x_39);
x_187 = lean_ctor_get(x_59, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_59, 1);
lean_inc(x_188);
lean_dec(x_59);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_194 = x_188;
} else {
 lean_dec_ref(x_188);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
 lean_ctor_set_tag(x_195, 1);
}
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_39);
if (lean_is_scalar(x_191)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_191;
 lean_ctor_set_tag(x_196, 1);
}
lean_ctor_set(x_196, 0, x_192);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_190);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_198, x_39);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_43);
lean_ctor_set(x_200, 1, x_39);
x_201 = l_List_appendTR___rarg(x_200, x_186);
x_202 = l_List_appendTR___rarg(x_201, x_199);
x_203 = l_List_appendTR___rarg(x_42, x_202);
x_204 = lean_array_mk(x_203);
x_205 = lean_array_size(x_204);
x_206 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_205, x_16, x_204);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_206);
x_207 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_13);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_2);
x_210 = l_Lean_Json_mkObj(x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_12);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_3);
x_2 = x_8;
x_3 = x_212;
goto _start;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; size_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_214 = lean_ctor_get(x_43, 0);
lean_inc(x_214);
lean_dec(x_43);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 2);
lean_inc(x_217);
lean_dec(x_214);
x_218 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_218, 0, x_215);
x_219 = lean_ctor_get(x_216, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_216, 1);
lean_inc(x_220);
lean_dec(x_216);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_223 = x_219;
} else {
 lean_dec_ref(x_219);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_220, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_220, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_226 = x_220;
} else {
 lean_dec_ref(x_220);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
 lean_ctor_set_tag(x_227, 1);
}
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_39);
if (lean_is_scalar(x_223)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_223;
 lean_ctor_set_tag(x_228, 1);
}
lean_ctor_set(x_228, 0, x_224);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_222);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_221);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_230, x_39);
x_232 = lean_ctor_get(x_217, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_217, 1);
lean_inc(x_233);
lean_dec(x_217);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_236 = x_232;
} else {
 lean_dec_ref(x_232);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_239 = x_233;
} else {
 lean_dec_ref(x_233);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
 lean_ctor_set_tag(x_240, 1);
}
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_39);
if (lean_is_scalar(x_236)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_236;
 lean_ctor_set_tag(x_241, 1);
}
lean_ctor_set(x_241, 0, x_237);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_235);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_234);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_243, x_39);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_218);
lean_ctor_set(x_245, 1, x_39);
x_246 = l_List_appendTR___rarg(x_245, x_231);
x_247 = l_List_appendTR___rarg(x_246, x_244);
x_248 = l_List_appendTR___rarg(x_42, x_247);
x_249 = lean_array_mk(x_248);
x_250 = lean_array_size(x_249);
x_251 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_250, x_16, x_249);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_251);
x_252 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_13);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_2);
x_255 = l_Lean_Json_mkObj(x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_12);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_3);
x_2 = x_8;
x_3 = x_257;
goto _start;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_259 = lean_ctor_get(x_31, 0);
x_260 = lean_ctor_get(x_31, 1);
x_261 = lean_ctor_get(x_32, 0);
x_262 = lean_ctor_get(x_32, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_32);
x_263 = lean_box(0);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_264);
lean_ctor_set(x_31, 0, x_261);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_260);
lean_ctor_set(x_265, 1, x_31);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_259);
lean_ctor_set(x_266, 1, x_265);
x_267 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_266, x_263);
x_268 = lean_ctor_get(x_29, 1);
lean_inc(x_268);
lean_dec(x_29);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; size_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_269 = l_List_appendTR___rarg(x_267, x_263);
x_270 = lean_array_mk(x_269);
x_271 = lean_array_size(x_270);
x_272 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_271, x_16, x_270);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_272);
x_273 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_13);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_2);
x_276 = l_Lean_Json_mkObj(x_275);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_12);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_3);
x_2 = x_8;
x_3 = x_278;
goto _start;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; size_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_280 = lean_ctor_get(x_268, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_281 = x_268;
} else {
 lean_dec_ref(x_268);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_280, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_280, 2);
lean_inc(x_284);
lean_dec(x_280);
if (lean_is_scalar(x_281)) {
 x_285 = lean_alloc_ctor(3, 1, 0);
} else {
 x_285 = x_281;
 lean_ctor_set_tag(x_285, 3);
}
lean_ctor_set(x_285, 0, x_282);
x_286 = lean_ctor_get(x_283, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
lean_dec(x_283);
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_290 = x_286;
} else {
 lean_dec_ref(x_286);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_287, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_287, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_293 = x_287;
} else {
 lean_dec_ref(x_287);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
 lean_ctor_set_tag(x_294, 1);
}
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_263);
if (lean_is_scalar(x_290)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_290;
 lean_ctor_set_tag(x_295, 1);
}
lean_ctor_set(x_295, 0, x_291);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_289);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_288);
lean_ctor_set(x_297, 1, x_296);
x_298 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_297, x_263);
x_299 = lean_ctor_get(x_284, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_284, 1);
lean_inc(x_300);
lean_dec(x_284);
x_301 = lean_ctor_get(x_299, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_303 = x_299;
} else {
 lean_dec_ref(x_299);
 x_303 = lean_box(0);
}
x_304 = lean_ctor_get(x_300, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_300, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_306 = x_300;
} else {
 lean_dec_ref(x_300);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
 lean_ctor_set_tag(x_307, 1);
}
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_263);
if (lean_is_scalar(x_303)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_303;
 lean_ctor_set_tag(x_308, 1);
}
lean_ctor_set(x_308, 0, x_304);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_302);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_301);
lean_ctor_set(x_310, 1, x_309);
x_311 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_310, x_263);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_285);
lean_ctor_set(x_312, 1, x_263);
x_313 = l_List_appendTR___rarg(x_312, x_298);
x_314 = l_List_appendTR___rarg(x_313, x_311);
x_315 = l_List_appendTR___rarg(x_267, x_314);
x_316 = lean_array_mk(x_315);
x_317 = lean_array_size(x_316);
x_318 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_317, x_16, x_316);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_318);
x_319 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_13);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_2);
x_322 = l_Lean_Json_mkObj(x_321);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_12);
lean_ctor_set(x_323, 1, x_322);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_3);
x_2 = x_8;
x_3 = x_324;
goto _start;
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_326 = lean_ctor_get(x_31, 0);
x_327 = lean_ctor_get(x_31, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_31);
x_328 = lean_ctor_get(x_32, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_32, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_330 = x_32;
} else {
 lean_dec_ref(x_32);
 x_330 = lean_box(0);
}
x_331 = lean_box(0);
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_330;
 lean_ctor_set_tag(x_332, 1);
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_328);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_327);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_326);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_335, x_331);
x_337 = lean_ctor_get(x_29, 1);
lean_inc(x_337);
lean_dec(x_29);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; size_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_338 = l_List_appendTR___rarg(x_336, x_331);
x_339 = lean_array_mk(x_338);
x_340 = lean_array_size(x_339);
x_341 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_340, x_16, x_339);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_341);
x_342 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_13);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_2);
x_345 = l_Lean_Json_mkObj(x_344);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_12);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_3);
x_2 = x_8;
x_3 = x_347;
goto _start;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; size_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_349 = lean_ctor_get(x_337, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_350 = x_337;
} else {
 lean_dec_ref(x_337);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_349, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 2);
lean_inc(x_353);
lean_dec(x_349);
if (lean_is_scalar(x_350)) {
 x_354 = lean_alloc_ctor(3, 1, 0);
} else {
 x_354 = x_350;
 lean_ctor_set_tag(x_354, 3);
}
lean_ctor_set(x_354, 0, x_351);
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
lean_dec(x_352);
x_357 = lean_ctor_get(x_355, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_355, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_359 = x_355;
} else {
 lean_dec_ref(x_355);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_356, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_356, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_362 = x_356;
} else {
 lean_dec_ref(x_356);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
 lean_ctor_set_tag(x_363, 1);
}
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_331);
if (lean_is_scalar(x_359)) {
 x_364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_364 = x_359;
 lean_ctor_set_tag(x_364, 1);
}
lean_ctor_set(x_364, 0, x_360);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_358);
lean_ctor_set(x_365, 1, x_364);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_357);
lean_ctor_set(x_366, 1, x_365);
x_367 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_366, x_331);
x_368 = lean_ctor_get(x_353, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_353, 1);
lean_inc(x_369);
lean_dec(x_353);
x_370 = lean_ctor_get(x_368, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_372 = x_368;
} else {
 lean_dec_ref(x_368);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_369, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_369, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_375 = x_369;
} else {
 lean_dec_ref(x_369);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_375;
 lean_ctor_set_tag(x_376, 1);
}
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_331);
if (lean_is_scalar(x_372)) {
 x_377 = lean_alloc_ctor(1, 2, 0);
} else {
 x_377 = x_372;
 lean_ctor_set_tag(x_377, 1);
}
lean_ctor_set(x_377, 0, x_373);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_371);
lean_ctor_set(x_378, 1, x_377);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_370);
lean_ctor_set(x_379, 1, x_378);
x_380 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_379, x_331);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_354);
lean_ctor_set(x_381, 1, x_331);
x_382 = l_List_appendTR___rarg(x_381, x_367);
x_383 = l_List_appendTR___rarg(x_382, x_380);
x_384 = l_List_appendTR___rarg(x_336, x_383);
x_385 = lean_array_mk(x_384);
x_386 = lean_array_size(x_385);
x_387 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_386, x_16, x_385);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_387);
x_388 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_13);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_2);
x_391 = l_Lean_Json_mkObj(x_390);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_12);
lean_ctor_set(x_392, 1, x_391);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_3);
x_2 = x_8;
x_3 = x_393;
goto _start;
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_395 = lean_ctor_get(x_13, 0);
lean_inc(x_395);
lean_dec(x_13);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_397, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_401 = x_397;
} else {
 lean_dec_ref(x_397);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_398, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_398, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_404 = x_398;
} else {
 lean_dec_ref(x_398);
 x_404 = lean_box(0);
}
x_405 = lean_box(0);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_404;
 lean_ctor_set_tag(x_406, 1);
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_405);
if (lean_is_scalar(x_401)) {
 x_407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_407 = x_401;
 lean_ctor_set_tag(x_407, 1);
}
lean_ctor_set(x_407, 0, x_402);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_400);
lean_ctor_set(x_408, 1, x_407);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_399);
lean_ctor_set(x_409, 1, x_408);
x_410 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_409, x_405);
x_411 = lean_ctor_get(x_395, 1);
lean_inc(x_411);
lean_dec(x_395);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; size_t x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_412 = l_List_appendTR___rarg(x_410, x_405);
x_413 = lean_array_mk(x_412);
x_414 = lean_array_size(x_413);
x_415 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_414, x_16, x_413);
x_416 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_416, 0, x_415);
x_417 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_416);
x_419 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_2);
x_420 = l_Lean_Json_mkObj(x_419);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_12);
lean_ctor_set(x_421, 1, x_420);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_3);
x_2 = x_8;
x_3 = x_422;
goto _start;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; size_t x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_424 = lean_ctor_get(x_411, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 x_425 = x_411;
} else {
 lean_dec_ref(x_411);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_424, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_424, 2);
lean_inc(x_428);
lean_dec(x_424);
if (lean_is_scalar(x_425)) {
 x_429 = lean_alloc_ctor(3, 1, 0);
} else {
 x_429 = x_425;
 lean_ctor_set_tag(x_429, 3);
}
lean_ctor_set(x_429, 0, x_426);
x_430 = lean_ctor_get(x_427, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_427, 1);
lean_inc(x_431);
lean_dec(x_427);
x_432 = lean_ctor_get(x_430, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_430, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_434 = x_430;
} else {
 lean_dec_ref(x_430);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_431, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_431, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_437 = x_431;
} else {
 lean_dec_ref(x_431);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_438 = x_437;
 lean_ctor_set_tag(x_438, 1);
}
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_405);
if (lean_is_scalar(x_434)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_434;
 lean_ctor_set_tag(x_439, 1);
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_438);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_433);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_432);
lean_ctor_set(x_441, 1, x_440);
x_442 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_441, x_405);
x_443 = lean_ctor_get(x_428, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_428, 1);
lean_inc(x_444);
lean_dec(x_428);
x_445 = lean_ctor_get(x_443, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_443, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_447 = x_443;
} else {
 lean_dec_ref(x_443);
 x_447 = lean_box(0);
}
x_448 = lean_ctor_get(x_444, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_444, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_450 = x_444;
} else {
 lean_dec_ref(x_444);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_450;
 lean_ctor_set_tag(x_451, 1);
}
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_405);
if (lean_is_scalar(x_447)) {
 x_452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_452 = x_447;
 lean_ctor_set_tag(x_452, 1);
}
lean_ctor_set(x_452, 0, x_448);
lean_ctor_set(x_452, 1, x_451);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_446);
lean_ctor_set(x_453, 1, x_452);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_445);
lean_ctor_set(x_454, 1, x_453);
x_455 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_454, x_405);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_429);
lean_ctor_set(x_456, 1, x_405);
x_457 = l_List_appendTR___rarg(x_456, x_442);
x_458 = l_List_appendTR___rarg(x_457, x_455);
x_459 = l_List_appendTR___rarg(x_410, x_458);
x_460 = lean_array_mk(x_459);
x_461 = lean_array_size(x_460);
x_462 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_461, x_16, x_460);
x_463 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_464 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_463);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_2);
x_467 = l_Lean_Json_mkObj(x_466);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_12);
lean_ctor_set(x_468, 1, x_467);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_3);
x_2 = x_8;
x_3 = x_469;
goto _start;
}
}
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; size_t x_478; size_t x_479; lean_object* x_480; size_t x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_471 = lean_ctor_get(x_2, 1);
x_472 = lean_ctor_get(x_6, 0);
x_473 = lean_ctor_get(x_6, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_6);
x_474 = l_Lean_Lsp_RefIdent_toJson(x_472);
x_475 = l_Lean_Json_compress(x_474);
x_476 = lean_ctor_get(x_473, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_473, 1);
lean_inc(x_477);
lean_dec(x_473);
x_478 = lean_array_size(x_477);
x_479 = 0;
x_480 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_478, x_479, x_477);
x_481 = lean_array_size(x_480);
x_482 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(x_479, x_481, x_479, x_480);
x_483 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_483, 0, x_482);
x_484 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_483);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_485);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_486 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_2);
x_488 = l_Lean_Json_mkObj(x_487);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_475);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_3);
x_2 = x_471;
x_3 = x_490;
goto _start;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_492 = lean_ctor_get(x_476, 0);
lean_inc(x_492);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_493 = x_476;
} else {
 lean_dec_ref(x_476);
 x_493 = lean_box(0);
}
x_494 = lean_ctor_get(x_492, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_499 = x_495;
} else {
 lean_dec_ref(x_495);
 x_499 = lean_box(0);
}
x_500 = lean_ctor_get(x_496, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_496, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_502 = x_496;
} else {
 lean_dec_ref(x_496);
 x_502 = lean_box(0);
}
x_503 = lean_box(0);
if (lean_is_scalar(x_502)) {
 x_504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_504 = x_502;
 lean_ctor_set_tag(x_504, 1);
}
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_503);
if (lean_is_scalar(x_499)) {
 x_505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_505 = x_499;
 lean_ctor_set_tag(x_505, 1);
}
lean_ctor_set(x_505, 0, x_500);
lean_ctor_set(x_505, 1, x_504);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_498);
lean_ctor_set(x_506, 1, x_505);
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_497);
lean_ctor_set(x_507, 1, x_506);
x_508 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_507, x_503);
x_509 = lean_ctor_get(x_492, 1);
lean_inc(x_509);
lean_dec(x_492);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; size_t x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_510 = l_List_appendTR___rarg(x_508, x_503);
x_511 = lean_array_mk(x_510);
x_512 = lean_array_size(x_511);
x_513 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_512, x_479, x_511);
if (lean_is_scalar(x_493)) {
 x_514 = lean_alloc_ctor(4, 1, 0);
} else {
 x_514 = x_493;
 lean_ctor_set_tag(x_514, 4);
}
lean_ctor_set(x_514, 0, x_513);
x_515 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_514);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_2);
x_518 = l_Lean_Json_mkObj(x_517);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_475);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_3);
x_2 = x_471;
x_3 = x_520;
goto _start;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; size_t x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_522 = lean_ctor_get(x_509, 0);
lean_inc(x_522);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 x_523 = x_509;
} else {
 lean_dec_ref(x_509);
 x_523 = lean_box(0);
}
x_524 = lean_ctor_get(x_522, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_525);
x_526 = lean_ctor_get(x_522, 2);
lean_inc(x_526);
lean_dec(x_522);
if (lean_is_scalar(x_523)) {
 x_527 = lean_alloc_ctor(3, 1, 0);
} else {
 x_527 = x_523;
 lean_ctor_set_tag(x_527, 3);
}
lean_ctor_set(x_527, 0, x_524);
x_528 = lean_ctor_get(x_525, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_525, 1);
lean_inc(x_529);
lean_dec(x_525);
x_530 = lean_ctor_get(x_528, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_528, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_532 = x_528;
} else {
 lean_dec_ref(x_528);
 x_532 = lean_box(0);
}
x_533 = lean_ctor_get(x_529, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_529, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_535 = x_529;
} else {
 lean_dec_ref(x_529);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 2, 0);
} else {
 x_536 = x_535;
 lean_ctor_set_tag(x_536, 1);
}
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_503);
if (lean_is_scalar(x_532)) {
 x_537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_537 = x_532;
 lean_ctor_set_tag(x_537, 1);
}
lean_ctor_set(x_537, 0, x_533);
lean_ctor_set(x_537, 1, x_536);
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_531);
lean_ctor_set(x_538, 1, x_537);
x_539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_539, 0, x_530);
lean_ctor_set(x_539, 1, x_538);
x_540 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_539, x_503);
x_541 = lean_ctor_get(x_526, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_526, 1);
lean_inc(x_542);
lean_dec(x_526);
x_543 = lean_ctor_get(x_541, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_545 = x_541;
} else {
 lean_dec_ref(x_541);
 x_545 = lean_box(0);
}
x_546 = lean_ctor_get(x_542, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_542, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 x_548 = x_542;
} else {
 lean_dec_ref(x_542);
 x_548 = lean_box(0);
}
if (lean_is_scalar(x_548)) {
 x_549 = lean_alloc_ctor(1, 2, 0);
} else {
 x_549 = x_548;
 lean_ctor_set_tag(x_549, 1);
}
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_503);
if (lean_is_scalar(x_545)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_545;
 lean_ctor_set_tag(x_550, 1);
}
lean_ctor_set(x_550, 0, x_546);
lean_ctor_set(x_550, 1, x_549);
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_544);
lean_ctor_set(x_551, 1, x_550);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_543);
lean_ctor_set(x_552, 1, x_551);
x_553 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_552, x_503);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_527);
lean_ctor_set(x_554, 1, x_503);
x_555 = l_List_appendTR___rarg(x_554, x_540);
x_556 = l_List_appendTR___rarg(x_555, x_553);
x_557 = l_List_appendTR___rarg(x_508, x_556);
x_558 = lean_array_mk(x_557);
x_559 = lean_array_size(x_558);
x_560 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_559, x_479, x_558);
if (lean_is_scalar(x_493)) {
 x_561 = lean_alloc_ctor(4, 1, 0);
} else {
 x_561 = x_493;
 lean_ctor_set_tag(x_561, 4);
}
lean_ctor_set(x_561, 0, x_560);
x_562 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_561);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_2);
x_565 = l_Lean_Json_mkObj(x_564);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_475);
lean_ctor_set(x_566, 1, x_565);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_3);
x_2 = x_471;
x_3 = x_567;
goto _start;
}
}
}
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; size_t x_578; size_t x_579; lean_object* x_580; size_t x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_569 = lean_ctor_get(x_2, 0);
x_570 = lean_ctor_get(x_2, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_2);
x_571 = lean_ctor_get(x_569, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_569, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_573 = x_569;
} else {
 lean_dec_ref(x_569);
 x_573 = lean_box(0);
}
x_574 = l_Lean_Lsp_RefIdent_toJson(x_571);
x_575 = l_Lean_Json_compress(x_574);
x_576 = lean_ctor_get(x_572, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_572, 1);
lean_inc(x_577);
lean_dec(x_572);
x_578 = lean_array_size(x_577);
x_579 = 0;
x_580 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_578, x_579, x_577);
x_581 = lean_array_size(x_580);
x_582 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(x_579, x_581, x_579, x_580);
x_583 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_583, 0, x_582);
x_584 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
if (lean_is_scalar(x_573)) {
 x_585 = lean_alloc_ctor(0, 2, 0);
} else {
 x_585 = x_573;
}
lean_ctor_set(x_585, 0, x_584);
lean_ctor_set(x_585, 1, x_583);
lean_inc(x_1);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_1);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_587 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_586);
x_589 = l_Lean_Json_mkObj(x_588);
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_575);
lean_ctor_set(x_590, 1, x_589);
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_3);
x_2 = x_570;
x_3 = x_591;
goto _start;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_593 = lean_ctor_get(x_576, 0);
lean_inc(x_593);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 x_594 = x_576;
} else {
 lean_dec_ref(x_576);
 x_594 = lean_box(0);
}
x_595 = lean_ctor_get(x_593, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
x_598 = lean_ctor_get(x_596, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_596, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_600 = x_596;
} else {
 lean_dec_ref(x_596);
 x_600 = lean_box(0);
}
x_601 = lean_ctor_get(x_597, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_597, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 x_603 = x_597;
} else {
 lean_dec_ref(x_597);
 x_603 = lean_box(0);
}
x_604 = lean_box(0);
if (lean_is_scalar(x_603)) {
 x_605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_605 = x_603;
 lean_ctor_set_tag(x_605, 1);
}
lean_ctor_set(x_605, 0, x_602);
lean_ctor_set(x_605, 1, x_604);
if (lean_is_scalar(x_600)) {
 x_606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_606 = x_600;
 lean_ctor_set_tag(x_606, 1);
}
lean_ctor_set(x_606, 0, x_601);
lean_ctor_set(x_606, 1, x_605);
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_599);
lean_ctor_set(x_607, 1, x_606);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_598);
lean_ctor_set(x_608, 1, x_607);
x_609 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_608, x_604);
x_610 = lean_ctor_get(x_593, 1);
lean_inc(x_610);
lean_dec(x_593);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; size_t x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_611 = l_List_appendTR___rarg(x_609, x_604);
x_612 = lean_array_mk(x_611);
x_613 = lean_array_size(x_612);
x_614 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_613, x_579, x_612);
if (lean_is_scalar(x_594)) {
 x_615 = lean_alloc_ctor(4, 1, 0);
} else {
 x_615 = x_594;
 lean_ctor_set_tag(x_615, 4);
}
lean_ctor_set(x_615, 0, x_614);
x_616 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_617 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_615);
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_586);
x_619 = l_Lean_Json_mkObj(x_618);
x_620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_620, 0, x_575);
lean_ctor_set(x_620, 1, x_619);
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_3);
x_2 = x_570;
x_3 = x_621;
goto _start;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; size_t x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_623 = lean_ctor_get(x_610, 0);
lean_inc(x_623);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_624 = x_610;
} else {
 lean_dec_ref(x_610);
 x_624 = lean_box(0);
}
x_625 = lean_ctor_get(x_623, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_623, 1);
lean_inc(x_626);
x_627 = lean_ctor_get(x_623, 2);
lean_inc(x_627);
lean_dec(x_623);
if (lean_is_scalar(x_624)) {
 x_628 = lean_alloc_ctor(3, 1, 0);
} else {
 x_628 = x_624;
 lean_ctor_set_tag(x_628, 3);
}
lean_ctor_set(x_628, 0, x_625);
x_629 = lean_ctor_get(x_626, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_626, 1);
lean_inc(x_630);
lean_dec(x_626);
x_631 = lean_ctor_get(x_629, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_629, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 x_633 = x_629;
} else {
 lean_dec_ref(x_629);
 x_633 = lean_box(0);
}
x_634 = lean_ctor_get(x_630, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_630, 1);
lean_inc(x_635);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 lean_ctor_release(x_630, 1);
 x_636 = x_630;
} else {
 lean_dec_ref(x_630);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(1, 2, 0);
} else {
 x_637 = x_636;
 lean_ctor_set_tag(x_637, 1);
}
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_604);
if (lean_is_scalar(x_633)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_633;
 lean_ctor_set_tag(x_638, 1);
}
lean_ctor_set(x_638, 0, x_634);
lean_ctor_set(x_638, 1, x_637);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_632);
lean_ctor_set(x_639, 1, x_638);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_631);
lean_ctor_set(x_640, 1, x_639);
x_641 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_640, x_604);
x_642 = lean_ctor_get(x_627, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_627, 1);
lean_inc(x_643);
lean_dec(x_627);
x_644 = lean_ctor_get(x_642, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_642, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 x_646 = x_642;
} else {
 lean_dec_ref(x_642);
 x_646 = lean_box(0);
}
x_647 = lean_ctor_get(x_643, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_643, 1);
lean_inc(x_648);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_649 = x_643;
} else {
 lean_dec_ref(x_643);
 x_649 = lean_box(0);
}
if (lean_is_scalar(x_649)) {
 x_650 = lean_alloc_ctor(1, 2, 0);
} else {
 x_650 = x_649;
 lean_ctor_set_tag(x_650, 1);
}
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_604);
if (lean_is_scalar(x_646)) {
 x_651 = lean_alloc_ctor(1, 2, 0);
} else {
 x_651 = x_646;
 lean_ctor_set_tag(x_651, 1);
}
lean_ctor_set(x_651, 0, x_647);
lean_ctor_set(x_651, 1, x_650);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_645);
lean_ctor_set(x_652, 1, x_651);
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_644);
lean_ctor_set(x_653, 1, x_652);
x_654 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_653, x_604);
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_628);
lean_ctor_set(x_655, 1, x_604);
x_656 = l_List_appendTR___rarg(x_655, x_641);
x_657 = l_List_appendTR___rarg(x_656, x_654);
x_658 = l_List_appendTR___rarg(x_609, x_657);
x_659 = lean_array_mk(x_658);
x_660 = lean_array_size(x_659);
x_661 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_660, x_579, x_659);
if (lean_is_scalar(x_594)) {
 x_662 = lean_alloc_ctor(4, 1, 0);
} else {
 x_662 = x_594;
 lean_ctor_set_tag(x_662, 4);
}
lean_ctor_set(x_662, 0, x_661);
x_663 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_664 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_662);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_586);
x_666 = l_Lean_Json_mkObj(x_665);
x_667 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_667, 0, x_575);
lean_ctor_set(x_667, 1, x_666);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_3);
x_2 = x_570;
x_3 = x_668;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Lean_Lsp_RefIdent_toJson(x_9);
x_12 = l_Lean_Json_compress(x_11);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_array_size(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_15, x_16, x_14);
x_18 = lean_array_size(x_17);
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(x_16, x_18, x_16, x_17);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_6, 0, x_21);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_24 = l_Lean_Json_mkObj(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
x_2 = x_8;
x_3 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
x_39 = lean_box(0);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_39);
lean_ctor_set(x_32, 0, x_38);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_32);
lean_ctor_set(x_31, 0, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_41, x_39);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = l_List_appendTR___rarg(x_42, x_39);
x_45 = lean_array_mk(x_44);
x_46 = lean_array_size(x_45);
x_47 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_46, x_16, x_45);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_47);
x_48 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_13);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_2);
x_51 = l_Lean_Json_mkObj(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
x_2 = x_8;
x_3 = x_53;
goto _start;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_43);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_43, 0);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 2);
lean_inc(x_59);
lean_dec(x_56);
lean_ctor_set_tag(x_43, 3);
lean_ctor_set(x_43, 0, x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 1, x_39);
lean_ctor_set(x_61, 0, x_67);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 1, x_61);
lean_ctor_set(x_60, 0, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_60);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_69, x_39);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
lean_dec(x_59);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_ctor_get(x_71, 1);
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_ctor_get(x_72, 1);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_39);
lean_ctor_set(x_72, 0, x_78);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_72);
lean_ctor_set(x_71, 0, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_71);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_80, x_39);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_43);
lean_ctor_set(x_82, 1, x_39);
x_83 = l_List_appendTR___rarg(x_82, x_70);
x_84 = l_List_appendTR___rarg(x_83, x_81);
x_85 = l_List_appendTR___rarg(x_42, x_84);
x_86 = lean_array_mk(x_85);
x_87 = lean_array_size(x_86);
x_88 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_87, x_16, x_86);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_88);
x_89 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_13);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_2);
x_92 = l_Lean_Json_mkObj(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_12);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_3);
x_2 = x_8;
x_3 = x_94;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_96 = lean_ctor_get(x_71, 0);
x_97 = lean_ctor_get(x_71, 1);
x_98 = lean_ctor_get(x_72, 0);
x_99 = lean_ctor_get(x_72, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_72);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_39);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_100);
lean_ctor_set(x_71, 0, x_98);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_71);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_102, x_39);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_43);
lean_ctor_set(x_104, 1, x_39);
x_105 = l_List_appendTR___rarg(x_104, x_70);
x_106 = l_List_appendTR___rarg(x_105, x_103);
x_107 = l_List_appendTR___rarg(x_42, x_106);
x_108 = lean_array_mk(x_107);
x_109 = lean_array_size(x_108);
x_110 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_109, x_16, x_108);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_110);
x_111 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_13);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_2);
x_114 = l_Lean_Json_mkObj(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_12);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_3);
x_2 = x_8;
x_3 = x_116;
goto _start;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; size_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_118 = lean_ctor_get(x_71, 0);
x_119 = lean_ctor_get(x_71, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_71);
x_120 = lean_ctor_get(x_72, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_72, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_122 = x_72;
} else {
 lean_dec_ref(x_72);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
 lean_ctor_set_tag(x_123, 1);
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_39);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_118);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_126, x_39);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_43);
lean_ctor_set(x_128, 1, x_39);
x_129 = l_List_appendTR___rarg(x_128, x_70);
x_130 = l_List_appendTR___rarg(x_129, x_127);
x_131 = l_List_appendTR___rarg(x_42, x_130);
x_132 = lean_array_mk(x_131);
x_133 = lean_array_size(x_132);
x_134 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_133, x_16, x_132);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_134);
x_135 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_13);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_2);
x_138 = l_Lean_Json_mkObj(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_12);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_3);
x_2 = x_8;
x_3 = x_140;
goto _start;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; size_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_142 = lean_ctor_get(x_60, 0);
x_143 = lean_ctor_get(x_60, 1);
x_144 = lean_ctor_get(x_61, 0);
x_145 = lean_ctor_get(x_61, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_61);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_39);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 1, x_146);
lean_ctor_set(x_60, 0, x_144);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_60);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_148, x_39);
x_150 = lean_ctor_get(x_59, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_59, 1);
lean_inc(x_151);
lean_dec(x_59);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_154 = x_150;
} else {
 lean_dec_ref(x_150);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_157 = x_151;
} else {
 lean_dec_ref(x_151);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
 lean_ctor_set_tag(x_158, 1);
}
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_39);
if (lean_is_scalar(x_154)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_154;
 lean_ctor_set_tag(x_159, 1);
}
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_153);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_152);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_161, x_39);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_43);
lean_ctor_set(x_163, 1, x_39);
x_164 = l_List_appendTR___rarg(x_163, x_149);
x_165 = l_List_appendTR___rarg(x_164, x_162);
x_166 = l_List_appendTR___rarg(x_42, x_165);
x_167 = lean_array_mk(x_166);
x_168 = lean_array_size(x_167);
x_169 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_168, x_16, x_167);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_169);
x_170 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_13);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_2);
x_173 = l_Lean_Json_mkObj(x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_12);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_3);
x_2 = x_8;
x_3 = x_175;
goto _start;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; size_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_177 = lean_ctor_get(x_60, 0);
x_178 = lean_ctor_get(x_60, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_60);
x_179 = lean_ctor_get(x_61, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_61, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_181 = x_61;
} else {
 lean_dec_ref(x_61);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
 lean_ctor_set_tag(x_182, 1);
}
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_39);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_177);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_185, x_39);
x_187 = lean_ctor_get(x_59, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_59, 1);
lean_inc(x_188);
lean_dec(x_59);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_194 = x_188;
} else {
 lean_dec_ref(x_188);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
 lean_ctor_set_tag(x_195, 1);
}
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_39);
if (lean_is_scalar(x_191)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_191;
 lean_ctor_set_tag(x_196, 1);
}
lean_ctor_set(x_196, 0, x_192);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_190);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_198, x_39);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_43);
lean_ctor_set(x_200, 1, x_39);
x_201 = l_List_appendTR___rarg(x_200, x_186);
x_202 = l_List_appendTR___rarg(x_201, x_199);
x_203 = l_List_appendTR___rarg(x_42, x_202);
x_204 = lean_array_mk(x_203);
x_205 = lean_array_size(x_204);
x_206 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_205, x_16, x_204);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_206);
x_207 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_13);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_2);
x_210 = l_Lean_Json_mkObj(x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_12);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_3);
x_2 = x_8;
x_3 = x_212;
goto _start;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; size_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_214 = lean_ctor_get(x_43, 0);
lean_inc(x_214);
lean_dec(x_43);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 2);
lean_inc(x_217);
lean_dec(x_214);
x_218 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_218, 0, x_215);
x_219 = lean_ctor_get(x_216, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_216, 1);
lean_inc(x_220);
lean_dec(x_216);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_223 = x_219;
} else {
 lean_dec_ref(x_219);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_220, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_220, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_226 = x_220;
} else {
 lean_dec_ref(x_220);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
 lean_ctor_set_tag(x_227, 1);
}
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_39);
if (lean_is_scalar(x_223)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_223;
 lean_ctor_set_tag(x_228, 1);
}
lean_ctor_set(x_228, 0, x_224);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_222);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_221);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_230, x_39);
x_232 = lean_ctor_get(x_217, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_217, 1);
lean_inc(x_233);
lean_dec(x_217);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_236 = x_232;
} else {
 lean_dec_ref(x_232);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_239 = x_233;
} else {
 lean_dec_ref(x_233);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
 lean_ctor_set_tag(x_240, 1);
}
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_39);
if (lean_is_scalar(x_236)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_236;
 lean_ctor_set_tag(x_241, 1);
}
lean_ctor_set(x_241, 0, x_237);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_235);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_234);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_243, x_39);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_218);
lean_ctor_set(x_245, 1, x_39);
x_246 = l_List_appendTR___rarg(x_245, x_231);
x_247 = l_List_appendTR___rarg(x_246, x_244);
x_248 = l_List_appendTR___rarg(x_42, x_247);
x_249 = lean_array_mk(x_248);
x_250 = lean_array_size(x_249);
x_251 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_250, x_16, x_249);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_251);
x_252 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_13);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_2);
x_255 = l_Lean_Json_mkObj(x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_12);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_3);
x_2 = x_8;
x_3 = x_257;
goto _start;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_259 = lean_ctor_get(x_31, 0);
x_260 = lean_ctor_get(x_31, 1);
x_261 = lean_ctor_get(x_32, 0);
x_262 = lean_ctor_get(x_32, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_32);
x_263 = lean_box(0);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_264);
lean_ctor_set(x_31, 0, x_261);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_260);
lean_ctor_set(x_265, 1, x_31);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_259);
lean_ctor_set(x_266, 1, x_265);
x_267 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_266, x_263);
x_268 = lean_ctor_get(x_29, 1);
lean_inc(x_268);
lean_dec(x_29);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; size_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_269 = l_List_appendTR___rarg(x_267, x_263);
x_270 = lean_array_mk(x_269);
x_271 = lean_array_size(x_270);
x_272 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_271, x_16, x_270);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_272);
x_273 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_13);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_2);
x_276 = l_Lean_Json_mkObj(x_275);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_12);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_3);
x_2 = x_8;
x_3 = x_278;
goto _start;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; size_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_280 = lean_ctor_get(x_268, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_281 = x_268;
} else {
 lean_dec_ref(x_268);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_280, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_280, 2);
lean_inc(x_284);
lean_dec(x_280);
if (lean_is_scalar(x_281)) {
 x_285 = lean_alloc_ctor(3, 1, 0);
} else {
 x_285 = x_281;
 lean_ctor_set_tag(x_285, 3);
}
lean_ctor_set(x_285, 0, x_282);
x_286 = lean_ctor_get(x_283, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
lean_dec(x_283);
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_290 = x_286;
} else {
 lean_dec_ref(x_286);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_287, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_287, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_293 = x_287;
} else {
 lean_dec_ref(x_287);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
 lean_ctor_set_tag(x_294, 1);
}
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_263);
if (lean_is_scalar(x_290)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_290;
 lean_ctor_set_tag(x_295, 1);
}
lean_ctor_set(x_295, 0, x_291);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_289);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_288);
lean_ctor_set(x_297, 1, x_296);
x_298 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_297, x_263);
x_299 = lean_ctor_get(x_284, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_284, 1);
lean_inc(x_300);
lean_dec(x_284);
x_301 = lean_ctor_get(x_299, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_303 = x_299;
} else {
 lean_dec_ref(x_299);
 x_303 = lean_box(0);
}
x_304 = lean_ctor_get(x_300, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_300, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_306 = x_300;
} else {
 lean_dec_ref(x_300);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
 lean_ctor_set_tag(x_307, 1);
}
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_263);
if (lean_is_scalar(x_303)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_303;
 lean_ctor_set_tag(x_308, 1);
}
lean_ctor_set(x_308, 0, x_304);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_302);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_301);
lean_ctor_set(x_310, 1, x_309);
x_311 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_310, x_263);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_285);
lean_ctor_set(x_312, 1, x_263);
x_313 = l_List_appendTR___rarg(x_312, x_298);
x_314 = l_List_appendTR___rarg(x_313, x_311);
x_315 = l_List_appendTR___rarg(x_267, x_314);
x_316 = lean_array_mk(x_315);
x_317 = lean_array_size(x_316);
x_318 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_317, x_16, x_316);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_318);
x_319 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_13);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_2);
x_322 = l_Lean_Json_mkObj(x_321);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_12);
lean_ctor_set(x_323, 1, x_322);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_3);
x_2 = x_8;
x_3 = x_324;
goto _start;
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_326 = lean_ctor_get(x_31, 0);
x_327 = lean_ctor_get(x_31, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_31);
x_328 = lean_ctor_get(x_32, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_32, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_330 = x_32;
} else {
 lean_dec_ref(x_32);
 x_330 = lean_box(0);
}
x_331 = lean_box(0);
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_330;
 lean_ctor_set_tag(x_332, 1);
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_328);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_327);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_326);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_335, x_331);
x_337 = lean_ctor_get(x_29, 1);
lean_inc(x_337);
lean_dec(x_29);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; size_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_338 = l_List_appendTR___rarg(x_336, x_331);
x_339 = lean_array_mk(x_338);
x_340 = lean_array_size(x_339);
x_341 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_340, x_16, x_339);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_341);
x_342 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_13);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_2);
x_345 = l_Lean_Json_mkObj(x_344);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_12);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_3);
x_2 = x_8;
x_3 = x_347;
goto _start;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; size_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_349 = lean_ctor_get(x_337, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_350 = x_337;
} else {
 lean_dec_ref(x_337);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_349, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 2);
lean_inc(x_353);
lean_dec(x_349);
if (lean_is_scalar(x_350)) {
 x_354 = lean_alloc_ctor(3, 1, 0);
} else {
 x_354 = x_350;
 lean_ctor_set_tag(x_354, 3);
}
lean_ctor_set(x_354, 0, x_351);
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
lean_dec(x_352);
x_357 = lean_ctor_get(x_355, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_355, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_359 = x_355;
} else {
 lean_dec_ref(x_355);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_356, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_356, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_362 = x_356;
} else {
 lean_dec_ref(x_356);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
 lean_ctor_set_tag(x_363, 1);
}
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_331);
if (lean_is_scalar(x_359)) {
 x_364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_364 = x_359;
 lean_ctor_set_tag(x_364, 1);
}
lean_ctor_set(x_364, 0, x_360);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_358);
lean_ctor_set(x_365, 1, x_364);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_357);
lean_ctor_set(x_366, 1, x_365);
x_367 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_366, x_331);
x_368 = lean_ctor_get(x_353, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_353, 1);
lean_inc(x_369);
lean_dec(x_353);
x_370 = lean_ctor_get(x_368, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_372 = x_368;
} else {
 lean_dec_ref(x_368);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_369, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_369, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_375 = x_369;
} else {
 lean_dec_ref(x_369);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_375;
 lean_ctor_set_tag(x_376, 1);
}
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_331);
if (lean_is_scalar(x_372)) {
 x_377 = lean_alloc_ctor(1, 2, 0);
} else {
 x_377 = x_372;
 lean_ctor_set_tag(x_377, 1);
}
lean_ctor_set(x_377, 0, x_373);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_371);
lean_ctor_set(x_378, 1, x_377);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_370);
lean_ctor_set(x_379, 1, x_378);
x_380 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_379, x_331);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_354);
lean_ctor_set(x_381, 1, x_331);
x_382 = l_List_appendTR___rarg(x_381, x_367);
x_383 = l_List_appendTR___rarg(x_382, x_380);
x_384 = l_List_appendTR___rarg(x_336, x_383);
x_385 = lean_array_mk(x_384);
x_386 = lean_array_size(x_385);
x_387 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_386, x_16, x_385);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_387);
x_388 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_13);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_2);
x_391 = l_Lean_Json_mkObj(x_390);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_12);
lean_ctor_set(x_392, 1, x_391);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_3);
x_2 = x_8;
x_3 = x_393;
goto _start;
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_395 = lean_ctor_get(x_13, 0);
lean_inc(x_395);
lean_dec(x_13);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_397, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_401 = x_397;
} else {
 lean_dec_ref(x_397);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_398, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_398, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_404 = x_398;
} else {
 lean_dec_ref(x_398);
 x_404 = lean_box(0);
}
x_405 = lean_box(0);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_404;
 lean_ctor_set_tag(x_406, 1);
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_405);
if (lean_is_scalar(x_401)) {
 x_407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_407 = x_401;
 lean_ctor_set_tag(x_407, 1);
}
lean_ctor_set(x_407, 0, x_402);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_400);
lean_ctor_set(x_408, 1, x_407);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_399);
lean_ctor_set(x_409, 1, x_408);
x_410 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_409, x_405);
x_411 = lean_ctor_get(x_395, 1);
lean_inc(x_411);
lean_dec(x_395);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; size_t x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_412 = l_List_appendTR___rarg(x_410, x_405);
x_413 = lean_array_mk(x_412);
x_414 = lean_array_size(x_413);
x_415 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_414, x_16, x_413);
x_416 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_416, 0, x_415);
x_417 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_416);
x_419 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_2);
x_420 = l_Lean_Json_mkObj(x_419);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_12);
lean_ctor_set(x_421, 1, x_420);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_3);
x_2 = x_8;
x_3 = x_422;
goto _start;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; size_t x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_424 = lean_ctor_get(x_411, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 x_425 = x_411;
} else {
 lean_dec_ref(x_411);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_424, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_424, 2);
lean_inc(x_428);
lean_dec(x_424);
if (lean_is_scalar(x_425)) {
 x_429 = lean_alloc_ctor(3, 1, 0);
} else {
 x_429 = x_425;
 lean_ctor_set_tag(x_429, 3);
}
lean_ctor_set(x_429, 0, x_426);
x_430 = lean_ctor_get(x_427, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_427, 1);
lean_inc(x_431);
lean_dec(x_427);
x_432 = lean_ctor_get(x_430, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_430, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_434 = x_430;
} else {
 lean_dec_ref(x_430);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_431, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_431, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_437 = x_431;
} else {
 lean_dec_ref(x_431);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_438 = x_437;
 lean_ctor_set_tag(x_438, 1);
}
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_405);
if (lean_is_scalar(x_434)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_434;
 lean_ctor_set_tag(x_439, 1);
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_438);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_433);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_432);
lean_ctor_set(x_441, 1, x_440);
x_442 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_441, x_405);
x_443 = lean_ctor_get(x_428, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_428, 1);
lean_inc(x_444);
lean_dec(x_428);
x_445 = lean_ctor_get(x_443, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_443, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_447 = x_443;
} else {
 lean_dec_ref(x_443);
 x_447 = lean_box(0);
}
x_448 = lean_ctor_get(x_444, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_444, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_450 = x_444;
} else {
 lean_dec_ref(x_444);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_450;
 lean_ctor_set_tag(x_451, 1);
}
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_405);
if (lean_is_scalar(x_447)) {
 x_452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_452 = x_447;
 lean_ctor_set_tag(x_452, 1);
}
lean_ctor_set(x_452, 0, x_448);
lean_ctor_set(x_452, 1, x_451);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_446);
lean_ctor_set(x_453, 1, x_452);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_445);
lean_ctor_set(x_454, 1, x_453);
x_455 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_454, x_405);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_429);
lean_ctor_set(x_456, 1, x_405);
x_457 = l_List_appendTR___rarg(x_456, x_442);
x_458 = l_List_appendTR___rarg(x_457, x_455);
x_459 = l_List_appendTR___rarg(x_410, x_458);
x_460 = lean_array_mk(x_459);
x_461 = lean_array_size(x_460);
x_462 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_461, x_16, x_460);
x_463 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_464 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_463);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_2);
x_467 = l_Lean_Json_mkObj(x_466);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_12);
lean_ctor_set(x_468, 1, x_467);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_3);
x_2 = x_8;
x_3 = x_469;
goto _start;
}
}
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; size_t x_478; size_t x_479; lean_object* x_480; size_t x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_471 = lean_ctor_get(x_2, 1);
x_472 = lean_ctor_get(x_6, 0);
x_473 = lean_ctor_get(x_6, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_6);
x_474 = l_Lean_Lsp_RefIdent_toJson(x_472);
x_475 = l_Lean_Json_compress(x_474);
x_476 = lean_ctor_get(x_473, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_473, 1);
lean_inc(x_477);
lean_dec(x_473);
x_478 = lean_array_size(x_477);
x_479 = 0;
x_480 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_478, x_479, x_477);
x_481 = lean_array_size(x_480);
x_482 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(x_479, x_481, x_479, x_480);
x_483 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_483, 0, x_482);
x_484 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_483);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_485);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_486 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_2);
x_488 = l_Lean_Json_mkObj(x_487);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_475);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_3);
x_2 = x_471;
x_3 = x_490;
goto _start;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_492 = lean_ctor_get(x_476, 0);
lean_inc(x_492);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_493 = x_476;
} else {
 lean_dec_ref(x_476);
 x_493 = lean_box(0);
}
x_494 = lean_ctor_get(x_492, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_499 = x_495;
} else {
 lean_dec_ref(x_495);
 x_499 = lean_box(0);
}
x_500 = lean_ctor_get(x_496, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_496, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_502 = x_496;
} else {
 lean_dec_ref(x_496);
 x_502 = lean_box(0);
}
x_503 = lean_box(0);
if (lean_is_scalar(x_502)) {
 x_504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_504 = x_502;
 lean_ctor_set_tag(x_504, 1);
}
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_503);
if (lean_is_scalar(x_499)) {
 x_505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_505 = x_499;
 lean_ctor_set_tag(x_505, 1);
}
lean_ctor_set(x_505, 0, x_500);
lean_ctor_set(x_505, 1, x_504);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_498);
lean_ctor_set(x_506, 1, x_505);
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_497);
lean_ctor_set(x_507, 1, x_506);
x_508 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_507, x_503);
x_509 = lean_ctor_get(x_492, 1);
lean_inc(x_509);
lean_dec(x_492);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; size_t x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_510 = l_List_appendTR___rarg(x_508, x_503);
x_511 = lean_array_mk(x_510);
x_512 = lean_array_size(x_511);
x_513 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_512, x_479, x_511);
if (lean_is_scalar(x_493)) {
 x_514 = lean_alloc_ctor(4, 1, 0);
} else {
 x_514 = x_493;
 lean_ctor_set_tag(x_514, 4);
}
lean_ctor_set(x_514, 0, x_513);
x_515 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_514);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_2);
x_518 = l_Lean_Json_mkObj(x_517);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_475);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_3);
x_2 = x_471;
x_3 = x_520;
goto _start;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; size_t x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_522 = lean_ctor_get(x_509, 0);
lean_inc(x_522);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 x_523 = x_509;
} else {
 lean_dec_ref(x_509);
 x_523 = lean_box(0);
}
x_524 = lean_ctor_get(x_522, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_525);
x_526 = lean_ctor_get(x_522, 2);
lean_inc(x_526);
lean_dec(x_522);
if (lean_is_scalar(x_523)) {
 x_527 = lean_alloc_ctor(3, 1, 0);
} else {
 x_527 = x_523;
 lean_ctor_set_tag(x_527, 3);
}
lean_ctor_set(x_527, 0, x_524);
x_528 = lean_ctor_get(x_525, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_525, 1);
lean_inc(x_529);
lean_dec(x_525);
x_530 = lean_ctor_get(x_528, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_528, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_532 = x_528;
} else {
 lean_dec_ref(x_528);
 x_532 = lean_box(0);
}
x_533 = lean_ctor_get(x_529, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_529, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_535 = x_529;
} else {
 lean_dec_ref(x_529);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 2, 0);
} else {
 x_536 = x_535;
 lean_ctor_set_tag(x_536, 1);
}
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_503);
if (lean_is_scalar(x_532)) {
 x_537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_537 = x_532;
 lean_ctor_set_tag(x_537, 1);
}
lean_ctor_set(x_537, 0, x_533);
lean_ctor_set(x_537, 1, x_536);
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_531);
lean_ctor_set(x_538, 1, x_537);
x_539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_539, 0, x_530);
lean_ctor_set(x_539, 1, x_538);
x_540 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_539, x_503);
x_541 = lean_ctor_get(x_526, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_526, 1);
lean_inc(x_542);
lean_dec(x_526);
x_543 = lean_ctor_get(x_541, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_545 = x_541;
} else {
 lean_dec_ref(x_541);
 x_545 = lean_box(0);
}
x_546 = lean_ctor_get(x_542, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_542, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 x_548 = x_542;
} else {
 lean_dec_ref(x_542);
 x_548 = lean_box(0);
}
if (lean_is_scalar(x_548)) {
 x_549 = lean_alloc_ctor(1, 2, 0);
} else {
 x_549 = x_548;
 lean_ctor_set_tag(x_549, 1);
}
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_503);
if (lean_is_scalar(x_545)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_545;
 lean_ctor_set_tag(x_550, 1);
}
lean_ctor_set(x_550, 0, x_546);
lean_ctor_set(x_550, 1, x_549);
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_544);
lean_ctor_set(x_551, 1, x_550);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_543);
lean_ctor_set(x_552, 1, x_551);
x_553 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_552, x_503);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_527);
lean_ctor_set(x_554, 1, x_503);
x_555 = l_List_appendTR___rarg(x_554, x_540);
x_556 = l_List_appendTR___rarg(x_555, x_553);
x_557 = l_List_appendTR___rarg(x_508, x_556);
x_558 = lean_array_mk(x_557);
x_559 = lean_array_size(x_558);
x_560 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_559, x_479, x_558);
if (lean_is_scalar(x_493)) {
 x_561 = lean_alloc_ctor(4, 1, 0);
} else {
 x_561 = x_493;
 lean_ctor_set_tag(x_561, 4);
}
lean_ctor_set(x_561, 0, x_560);
x_562 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_561);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_2);
x_565 = l_Lean_Json_mkObj(x_564);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_475);
lean_ctor_set(x_566, 1, x_565);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_3);
x_2 = x_471;
x_3 = x_567;
goto _start;
}
}
}
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; size_t x_578; size_t x_579; lean_object* x_580; size_t x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_569 = lean_ctor_get(x_2, 0);
x_570 = lean_ctor_get(x_2, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_2);
x_571 = lean_ctor_get(x_569, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_569, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_573 = x_569;
} else {
 lean_dec_ref(x_569);
 x_573 = lean_box(0);
}
x_574 = l_Lean_Lsp_RefIdent_toJson(x_571);
x_575 = l_Lean_Json_compress(x_574);
x_576 = lean_ctor_get(x_572, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_572, 1);
lean_inc(x_577);
lean_dec(x_572);
x_578 = lean_array_size(x_577);
x_579 = 0;
x_580 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_578, x_579, x_577);
x_581 = lean_array_size(x_580);
x_582 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(x_579, x_581, x_579, x_580);
x_583 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_583, 0, x_582);
x_584 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
if (lean_is_scalar(x_573)) {
 x_585 = lean_alloc_ctor(0, 2, 0);
} else {
 x_585 = x_573;
}
lean_ctor_set(x_585, 0, x_584);
lean_ctor_set(x_585, 1, x_583);
lean_inc(x_1);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_1);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_587 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_586);
x_589 = l_Lean_Json_mkObj(x_588);
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_575);
lean_ctor_set(x_590, 1, x_589);
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_3);
x_2 = x_570;
x_3 = x_591;
goto _start;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_593 = lean_ctor_get(x_576, 0);
lean_inc(x_593);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 x_594 = x_576;
} else {
 lean_dec_ref(x_576);
 x_594 = lean_box(0);
}
x_595 = lean_ctor_get(x_593, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
x_598 = lean_ctor_get(x_596, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_596, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_600 = x_596;
} else {
 lean_dec_ref(x_596);
 x_600 = lean_box(0);
}
x_601 = lean_ctor_get(x_597, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_597, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 x_603 = x_597;
} else {
 lean_dec_ref(x_597);
 x_603 = lean_box(0);
}
x_604 = lean_box(0);
if (lean_is_scalar(x_603)) {
 x_605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_605 = x_603;
 lean_ctor_set_tag(x_605, 1);
}
lean_ctor_set(x_605, 0, x_602);
lean_ctor_set(x_605, 1, x_604);
if (lean_is_scalar(x_600)) {
 x_606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_606 = x_600;
 lean_ctor_set_tag(x_606, 1);
}
lean_ctor_set(x_606, 0, x_601);
lean_ctor_set(x_606, 1, x_605);
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_599);
lean_ctor_set(x_607, 1, x_606);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_598);
lean_ctor_set(x_608, 1, x_607);
x_609 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_608, x_604);
x_610 = lean_ctor_get(x_593, 1);
lean_inc(x_610);
lean_dec(x_593);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; size_t x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_611 = l_List_appendTR___rarg(x_609, x_604);
x_612 = lean_array_mk(x_611);
x_613 = lean_array_size(x_612);
x_614 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_613, x_579, x_612);
if (lean_is_scalar(x_594)) {
 x_615 = lean_alloc_ctor(4, 1, 0);
} else {
 x_615 = x_594;
 lean_ctor_set_tag(x_615, 4);
}
lean_ctor_set(x_615, 0, x_614);
x_616 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_617 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_615);
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_586);
x_619 = l_Lean_Json_mkObj(x_618);
x_620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_620, 0, x_575);
lean_ctor_set(x_620, 1, x_619);
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_3);
x_2 = x_570;
x_3 = x_621;
goto _start;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; size_t x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_623 = lean_ctor_get(x_610, 0);
lean_inc(x_623);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_624 = x_610;
} else {
 lean_dec_ref(x_610);
 x_624 = lean_box(0);
}
x_625 = lean_ctor_get(x_623, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_623, 1);
lean_inc(x_626);
x_627 = lean_ctor_get(x_623, 2);
lean_inc(x_627);
lean_dec(x_623);
if (lean_is_scalar(x_624)) {
 x_628 = lean_alloc_ctor(3, 1, 0);
} else {
 x_628 = x_624;
 lean_ctor_set_tag(x_628, 3);
}
lean_ctor_set(x_628, 0, x_625);
x_629 = lean_ctor_get(x_626, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_626, 1);
lean_inc(x_630);
lean_dec(x_626);
x_631 = lean_ctor_get(x_629, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_629, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 x_633 = x_629;
} else {
 lean_dec_ref(x_629);
 x_633 = lean_box(0);
}
x_634 = lean_ctor_get(x_630, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_630, 1);
lean_inc(x_635);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 lean_ctor_release(x_630, 1);
 x_636 = x_630;
} else {
 lean_dec_ref(x_630);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(1, 2, 0);
} else {
 x_637 = x_636;
 lean_ctor_set_tag(x_637, 1);
}
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_604);
if (lean_is_scalar(x_633)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_633;
 lean_ctor_set_tag(x_638, 1);
}
lean_ctor_set(x_638, 0, x_634);
lean_ctor_set(x_638, 1, x_637);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_632);
lean_ctor_set(x_639, 1, x_638);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_631);
lean_ctor_set(x_640, 1, x_639);
x_641 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_640, x_604);
x_642 = lean_ctor_get(x_627, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_627, 1);
lean_inc(x_643);
lean_dec(x_627);
x_644 = lean_ctor_get(x_642, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_642, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 x_646 = x_642;
} else {
 lean_dec_ref(x_642);
 x_646 = lean_box(0);
}
x_647 = lean_ctor_get(x_643, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_643, 1);
lean_inc(x_648);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_649 = x_643;
} else {
 lean_dec_ref(x_643);
 x_649 = lean_box(0);
}
if (lean_is_scalar(x_649)) {
 x_650 = lean_alloc_ctor(1, 2, 0);
} else {
 x_650 = x_649;
 lean_ctor_set_tag(x_650, 1);
}
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_604);
if (lean_is_scalar(x_646)) {
 x_651 = lean_alloc_ctor(1, 2, 0);
} else {
 x_651 = x_646;
 lean_ctor_set_tag(x_651, 1);
}
lean_ctor_set(x_651, 0, x_647);
lean_ctor_set(x_651, 1, x_650);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_645);
lean_ctor_set(x_652, 1, x_651);
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_644);
lean_ctor_set(x_653, 1, x_652);
x_654 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_653, x_604);
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_628);
lean_ctor_set(x_655, 1, x_604);
x_656 = l_List_appendTR___rarg(x_655, x_641);
x_657 = l_List_appendTR___rarg(x_656, x_654);
x_658 = l_List_appendTR___rarg(x_609, x_657);
x_659 = lean_array_mk(x_658);
x_660 = lean_array_size(x_659);
x_661 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_660, x_579, x_659);
if (lean_is_scalar(x_594)) {
 x_662 = lean_alloc_ctor(4, 1, 0);
} else {
 x_662 = x_594;
 lean_ctor_set_tag(x_662, 4);
}
lean_ctor_set(x_662, 0, x_661);
x_663 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_664 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_662);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_586);
x_666 = l_Lean_Json_mkObj(x_665);
x_667 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_667, 0, x_575);
lean_ctor_set(x_667, 1, x_666);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_3);
x_2 = x_570;
x_3 = x_668;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Lean_Lsp_RefIdent_toJson(x_9);
x_12 = l_Lean_Json_compress(x_11);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_array_size(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_15, x_16, x_14);
x_18 = lean_array_size(x_17);
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(x_16, x_18, x_16, x_17);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_6, 0, x_21);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_24 = l_Lean_Json_mkObj(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
x_2 = x_8;
x_3 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
x_39 = lean_box(0);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_39);
lean_ctor_set(x_32, 0, x_38);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_32);
lean_ctor_set(x_31, 0, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_41, x_39);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = l_List_appendTR___rarg(x_42, x_39);
x_45 = lean_array_mk(x_44);
x_46 = lean_array_size(x_45);
x_47 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_46, x_16, x_45);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_47);
x_48 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_13);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_2);
x_51 = l_Lean_Json_mkObj(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
x_2 = x_8;
x_3 = x_53;
goto _start;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_43);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_43, 0);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 2);
lean_inc(x_59);
lean_dec(x_56);
lean_ctor_set_tag(x_43, 3);
lean_ctor_set(x_43, 0, x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 1, x_39);
lean_ctor_set(x_61, 0, x_67);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 1, x_61);
lean_ctor_set(x_60, 0, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_60);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_69, x_39);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
lean_dec(x_59);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_ctor_get(x_71, 1);
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_ctor_get(x_72, 1);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_39);
lean_ctor_set(x_72, 0, x_78);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_72);
lean_ctor_set(x_71, 0, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_71);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_80, x_39);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_43);
lean_ctor_set(x_82, 1, x_39);
x_83 = l_List_appendTR___rarg(x_82, x_70);
x_84 = l_List_appendTR___rarg(x_83, x_81);
x_85 = l_List_appendTR___rarg(x_42, x_84);
x_86 = lean_array_mk(x_85);
x_87 = lean_array_size(x_86);
x_88 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_87, x_16, x_86);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_88);
x_89 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_13);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_2);
x_92 = l_Lean_Json_mkObj(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_12);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_3);
x_2 = x_8;
x_3 = x_94;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_96 = lean_ctor_get(x_71, 0);
x_97 = lean_ctor_get(x_71, 1);
x_98 = lean_ctor_get(x_72, 0);
x_99 = lean_ctor_get(x_72, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_72);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_39);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_100);
lean_ctor_set(x_71, 0, x_98);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_71);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_102, x_39);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_43);
lean_ctor_set(x_104, 1, x_39);
x_105 = l_List_appendTR___rarg(x_104, x_70);
x_106 = l_List_appendTR___rarg(x_105, x_103);
x_107 = l_List_appendTR___rarg(x_42, x_106);
x_108 = lean_array_mk(x_107);
x_109 = lean_array_size(x_108);
x_110 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_109, x_16, x_108);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_110);
x_111 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_13);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_2);
x_114 = l_Lean_Json_mkObj(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_12);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_3);
x_2 = x_8;
x_3 = x_116;
goto _start;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; size_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_118 = lean_ctor_get(x_71, 0);
x_119 = lean_ctor_get(x_71, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_71);
x_120 = lean_ctor_get(x_72, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_72, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_122 = x_72;
} else {
 lean_dec_ref(x_72);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
 lean_ctor_set_tag(x_123, 1);
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_39);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_118);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_126, x_39);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_43);
lean_ctor_set(x_128, 1, x_39);
x_129 = l_List_appendTR___rarg(x_128, x_70);
x_130 = l_List_appendTR___rarg(x_129, x_127);
x_131 = l_List_appendTR___rarg(x_42, x_130);
x_132 = lean_array_mk(x_131);
x_133 = lean_array_size(x_132);
x_134 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_133, x_16, x_132);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_134);
x_135 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_13);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_2);
x_138 = l_Lean_Json_mkObj(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_12);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_3);
x_2 = x_8;
x_3 = x_140;
goto _start;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; size_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_142 = lean_ctor_get(x_60, 0);
x_143 = lean_ctor_get(x_60, 1);
x_144 = lean_ctor_get(x_61, 0);
x_145 = lean_ctor_get(x_61, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_61);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_39);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 1, x_146);
lean_ctor_set(x_60, 0, x_144);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_60);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_148, x_39);
x_150 = lean_ctor_get(x_59, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_59, 1);
lean_inc(x_151);
lean_dec(x_59);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_154 = x_150;
} else {
 lean_dec_ref(x_150);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_157 = x_151;
} else {
 lean_dec_ref(x_151);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
 lean_ctor_set_tag(x_158, 1);
}
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_39);
if (lean_is_scalar(x_154)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_154;
 lean_ctor_set_tag(x_159, 1);
}
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_153);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_152);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_161, x_39);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_43);
lean_ctor_set(x_163, 1, x_39);
x_164 = l_List_appendTR___rarg(x_163, x_149);
x_165 = l_List_appendTR___rarg(x_164, x_162);
x_166 = l_List_appendTR___rarg(x_42, x_165);
x_167 = lean_array_mk(x_166);
x_168 = lean_array_size(x_167);
x_169 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_168, x_16, x_167);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_169);
x_170 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_13);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_2);
x_173 = l_Lean_Json_mkObj(x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_12);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_3);
x_2 = x_8;
x_3 = x_175;
goto _start;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; size_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_177 = lean_ctor_get(x_60, 0);
x_178 = lean_ctor_get(x_60, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_60);
x_179 = lean_ctor_get(x_61, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_61, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_181 = x_61;
} else {
 lean_dec_ref(x_61);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
 lean_ctor_set_tag(x_182, 1);
}
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_39);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_177);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_185, x_39);
x_187 = lean_ctor_get(x_59, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_59, 1);
lean_inc(x_188);
lean_dec(x_59);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_194 = x_188;
} else {
 lean_dec_ref(x_188);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
 lean_ctor_set_tag(x_195, 1);
}
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_39);
if (lean_is_scalar(x_191)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_191;
 lean_ctor_set_tag(x_196, 1);
}
lean_ctor_set(x_196, 0, x_192);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_190);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_198, x_39);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_43);
lean_ctor_set(x_200, 1, x_39);
x_201 = l_List_appendTR___rarg(x_200, x_186);
x_202 = l_List_appendTR___rarg(x_201, x_199);
x_203 = l_List_appendTR___rarg(x_42, x_202);
x_204 = lean_array_mk(x_203);
x_205 = lean_array_size(x_204);
x_206 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_205, x_16, x_204);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_206);
x_207 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_13);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_2);
x_210 = l_Lean_Json_mkObj(x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_12);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_3);
x_2 = x_8;
x_3 = x_212;
goto _start;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; size_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_214 = lean_ctor_get(x_43, 0);
lean_inc(x_214);
lean_dec(x_43);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 2);
lean_inc(x_217);
lean_dec(x_214);
x_218 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_218, 0, x_215);
x_219 = lean_ctor_get(x_216, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_216, 1);
lean_inc(x_220);
lean_dec(x_216);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_223 = x_219;
} else {
 lean_dec_ref(x_219);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_220, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_220, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_226 = x_220;
} else {
 lean_dec_ref(x_220);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
 lean_ctor_set_tag(x_227, 1);
}
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_39);
if (lean_is_scalar(x_223)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_223;
 lean_ctor_set_tag(x_228, 1);
}
lean_ctor_set(x_228, 0, x_224);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_222);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_221);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_230, x_39);
x_232 = lean_ctor_get(x_217, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_217, 1);
lean_inc(x_233);
lean_dec(x_217);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_236 = x_232;
} else {
 lean_dec_ref(x_232);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_239 = x_233;
} else {
 lean_dec_ref(x_233);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
 lean_ctor_set_tag(x_240, 1);
}
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_39);
if (lean_is_scalar(x_236)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_236;
 lean_ctor_set_tag(x_241, 1);
}
lean_ctor_set(x_241, 0, x_237);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_235);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_234);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_243, x_39);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_218);
lean_ctor_set(x_245, 1, x_39);
x_246 = l_List_appendTR___rarg(x_245, x_231);
x_247 = l_List_appendTR___rarg(x_246, x_244);
x_248 = l_List_appendTR___rarg(x_42, x_247);
x_249 = lean_array_mk(x_248);
x_250 = lean_array_size(x_249);
x_251 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_250, x_16, x_249);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_251);
x_252 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_13);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_2);
x_255 = l_Lean_Json_mkObj(x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_12);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_3);
x_2 = x_8;
x_3 = x_257;
goto _start;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_259 = lean_ctor_get(x_31, 0);
x_260 = lean_ctor_get(x_31, 1);
x_261 = lean_ctor_get(x_32, 0);
x_262 = lean_ctor_get(x_32, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_32);
x_263 = lean_box(0);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_264);
lean_ctor_set(x_31, 0, x_261);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_260);
lean_ctor_set(x_265, 1, x_31);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_259);
lean_ctor_set(x_266, 1, x_265);
x_267 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_266, x_263);
x_268 = lean_ctor_get(x_29, 1);
lean_inc(x_268);
lean_dec(x_29);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; size_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_269 = l_List_appendTR___rarg(x_267, x_263);
x_270 = lean_array_mk(x_269);
x_271 = lean_array_size(x_270);
x_272 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_271, x_16, x_270);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_272);
x_273 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_13);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_2);
x_276 = l_Lean_Json_mkObj(x_275);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_12);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_3);
x_2 = x_8;
x_3 = x_278;
goto _start;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; size_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_280 = lean_ctor_get(x_268, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_281 = x_268;
} else {
 lean_dec_ref(x_268);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_280, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_280, 2);
lean_inc(x_284);
lean_dec(x_280);
if (lean_is_scalar(x_281)) {
 x_285 = lean_alloc_ctor(3, 1, 0);
} else {
 x_285 = x_281;
 lean_ctor_set_tag(x_285, 3);
}
lean_ctor_set(x_285, 0, x_282);
x_286 = lean_ctor_get(x_283, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
lean_dec(x_283);
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_290 = x_286;
} else {
 lean_dec_ref(x_286);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_287, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_287, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_293 = x_287;
} else {
 lean_dec_ref(x_287);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
 lean_ctor_set_tag(x_294, 1);
}
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_263);
if (lean_is_scalar(x_290)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_290;
 lean_ctor_set_tag(x_295, 1);
}
lean_ctor_set(x_295, 0, x_291);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_289);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_288);
lean_ctor_set(x_297, 1, x_296);
x_298 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_297, x_263);
x_299 = lean_ctor_get(x_284, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_284, 1);
lean_inc(x_300);
lean_dec(x_284);
x_301 = lean_ctor_get(x_299, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_303 = x_299;
} else {
 lean_dec_ref(x_299);
 x_303 = lean_box(0);
}
x_304 = lean_ctor_get(x_300, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_300, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_306 = x_300;
} else {
 lean_dec_ref(x_300);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
 lean_ctor_set_tag(x_307, 1);
}
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_263);
if (lean_is_scalar(x_303)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_303;
 lean_ctor_set_tag(x_308, 1);
}
lean_ctor_set(x_308, 0, x_304);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_302);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_301);
lean_ctor_set(x_310, 1, x_309);
x_311 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_310, x_263);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_285);
lean_ctor_set(x_312, 1, x_263);
x_313 = l_List_appendTR___rarg(x_312, x_298);
x_314 = l_List_appendTR___rarg(x_313, x_311);
x_315 = l_List_appendTR___rarg(x_267, x_314);
x_316 = lean_array_mk(x_315);
x_317 = lean_array_size(x_316);
x_318 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_317, x_16, x_316);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_318);
x_319 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_13);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_2);
x_322 = l_Lean_Json_mkObj(x_321);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_12);
lean_ctor_set(x_323, 1, x_322);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_3);
x_2 = x_8;
x_3 = x_324;
goto _start;
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_326 = lean_ctor_get(x_31, 0);
x_327 = lean_ctor_get(x_31, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_31);
x_328 = lean_ctor_get(x_32, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_32, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_330 = x_32;
} else {
 lean_dec_ref(x_32);
 x_330 = lean_box(0);
}
x_331 = lean_box(0);
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_330;
 lean_ctor_set_tag(x_332, 1);
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_328);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_327);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_326);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_335, x_331);
x_337 = lean_ctor_get(x_29, 1);
lean_inc(x_337);
lean_dec(x_29);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; size_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_338 = l_List_appendTR___rarg(x_336, x_331);
x_339 = lean_array_mk(x_338);
x_340 = lean_array_size(x_339);
x_341 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_340, x_16, x_339);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_341);
x_342 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_13);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_2);
x_345 = l_Lean_Json_mkObj(x_344);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_12);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_3);
x_2 = x_8;
x_3 = x_347;
goto _start;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; size_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_349 = lean_ctor_get(x_337, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_350 = x_337;
} else {
 lean_dec_ref(x_337);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_349, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 2);
lean_inc(x_353);
lean_dec(x_349);
if (lean_is_scalar(x_350)) {
 x_354 = lean_alloc_ctor(3, 1, 0);
} else {
 x_354 = x_350;
 lean_ctor_set_tag(x_354, 3);
}
lean_ctor_set(x_354, 0, x_351);
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
lean_dec(x_352);
x_357 = lean_ctor_get(x_355, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_355, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_359 = x_355;
} else {
 lean_dec_ref(x_355);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_356, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_356, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_362 = x_356;
} else {
 lean_dec_ref(x_356);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
 lean_ctor_set_tag(x_363, 1);
}
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_331);
if (lean_is_scalar(x_359)) {
 x_364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_364 = x_359;
 lean_ctor_set_tag(x_364, 1);
}
lean_ctor_set(x_364, 0, x_360);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_358);
lean_ctor_set(x_365, 1, x_364);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_357);
lean_ctor_set(x_366, 1, x_365);
x_367 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_366, x_331);
x_368 = lean_ctor_get(x_353, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_353, 1);
lean_inc(x_369);
lean_dec(x_353);
x_370 = lean_ctor_get(x_368, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_372 = x_368;
} else {
 lean_dec_ref(x_368);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_369, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_369, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_375 = x_369;
} else {
 lean_dec_ref(x_369);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_375;
 lean_ctor_set_tag(x_376, 1);
}
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_331);
if (lean_is_scalar(x_372)) {
 x_377 = lean_alloc_ctor(1, 2, 0);
} else {
 x_377 = x_372;
 lean_ctor_set_tag(x_377, 1);
}
lean_ctor_set(x_377, 0, x_373);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_371);
lean_ctor_set(x_378, 1, x_377);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_370);
lean_ctor_set(x_379, 1, x_378);
x_380 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_379, x_331);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_354);
lean_ctor_set(x_381, 1, x_331);
x_382 = l_List_appendTR___rarg(x_381, x_367);
x_383 = l_List_appendTR___rarg(x_382, x_380);
x_384 = l_List_appendTR___rarg(x_336, x_383);
x_385 = lean_array_mk(x_384);
x_386 = lean_array_size(x_385);
x_387 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_386, x_16, x_385);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 0, x_387);
x_388 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_13);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_2);
x_391 = l_Lean_Json_mkObj(x_390);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_12);
lean_ctor_set(x_392, 1, x_391);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_3);
x_2 = x_8;
x_3 = x_393;
goto _start;
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_395 = lean_ctor_get(x_13, 0);
lean_inc(x_395);
lean_dec(x_13);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_397, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_401 = x_397;
} else {
 lean_dec_ref(x_397);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_398, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_398, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_404 = x_398;
} else {
 lean_dec_ref(x_398);
 x_404 = lean_box(0);
}
x_405 = lean_box(0);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_404;
 lean_ctor_set_tag(x_406, 1);
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_405);
if (lean_is_scalar(x_401)) {
 x_407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_407 = x_401;
 lean_ctor_set_tag(x_407, 1);
}
lean_ctor_set(x_407, 0, x_402);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_400);
lean_ctor_set(x_408, 1, x_407);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_399);
lean_ctor_set(x_409, 1, x_408);
x_410 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_409, x_405);
x_411 = lean_ctor_get(x_395, 1);
lean_inc(x_411);
lean_dec(x_395);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; size_t x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_412 = l_List_appendTR___rarg(x_410, x_405);
x_413 = lean_array_mk(x_412);
x_414 = lean_array_size(x_413);
x_415 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_414, x_16, x_413);
x_416 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_416, 0, x_415);
x_417 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_416);
x_419 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_2);
x_420 = l_Lean_Json_mkObj(x_419);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_12);
lean_ctor_set(x_421, 1, x_420);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_3);
x_2 = x_8;
x_3 = x_422;
goto _start;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; size_t x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_424 = lean_ctor_get(x_411, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 x_425 = x_411;
} else {
 lean_dec_ref(x_411);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_424, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_424, 2);
lean_inc(x_428);
lean_dec(x_424);
if (lean_is_scalar(x_425)) {
 x_429 = lean_alloc_ctor(3, 1, 0);
} else {
 x_429 = x_425;
 lean_ctor_set_tag(x_429, 3);
}
lean_ctor_set(x_429, 0, x_426);
x_430 = lean_ctor_get(x_427, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_427, 1);
lean_inc(x_431);
lean_dec(x_427);
x_432 = lean_ctor_get(x_430, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_430, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_434 = x_430;
} else {
 lean_dec_ref(x_430);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_431, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_431, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_437 = x_431;
} else {
 lean_dec_ref(x_431);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_438 = x_437;
 lean_ctor_set_tag(x_438, 1);
}
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_405);
if (lean_is_scalar(x_434)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_434;
 lean_ctor_set_tag(x_439, 1);
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_438);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_433);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_432);
lean_ctor_set(x_441, 1, x_440);
x_442 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_441, x_405);
x_443 = lean_ctor_get(x_428, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_428, 1);
lean_inc(x_444);
lean_dec(x_428);
x_445 = lean_ctor_get(x_443, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_443, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_447 = x_443;
} else {
 lean_dec_ref(x_443);
 x_447 = lean_box(0);
}
x_448 = lean_ctor_get(x_444, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_444, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_450 = x_444;
} else {
 lean_dec_ref(x_444);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_450;
 lean_ctor_set_tag(x_451, 1);
}
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_405);
if (lean_is_scalar(x_447)) {
 x_452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_452 = x_447;
 lean_ctor_set_tag(x_452, 1);
}
lean_ctor_set(x_452, 0, x_448);
lean_ctor_set(x_452, 1, x_451);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_446);
lean_ctor_set(x_453, 1, x_452);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_445);
lean_ctor_set(x_454, 1, x_453);
x_455 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_454, x_405);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_429);
lean_ctor_set(x_456, 1, x_405);
x_457 = l_List_appendTR___rarg(x_456, x_442);
x_458 = l_List_appendTR___rarg(x_457, x_455);
x_459 = l_List_appendTR___rarg(x_410, x_458);
x_460 = lean_array_mk(x_459);
x_461 = lean_array_size(x_460);
x_462 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_461, x_16, x_460);
x_463 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_464 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_463);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_2);
x_467 = l_Lean_Json_mkObj(x_466);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_12);
lean_ctor_set(x_468, 1, x_467);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_3);
x_2 = x_8;
x_3 = x_469;
goto _start;
}
}
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; size_t x_478; size_t x_479; lean_object* x_480; size_t x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_471 = lean_ctor_get(x_2, 1);
x_472 = lean_ctor_get(x_6, 0);
x_473 = lean_ctor_get(x_6, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_6);
x_474 = l_Lean_Lsp_RefIdent_toJson(x_472);
x_475 = l_Lean_Json_compress(x_474);
x_476 = lean_ctor_get(x_473, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_473, 1);
lean_inc(x_477);
lean_dec(x_473);
x_478 = lean_array_size(x_477);
x_479 = 0;
x_480 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_478, x_479, x_477);
x_481 = lean_array_size(x_480);
x_482 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(x_479, x_481, x_479, x_480);
x_483 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_483, 0, x_482);
x_484 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_483);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_485);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_486 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_2);
x_488 = l_Lean_Json_mkObj(x_487);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_475);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_3);
x_2 = x_471;
x_3 = x_490;
goto _start;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_492 = lean_ctor_get(x_476, 0);
lean_inc(x_492);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_493 = x_476;
} else {
 lean_dec_ref(x_476);
 x_493 = lean_box(0);
}
x_494 = lean_ctor_get(x_492, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_499 = x_495;
} else {
 lean_dec_ref(x_495);
 x_499 = lean_box(0);
}
x_500 = lean_ctor_get(x_496, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_496, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_502 = x_496;
} else {
 lean_dec_ref(x_496);
 x_502 = lean_box(0);
}
x_503 = lean_box(0);
if (lean_is_scalar(x_502)) {
 x_504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_504 = x_502;
 lean_ctor_set_tag(x_504, 1);
}
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_503);
if (lean_is_scalar(x_499)) {
 x_505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_505 = x_499;
 lean_ctor_set_tag(x_505, 1);
}
lean_ctor_set(x_505, 0, x_500);
lean_ctor_set(x_505, 1, x_504);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_498);
lean_ctor_set(x_506, 1, x_505);
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_497);
lean_ctor_set(x_507, 1, x_506);
x_508 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_507, x_503);
x_509 = lean_ctor_get(x_492, 1);
lean_inc(x_509);
lean_dec(x_492);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; size_t x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_510 = l_List_appendTR___rarg(x_508, x_503);
x_511 = lean_array_mk(x_510);
x_512 = lean_array_size(x_511);
x_513 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_512, x_479, x_511);
if (lean_is_scalar(x_493)) {
 x_514 = lean_alloc_ctor(4, 1, 0);
} else {
 x_514 = x_493;
 lean_ctor_set_tag(x_514, 4);
}
lean_ctor_set(x_514, 0, x_513);
x_515 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_514);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_2);
x_518 = l_Lean_Json_mkObj(x_517);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_475);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_3);
x_2 = x_471;
x_3 = x_520;
goto _start;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; size_t x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_522 = lean_ctor_get(x_509, 0);
lean_inc(x_522);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 x_523 = x_509;
} else {
 lean_dec_ref(x_509);
 x_523 = lean_box(0);
}
x_524 = lean_ctor_get(x_522, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_525);
x_526 = lean_ctor_get(x_522, 2);
lean_inc(x_526);
lean_dec(x_522);
if (lean_is_scalar(x_523)) {
 x_527 = lean_alloc_ctor(3, 1, 0);
} else {
 x_527 = x_523;
 lean_ctor_set_tag(x_527, 3);
}
lean_ctor_set(x_527, 0, x_524);
x_528 = lean_ctor_get(x_525, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_525, 1);
lean_inc(x_529);
lean_dec(x_525);
x_530 = lean_ctor_get(x_528, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_528, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_532 = x_528;
} else {
 lean_dec_ref(x_528);
 x_532 = lean_box(0);
}
x_533 = lean_ctor_get(x_529, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_529, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_535 = x_529;
} else {
 lean_dec_ref(x_529);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 2, 0);
} else {
 x_536 = x_535;
 lean_ctor_set_tag(x_536, 1);
}
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_503);
if (lean_is_scalar(x_532)) {
 x_537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_537 = x_532;
 lean_ctor_set_tag(x_537, 1);
}
lean_ctor_set(x_537, 0, x_533);
lean_ctor_set(x_537, 1, x_536);
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_531);
lean_ctor_set(x_538, 1, x_537);
x_539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_539, 0, x_530);
lean_ctor_set(x_539, 1, x_538);
x_540 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_539, x_503);
x_541 = lean_ctor_get(x_526, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_526, 1);
lean_inc(x_542);
lean_dec(x_526);
x_543 = lean_ctor_get(x_541, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_545 = x_541;
} else {
 lean_dec_ref(x_541);
 x_545 = lean_box(0);
}
x_546 = lean_ctor_get(x_542, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_542, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 x_548 = x_542;
} else {
 lean_dec_ref(x_542);
 x_548 = lean_box(0);
}
if (lean_is_scalar(x_548)) {
 x_549 = lean_alloc_ctor(1, 2, 0);
} else {
 x_549 = x_548;
 lean_ctor_set_tag(x_549, 1);
}
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_503);
if (lean_is_scalar(x_545)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_545;
 lean_ctor_set_tag(x_550, 1);
}
lean_ctor_set(x_550, 0, x_546);
lean_ctor_set(x_550, 1, x_549);
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_544);
lean_ctor_set(x_551, 1, x_550);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_543);
lean_ctor_set(x_552, 1, x_551);
x_553 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_552, x_503);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_527);
lean_ctor_set(x_554, 1, x_503);
x_555 = l_List_appendTR___rarg(x_554, x_540);
x_556 = l_List_appendTR___rarg(x_555, x_553);
x_557 = l_List_appendTR___rarg(x_508, x_556);
x_558 = lean_array_mk(x_557);
x_559 = lean_array_size(x_558);
x_560 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_559, x_479, x_558);
if (lean_is_scalar(x_493)) {
 x_561 = lean_alloc_ctor(4, 1, 0);
} else {
 x_561 = x_493;
 lean_ctor_set_tag(x_561, 4);
}
lean_ctor_set(x_561, 0, x_560);
x_562 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_561);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_2);
x_565 = l_Lean_Json_mkObj(x_564);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_475);
lean_ctor_set(x_566, 1, x_565);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_3);
x_2 = x_471;
x_3 = x_567;
goto _start;
}
}
}
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; size_t x_578; size_t x_579; lean_object* x_580; size_t x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_569 = lean_ctor_get(x_2, 0);
x_570 = lean_ctor_get(x_2, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_2);
x_571 = lean_ctor_get(x_569, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_569, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_573 = x_569;
} else {
 lean_dec_ref(x_569);
 x_573 = lean_box(0);
}
x_574 = l_Lean_Lsp_RefIdent_toJson(x_571);
x_575 = l_Lean_Json_compress(x_574);
x_576 = lean_ctor_get(x_572, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_572, 1);
lean_inc(x_577);
lean_dec(x_572);
x_578 = lean_array_size(x_577);
x_579 = 0;
x_580 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instToJsonRefInfo___spec__2(x_578, x_579, x_577);
x_581 = lean_array_size(x_580);
x_582 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(x_579, x_581, x_579, x_580);
x_583 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_583, 0, x_582);
x_584 = l_Lean_Lsp_instToJsonRefInfo___closed__1;
if (lean_is_scalar(x_573)) {
 x_585 = lean_alloc_ctor(0, 2, 0);
} else {
 x_585 = x_573;
}
lean_ctor_set(x_585, 0, x_584);
lean_ctor_set(x_585, 1, x_583);
lean_inc(x_1);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_1);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_587 = l_Lean_Lsp_instToJsonRefInfo___closed__3;
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_586);
x_589 = l_Lean_Json_mkObj(x_588);
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_575);
lean_ctor_set(x_590, 1, x_589);
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_3);
x_2 = x_570;
x_3 = x_591;
goto _start;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_593 = lean_ctor_get(x_576, 0);
lean_inc(x_593);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 x_594 = x_576;
} else {
 lean_dec_ref(x_576);
 x_594 = lean_box(0);
}
x_595 = lean_ctor_get(x_593, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
x_598 = lean_ctor_get(x_596, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_596, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_600 = x_596;
} else {
 lean_dec_ref(x_596);
 x_600 = lean_box(0);
}
x_601 = lean_ctor_get(x_597, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_597, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 x_603 = x_597;
} else {
 lean_dec_ref(x_597);
 x_603 = lean_box(0);
}
x_604 = lean_box(0);
if (lean_is_scalar(x_603)) {
 x_605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_605 = x_603;
 lean_ctor_set_tag(x_605, 1);
}
lean_ctor_set(x_605, 0, x_602);
lean_ctor_set(x_605, 1, x_604);
if (lean_is_scalar(x_600)) {
 x_606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_606 = x_600;
 lean_ctor_set_tag(x_606, 1);
}
lean_ctor_set(x_606, 0, x_601);
lean_ctor_set(x_606, 1, x_605);
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_599);
lean_ctor_set(x_607, 1, x_606);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_598);
lean_ctor_set(x_608, 1, x_607);
x_609 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_608, x_604);
x_610 = lean_ctor_get(x_593, 1);
lean_inc(x_610);
lean_dec(x_593);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; size_t x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_611 = l_List_appendTR___rarg(x_609, x_604);
x_612 = lean_array_mk(x_611);
x_613 = lean_array_size(x_612);
x_614 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_613, x_579, x_612);
if (lean_is_scalar(x_594)) {
 x_615 = lean_alloc_ctor(4, 1, 0);
} else {
 x_615 = x_594;
 lean_ctor_set_tag(x_615, 4);
}
lean_ctor_set(x_615, 0, x_614);
x_616 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_617 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_615);
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_586);
x_619 = l_Lean_Json_mkObj(x_618);
x_620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_620, 0, x_575);
lean_ctor_set(x_620, 1, x_619);
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_3);
x_2 = x_570;
x_3 = x_621;
goto _start;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; size_t x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_623 = lean_ctor_get(x_610, 0);
lean_inc(x_623);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_624 = x_610;
} else {
 lean_dec_ref(x_610);
 x_624 = lean_box(0);
}
x_625 = lean_ctor_get(x_623, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_623, 1);
lean_inc(x_626);
x_627 = lean_ctor_get(x_623, 2);
lean_inc(x_627);
lean_dec(x_623);
if (lean_is_scalar(x_624)) {
 x_628 = lean_alloc_ctor(3, 1, 0);
} else {
 x_628 = x_624;
 lean_ctor_set_tag(x_628, 3);
}
lean_ctor_set(x_628, 0, x_625);
x_629 = lean_ctor_get(x_626, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_626, 1);
lean_inc(x_630);
lean_dec(x_626);
x_631 = lean_ctor_get(x_629, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_629, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 x_633 = x_629;
} else {
 lean_dec_ref(x_629);
 x_633 = lean_box(0);
}
x_634 = lean_ctor_get(x_630, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_630, 1);
lean_inc(x_635);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 lean_ctor_release(x_630, 1);
 x_636 = x_630;
} else {
 lean_dec_ref(x_630);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(1, 2, 0);
} else {
 x_637 = x_636;
 lean_ctor_set_tag(x_637, 1);
}
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_604);
if (lean_is_scalar(x_633)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_633;
 lean_ctor_set_tag(x_638, 1);
}
lean_ctor_set(x_638, 0, x_634);
lean_ctor_set(x_638, 1, x_637);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_632);
lean_ctor_set(x_639, 1, x_638);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_631);
lean_ctor_set(x_640, 1, x_639);
x_641 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_640, x_604);
x_642 = lean_ctor_get(x_627, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_627, 1);
lean_inc(x_643);
lean_dec(x_627);
x_644 = lean_ctor_get(x_642, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_642, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 x_646 = x_642;
} else {
 lean_dec_ref(x_642);
 x_646 = lean_box(0);
}
x_647 = lean_ctor_get(x_643, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_643, 1);
lean_inc(x_648);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_649 = x_643;
} else {
 lean_dec_ref(x_643);
 x_649 = lean_box(0);
}
if (lean_is_scalar(x_649)) {
 x_650 = lean_alloc_ctor(1, 2, 0);
} else {
 x_650 = x_649;
 lean_ctor_set_tag(x_650, 1);
}
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_604);
if (lean_is_scalar(x_646)) {
 x_651 = lean_alloc_ctor(1, 2, 0);
} else {
 x_651 = x_646;
 lean_ctor_set_tag(x_651, 1);
}
lean_ctor_set(x_651, 0, x_647);
lean_ctor_set(x_651, 1, x_650);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_645);
lean_ctor_set(x_652, 1, x_651);
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_644);
lean_ctor_set(x_653, 1, x_652);
x_654 = l_List_mapTR_loop___at_Lean_Lsp_instToJsonRefInfo___spec__1(x_653, x_604);
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_628);
lean_ctor_set(x_655, 1, x_604);
x_656 = l_List_appendTR___rarg(x_655, x_641);
x_657 = l_List_appendTR___rarg(x_656, x_654);
x_658 = l_List_appendTR___rarg(x_609, x_657);
x_659 = lean_array_mk(x_658);
x_660 = lean_array_size(x_659);
x_661 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1627____spec__2(x_660, x_579, x_659);
if (lean_is_scalar(x_594)) {
 x_662 = lean_alloc_ctor(4, 1, 0);
} else {
 x_662 = x_594;
 lean_ctor_set_tag(x_662, 4);
}
lean_ctor_set(x_662, 0, x_661);
x_663 = l_Lean_Lsp_instToJsonRefInfo___closed__2;
x_664 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_662);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_586);
x_666 = l_Lean_Json_mkObj(x_665);
x_667 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_667, 0, x_575);
lean_ctor_set(x_667, 1, x_666);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_3);
x_2 = x_570;
x_3 = x_668;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_JsonNumber_fromNat(x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__1;
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
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__2(x_7, x_7, x_7);
x_15 = l_Lean_Json_mkObj(x_14);
x_16 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__15;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__4;
x_22 = l_List_flatMapTR_go___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_86____spec__1(x_20, x_21);
x_23 = l_Lean_Json_mkObj(x_22);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_11, x_11);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
lean_dec(x_10);
x_25 = l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__3(x_7, x_7, x_7);
x_26 = l_Lean_Json_mkObj(x_25);
x_27 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__15;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__4;
x_33 = l_List_flatMapTR_go___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_86____spec__1(x_31, x_32);
x_34 = l_Lean_Json_mkObj(x_33);
return x_34;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_37 = l_Array_foldlMUnsafe_fold___at_Lean_Lsp_instToJsonModuleRefs___spec__4(x_10, x_35, x_36, x_7);
lean_dec(x_10);
x_38 = l_List_mapTR_loop___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__4(x_7, x_37, x_7);
x_39 = l_Lean_Json_mkObj(x_38);
x_40 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__15;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_7);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_7);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_43);
x_45 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__4;
x_46 = l_List_flatMapTR_go___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_86____spec__1(x_44, x_45);
x_47 = l_Lean_Json_mkObj(x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020____spec__1(x_5, x_6, x_7, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2020_), 1, 0);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_9 = l_Lean_Json_getStr_x3f(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_3, x_4);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(80u);
x_12 = l_Lean_Json_pretty(x_3, x_11);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
case 4:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_array_size(x_18);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__2(x_19, x_20, x_18);
return x_21;
}
default: 
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(80u);
lean_inc(x_3);
x_23 = l_Lean_Json_pretty(x_3, x_22);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 0);
lean_dec(x_25);
x_26 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_27 = lean_string_append(x_26, x_23);
lean_dec(x_23);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_29 = lean_string_append(x_27, x_28);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
x_30 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1;
x_31 = lean_string_append(x_30, x_23);
lean_dec(x_23);
x_32 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("importClosure", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LeanImportClosureParams", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__2;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__3;
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__3;
x_2 = 1;
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__4;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__6;
x_2 = 1;
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__5;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__8;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__9;
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
x_9 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__9;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFromJsonLeanImportClosureParams___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2152____spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2152_(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2152____spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__4;
x_12 = l_List_flatMapTR_go___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_86____spec__1(x_10, x_11);
x_13 = l_Lean_Json_mkObj(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2152____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2152____spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanImportClosureParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2152_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanImportClosureParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToJsonLeanImportClosureParams___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("staleDependency", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LeanStaleDependencyParams", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__2;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__3;
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__3;
x_2 = 1;
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__4;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__6;
x_2 = 1;
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__5;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__8;
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_1132____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__9;
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
x_9 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__9;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFromJsonLeanStaleDependencyParams___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2269_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__4;
x_9 = l_List_flatMapTR_go___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_86____spec__1(x_7, x_8);
x_10 = l_Lean_Json_mkObj(x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanStaleDependencyParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2269_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanStaleDependencyParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToJsonLeanStaleDependencyParams___closed__1;
return x_1;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Internal(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Basic(builtin, lean_io_mk_world());
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
l_Lean_Lsp_instInhabitedRefIdent___closed__2 = _init_l_Lean_Lsp_instInhabitedRefIdent___closed__2();
lean_mark_persistent(l_Lean_Lsp_instInhabitedRefIdent___closed__2);
l_Lean_Lsp_instInhabitedRefIdent = _init_l_Lean_Lsp_instInhabitedRefIdent();
lean_mark_persistent(l_Lean_Lsp_instInhabitedRefIdent);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__1 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__1);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__2 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__1___closed__2);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__1 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__1);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__2 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__2);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__3 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__3);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____lambda__2___closed__4);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__1 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__1);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__2 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__2);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__3 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__3);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__4 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__4();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__4);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__5 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__5();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__5);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__6 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__6();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__6);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__7 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__7();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__7);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__8 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__8();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__8);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__9 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__9();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefIdent_fromJsonRefIdentJsonRepr____x40_Lean_Data_Lsp_Internal___hyg_268____closed__9);
l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr___closed__1 = _init_l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr___closed__1();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr___closed__1);
l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr = _init_l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr);
l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr___closed__1 = _init_l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr___closed__1();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr___closed__1);
l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr = _init_l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr);
l_Lean_Lsp_RefIdent_instFromJson___closed__1 = _init_l_Lean_Lsp_RefIdent_instFromJson___closed__1();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instFromJson___closed__1);
l_Lean_Lsp_RefIdent_instFromJson = _init_l_Lean_Lsp_RefIdent_instFromJson();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instFromJson);
l_Lean_Lsp_RefIdent_instToJson___closed__1 = _init_l_Lean_Lsp_RefIdent_instToJson___closed__1();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instToJson___closed__1);
l_Lean_Lsp_RefIdent_instToJson = _init_l_Lean_Lsp_RefIdent_instToJson();
lean_mark_persistent(l_Lean_Lsp_RefIdent_instToJson);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__1 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__1);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__2 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__2);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__3 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__3);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__4 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__4();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_RefInfo_toJsonParentDecl____x40_Lean_Data_Lsp_Internal___hyg_721____closed__4);
l_Lean_Lsp_RefInfo_instToJsonParentDecl___closed__1 = _init_l_Lean_Lsp_RefInfo_instToJsonParentDecl___closed__1();
lean_mark_persistent(l_Lean_Lsp_RefInfo_instToJsonParentDecl___closed__1);
l_Lean_Lsp_RefInfo_instToJsonParentDecl = _init_l_Lean_Lsp_RefInfo_instToJsonParentDecl();
lean_mark_persistent(l_Lean_Lsp_RefInfo_instToJsonParentDecl);
l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__1 = _init_l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__1();
lean_mark_persistent(l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__1);
l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__2 = _init_l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__2();
lean_mark_persistent(l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__2);
l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__3 = _init_l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__3();
lean_mark_persistent(l_Lean_Lsp_RefInfo_instInhabitedLocation___closed__3);
l_Lean_Lsp_RefInfo_instInhabitedLocation = _init_l_Lean_Lsp_RefInfo_instInhabitedLocation();
lean_mark_persistent(l_Lean_Lsp_RefInfo_instInhabitedLocation);
l_Lean_Lsp_instToJsonRefInfo___closed__1 = _init_l_Lean_Lsp_instToJsonRefInfo___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonRefInfo___closed__1);
l_Lean_Lsp_instToJsonRefInfo___closed__2 = _init_l_Lean_Lsp_instToJsonRefInfo___closed__2();
lean_mark_persistent(l_Lean_Lsp_instToJsonRefInfo___closed__2);
l_Lean_Lsp_instToJsonRefInfo___closed__3 = _init_l_Lean_Lsp_instToJsonRefInfo___closed__3();
lean_mark_persistent(l_Lean_Lsp_instToJsonRefInfo___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___lambda__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonRefInfo___spec__3___closed__2);
l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__6___closed__1 = _init_l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__6___closed__1();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lean_Lsp_instFromJsonModuleRefs___spec__6___closed__1);
l_Lean_Lsp_instFromJsonModuleRefs___closed__1 = _init_l_Lean_Lsp_instFromJsonModuleRefs___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonModuleRefs___closed__1);
l_Lean_Lsp_instFromJsonModuleRefs___closed__2 = _init_l_Lean_Lsp_instFromJsonModuleRefs___closed__2();
lean_mark_persistent(l_Lean_Lsp_instFromJsonModuleRefs___closed__2);
l_Lean_Lsp_instFromJsonModuleRefs___closed__3 = _init_l_Lean_Lsp_instFromJsonModuleRefs___closed__3();
lean_mark_persistent(l_Lean_Lsp_instFromJsonModuleRefs___closed__3);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__1 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__1);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__2 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__2);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__3 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__3);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__4 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__4();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__4);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__5 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__5();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__5);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__6);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__7 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__7();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__7);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__8 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__8();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__8);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__9 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__9();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__9);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__10 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__10();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__10);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__11 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__11();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__11);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__12 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__12();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__12);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__13 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__13();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__13);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__14 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__14();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__14);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__15 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__15();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__15);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__16 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__16();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__16);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__17 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__17();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__17);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__18 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__18();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__18);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__19 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__19();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1914____closed__19);
l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__1 = _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__1);
l_Lean_Lsp_instFromJsonLeanIleanInfoParams = _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanIleanInfoParams);
l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__1 = _init_l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__1);
l_Lean_Lsp_instToJsonLeanIleanInfoParams = _init_l_Lean_Lsp_instToJsonLeanIleanInfoParams();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanIleanInfoParams);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__1 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__1);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__2 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__2);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__3 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__3);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__4 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__4();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__4);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__5 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__5();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__5);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__6 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__6();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__6);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__7 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__7();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__7);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__8 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__8();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__8);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__9 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__9();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2085____closed__9);
l_Lean_Lsp_instFromJsonLeanImportClosureParams___closed__1 = _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanImportClosureParams___closed__1);
l_Lean_Lsp_instFromJsonLeanImportClosureParams = _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanImportClosureParams);
l_Lean_Lsp_instToJsonLeanImportClosureParams___closed__1 = _init_l_Lean_Lsp_instToJsonLeanImportClosureParams___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanImportClosureParams___closed__1);
l_Lean_Lsp_instToJsonLeanImportClosureParams = _init_l_Lean_Lsp_instToJsonLeanImportClosureParams();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanImportClosureParams);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__1 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__1);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__2 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__2);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__3 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__3);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__4 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__4();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__4);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__5 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__5();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__5);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__6 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__6();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__6);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__7 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__7();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__7);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__8 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__8();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__8);
l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__9 = _init_l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__9();
lean_mark_persistent(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2202____closed__9);
l_Lean_Lsp_instFromJsonLeanStaleDependencyParams___closed__1 = _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams___closed__1);
l_Lean_Lsp_instFromJsonLeanStaleDependencyParams = _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams();
lean_mark_persistent(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams);
l_Lean_Lsp_instToJsonLeanStaleDependencyParams___closed__1 = _init_l_Lean_Lsp_instToJsonLeanStaleDependencyParams___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanStaleDependencyParams___closed__1);
l_Lean_Lsp_instToJsonLeanStaleDependencyParams = _init_l_Lean_Lsp_instToJsonLeanStaleDependencyParams();
lean_mark_persistent(l_Lean_Lsp_instToJsonLeanStaleDependencyParams);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
