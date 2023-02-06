// Lean compiler output
// Module: Lean.Meta.DiscrTree
// Imports: Init Lean.Meta.WHNF Lean.Meta.DiscrTreeTypes
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__17(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___rarg___closed__8;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_format(uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__14(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1(lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree___rarg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
static lean_object* l_Lean_Meta_DiscrTree_mkPath___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instLTKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__19___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey___boxed(lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3;
LEAN_EXPORT lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_instToFormatKey___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__3;
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity(uint8_t);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__3___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__15___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___closed__1;
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__21___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_hash___rarg___boxed(lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__9___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(uint8_t, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_join(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instLTKey(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__5;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__6;
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_go___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__2___rarg(uint8_t, lean_object*, size_t, lean_object*);
lean_object* l_List_format___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___rarg___closed__5;
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__8___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___rarg(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lt___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify_process___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__19(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2;
static lean_object* l_Lean_Meta_DiscrTree_Key_format___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_format___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1___rarg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchCore(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_go___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___rarg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__21(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__22(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__17___rarg(uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity___rarg(lean_object*);
uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__18___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lt___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__6;
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__2;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Key_lt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lt(uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__8(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1(lean_object*, uint8_t);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey(uint8_t);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__22___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__23___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__7;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_hasNoindexAnnotation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__21___rarg(uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_go___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__19___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__5___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_format___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__18(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore_go___spec__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchCore___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx(uint8_t);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__7___rarg(uint8_t, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22(lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isStrictImplicit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__14___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Array_contains___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey___boxed(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___rarg___closed__7;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__22___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__9(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__2;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__1;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify_process(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatKey(uint8_t);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify_process___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___boxed(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3;
LEAN_EXPORT lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity___rarg___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__6___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__23(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__23___rarg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_go___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4(lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash___rarg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__13___rarg(uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format(lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__4___rarg(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__17___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12(lean_object*, lean_object*, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_format___rarg___closed__1;
uint8_t l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4;
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__18___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(4u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(3u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(1u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Key_lt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Name_quickLt(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_name_eq(x_3, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_4, x_6);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(x_1);
x_13 = l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(x_2);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
return x_14;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = l_Lean_Name_quickLt(x_15, x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = lean_name_eq(x_15, x_17);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_lt(x_16, x_18);
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
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(x_1);
x_25 = l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(x_2);
x_26 = lean_nat_dec_lt(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
return x_26;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_2, 0);
x_29 = l_Lean_Literal_lt(x_27, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(x_1);
x_31 = l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(x_2);
x_32 = lean_nat_dec_lt(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
return x_32;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_ctor_get(x_2, 2);
x_39 = l_Lean_Name_quickLt(x_33, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_name_eq(x_33, x_36);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = 0;
return x_41;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_lt(x_34, x_37);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = lean_nat_dec_eq(x_34, x_37);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = 0;
return x_44;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_lt(x_35, x_38);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = 1;
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = 1;
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(x_1);
x_49 = l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(x_2);
x_50 = lean_nat_dec_lt(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
return x_50;
}
}
default: 
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(x_1);
x_52 = l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(x_2);
x_53 = lean_nat_dec_lt(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lt(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_lt___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lt___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_DiscrTree_Key_lt(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instLTKey(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instLTKey___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_DiscrTree_instLTKey(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("*", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Key_format___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("◾", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Key_format___rarg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("→", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Key_format___rarg___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Key_format___rarg___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_format___rarg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Nat_repr(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_String_quote(x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 3:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_DiscrTree_Key_format___rarg___closed__2;
return x_9;
}
case 4:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_DiscrTree_Key_format___rarg___closed__4;
return x_10;
}
case 5:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_DiscrTree_Key_format___rarg___closed__6;
return x_11;
}
case 6:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = 1;
x_15 = l_Lean_Name_toString(x_12, x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_DiscrTree_Key_format___rarg___closed__8;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Nat_repr(x_13);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
default: 
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = 1;
x_24 = l_Lean_Name_toString(x_22, x_23);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_format(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_format___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_format___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_DiscrTree_Key_format(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToFormatKey___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_format___rarg), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatKey(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_instToFormatKey___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatKey___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_DiscrTree_instToFormatKey(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity___rarg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
return x_3;
}
case 5:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 6:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_6, x_5);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_arity___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_Key_arity___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_DiscrTree_Key_arity(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_empty___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_empty___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_empty___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_empty___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_empty___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_hash___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_empty___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_DiscrTree_empty___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DiscrTree_empty___closed__5;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_DiscrTree_empty(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" => ", 4);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Meta_DiscrTree_Key_format___rarg(x_9);
x_12 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_inc(x_2);
x_14 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_2, x_10);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = 0;
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_25);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_Meta_DiscrTree_Key_format___rarg(x_29);
x_32 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_2);
x_34 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_2, x_30);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = 0;
x_43 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_box(1);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
x_3 = x_28;
x_4 = x_46;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("node", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Array_isEmpty___rarg(x_4);
x_7 = lean_array_to_list(lean_box(0), x_5);
x_8 = lean_box(0);
lean_inc(x_2);
x_9 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(x_1, x_2, x_7, x_8);
x_10 = l_Std_Format_join(x_9);
if (x_6 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_array_to_list(lean_box(0), x_4);
x_12 = l_List_format___rarg(x_2, x_11);
x_13 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__6;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__4;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
x_20 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = 0;
x_27 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_4);
lean_dec(x_2);
x_29 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__7;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_10);
x_31 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = 0;
x_38 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_37);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format___rarg___boxed), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_instToFormatTrie___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_instToFormatTrie___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 0);
x_8 = l_Lean_Meta_DiscrTree_Key_format___rarg(x_4);
x_9 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_2, x_5);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = 0;
x_20 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_unbox(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_box(1);
lean_inc(x_6);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_box(0);
lean_inc(x_6);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_20);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_format___rarg___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = lean_box(0);
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_box(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Meta_DiscrTree_format___rarg___closed__1;
x_7 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg(x_3, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Meta_DiscrTree_format___rarg___lambda__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Meta_DiscrTree_format___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___rarg___boxed), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_instToFormatDiscrTree___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_instToFormatDiscrTree___rarg(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_discr_tree_tmp", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__2;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId;
x_2 = l_Lean_Expr_mvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DiscrTree_empty___closed__5;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isProof(x_1, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget(x_3, x_2);
x_13 = l_Lean_Meta_ParamInfo_isInstImplicit(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Meta_ParamInfo_isImplicit(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Meta_ParamInfo_isStrictImplicit(x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Meta_isProof(x_1, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Meta_isType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = 1;
x_23 = lean_box(x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_12);
x_40 = l_Lean_Meta_isType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = 1;
x_46 = lean_box(x_45);
lean_ctor_set(x_40, 0, x_46);
return x_40;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec(x_40);
x_48 = 1;
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
lean_dec(x_52);
x_53 = 0;
x_54 = lean_box(x_53);
lean_ctor_set(x_40, 0, x_54);
return x_40;
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_dec(x_40);
x_56 = 0;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_40);
if (x_59 == 0)
{
return x_40;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_63 = 1;
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_8);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg(x_11, x_2, x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
lean_dec(x_2);
x_18 = lean_array_push(x_4, x_11);
x_2 = x_17;
x_3 = x_10;
x_4 = x_18;
x_9 = x_15;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_2, x_21);
lean_dec(x_2);
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar;
x_24 = lean_array_push(x_4, x_23);
x_2 = x_22;
x_3 = x_10;
x_4 = x_24;
x_9 = x_20;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_9);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("OfNat", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__1;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("zero", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("succ", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isNatLit(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; uint8_t x_40; 
x_3 = l_Lean_Expr_getAppFn(x_1);
x_40 = l_Lean_Expr_isConst(x_3);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = 1;
x_4 = x_41;
goto block_39;
}
else
{
uint8_t x_42; 
x_42 = 0;
x_4 = x_42;
goto block_39;
}
block_39:
{
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_31; uint8_t x_32; 
x_5 = l_Lean_Expr_constName_x21(x_3);
lean_dec(x_3);
x_31 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
x_32 = lean_name_eq(x_5, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = 0;
x_6 = x_33;
goto block_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_dec_eq(x_35, x_36);
lean_dec(x_35);
x_6 = x_37;
goto block_30;
}
block_30:
{
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3;
x_8 = lean_name_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6;
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_5);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = 0;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_12);
lean_dec(x_1);
x_14 = lean_nat_dec_eq(x_13, x_12);
lean_dec(x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_1);
x_19 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6;
x_20 = lean_name_eq(x_5, x_19);
lean_dec(x_5);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_16);
x_21 = 0;
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_16, x_15);
lean_dec(x_16);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_16, x_23);
lean_dec(x_16);
x_25 = lean_nat_sub(x_24, x_23);
lean_dec(x_24);
x_26 = l_Lean_Expr_getRevArg_x21(x_1, x_25);
x_1 = x_26;
goto _start;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_5);
x_28 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_1 = x_28;
goto _start;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_3);
lean_dec(x_1);
x_38 = 0;
return x_38;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_1);
x_43 = 1;
return x_43;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType___closed__1;
x_11 = l_Lean_Expr_isConstOf(x_9, x_10);
lean_dec(x_9);
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType___closed__1;
x_16 = l_Lean_Expr_isConstOf(x_13, x_15);
lean_dec(x_13);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HAdd", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hAdd", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__1;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("add", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Add", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__6;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_52; lean_object* x_92; uint8_t x_93; 
x_92 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__5;
x_93 = lean_name_eq(x_1, x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7;
x_95 = lean_name_eq(x_1, x_94);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = 0;
x_52 = x_96;
goto block_91;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_unsigned_to_nat(0u);
x_98 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_97);
x_99 = lean_unsigned_to_nat(4u);
x_100 = lean_nat_dec_eq(x_98, x_99);
lean_dec(x_98);
x_52 = x_100;
goto block_91;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_unsigned_to_nat(0u);
x_102 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_101);
x_103 = lean_unsigned_to_nat(2u);
x_104 = lean_nat_dec_eq(x_102, x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7;
x_106 = lean_name_eq(x_1, x_105);
if (x_106 == 0)
{
uint8_t x_107; 
lean_dec(x_102);
x_107 = 0;
x_52 = x_107;
goto block_91;
}
else
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_unsigned_to_nat(4u);
x_109 = lean_nat_dec_eq(x_102, x_108);
lean_dec(x_102);
x_52 = x_109;
goto block_91;
}
}
else
{
lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_102);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_111 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_110);
x_112 = lean_box(x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_7);
return x_113;
}
}
block_51:
{
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
x_10 = lean_name_eq(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_14);
lean_dec(x_2);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_24 = lean_nat_sub(x_23, x_22);
lean_dec(x_23);
lean_inc(x_2);
x_25 = l_Lean_Expr_getRevArg_x21(x_2, x_24);
x_26 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType(x_25, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = 0;
x_32 = lean_box(x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_26);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_26, 0);
lean_dec(x_38);
x_39 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_40 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_39);
x_41 = lean_box(x_40);
lean_ctor_set(x_26, 0, x_41);
return x_26;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_dec(x_26);
x_43 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_44 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_43);
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
block_91:
{
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3;
x_54 = lean_name_eq(x_1, x_53);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = 0;
x_8 = x_55;
goto block_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_unsigned_to_nat(0u);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_56);
x_58 = lean_unsigned_to_nat(6u);
x_59 = lean_nat_dec_eq(x_57, x_58);
lean_dec(x_57);
x_8 = x_59;
goto block_51;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_unsigned_to_nat(0u);
x_61 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_60);
x_62 = lean_nat_sub(x_61, x_60);
lean_dec(x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_62, x_63);
lean_dec(x_62);
lean_inc(x_2);
x_65 = l_Lean_Expr_getRevArg_x21(x_2, x_64);
x_66 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType(x_65, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
uint8_t x_69; 
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
x_71 = 0;
x_72 = lean_box(x_71);
lean_ctor_set(x_66, 0, x_72);
return x_66;
}
else
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = 0;
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_66);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_66, 0);
lean_dec(x_78);
x_79 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_80 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_79);
x_81 = lean_box(x_80);
lean_ctor_set(x_66, 0, x_81);
return x_66;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_66, 1);
lean_inc(x_82);
lean_dec(x_66);
x_83 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_84 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_83);
x_85 = lean_box(x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_66);
if (x_87 == 0)
{
return x_66;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_66, 0);
x_89 = lean_ctor_get(x_66, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_66);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6;
x_9 = lean_name_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("noindex", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2;
x_3 = l_Lean_annotation_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_hasNoindexAnnotation___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore_go___spec__3(x_8, x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
x_12 = l_Lean_Meta_unfoldDefinition_x3f(x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
lean_inc(x_10);
x_17 = l_Lean_Expr_etaExpandedStrict_x3f(x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_18; 
lean_free_object(x_12);
lean_dec(x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_1 = x_18;
x_7 = x_15;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
lean_inc(x_10);
x_21 = l_Lean_Expr_etaExpandedStrict_x3f(x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_10);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_1 = x_23;
x_7 = x_20;
goto _start;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
lean_dec(x_13);
x_1 = x_26;
x_7 = x_25;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
return x_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_DiscrTree_reduce(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 4:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 7:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Expr_hasLooseBVars(x_4);
return x_5;
}
case 9:
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
case 11:
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
default: 
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore_go___spec__3(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
x_12 = l_Lean_Meta_unfoldDefinition_x3f(x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_Expr_getAppFn(x_21);
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_free_object(x_12);
lean_dec(x_10);
x_2 = x_21;
x_7 = x_19;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
lean_dec(x_13);
x_27 = l_Lean_Expr_getAppFn(x_26);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_10);
x_2 = x_26;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_9);
if (x_35 == 0)
{
return x_9;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_9, 0);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_9);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_12 = l_Lean_Expr_etaExpandedStrict_x3f(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
else
{
lean_object* x_13; 
lean_free_object(x_8);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_1 = x_13;
x_7 = x_11;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
lean_inc(x_15);
x_17 = l_Lean_Expr_etaExpandedStrict_x3f(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_15);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_1 = x_19;
x_7 = x_16;
goto _start;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_2 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Meta_DiscrTree_reduce(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_reduceUntilBadKey(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_DiscrTree_reduceDT(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_12);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
x_15 = l_Lean_Meta_getFunInfoNArgs(x_4, x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_13, x_19);
lean_dec(x_13);
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_18, x_20, x_1, x_5, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Meta_DiscrTree_reduceDT(x_4, x_2, x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_getAppFn(x_13);
switch (lean_obj_tag(x_15)) {
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_13, x_17);
lean_inc(x_18);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_18);
x_20 = l_Lean_Meta_getFunInfoNArgs(x_15, x_18, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_18, x_24);
lean_dec(x_18);
x_26 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_23, x_25, x_13, x_3, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_19);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
case 2:
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_13);
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
lean_dec(x_15);
x_43 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId;
x_44 = lean_name_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_free_object(x_11);
x_45 = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(x_42, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
lean_dec(x_49);
x_50 = lean_box(3);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_3);
lean_ctor_set(x_45, 0, x_51);
return x_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_box(3);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_45);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_45, 0);
lean_dec(x_57);
x_58 = lean_box(4);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_3);
lean_ctor_set(x_45, 0, x_59);
return x_45;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_dec(x_45);
x_61 = lean_box(4);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_3);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_45);
if (x_64 == 0)
{
return x_45;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_45, 0);
x_66 = lean_ctor_get(x_45, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_45);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_42);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_68 = lean_box(3);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_3);
lean_ctor_set(x_11, 0, x_69);
return x_11;
}
}
case 4:
{
lean_free_object(x_11);
if (x_2 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_15, 0);
lean_inc(x_70);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_71 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar(x_70, x_13, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_box(0);
x_76 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_13, x_1, x_70, x_15, x_3, x_75, x_5, x_6, x_7, x_8, x_74);
return x_76;
}
else
{
uint8_t x_77; 
lean_dec(x_70);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = !lean_is_exclusive(x_71);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_71, 0);
lean_dec(x_78);
x_79 = lean_box(3);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_3);
lean_ctor_set(x_71, 0, x_80);
return x_71;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_box(3);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_3);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_70);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_71);
if (x_85 == 0)
{
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_71, 0);
x_87 = lean_ctor_get(x_71, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_71);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_15, 0);
lean_inc(x_89);
x_90 = lean_box(0);
x_91 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_13, x_1, x_89, x_15, x_3, x_90, x_5, x_6, x_7, x_8, x_14);
return x_91;
}
}
case 7:
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_92 = lean_ctor_get(x_15, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_15, 2);
lean_inc(x_93);
lean_dec(x_15);
x_94 = l_Lean_Expr_hasLooseBVars(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_box(5);
x_96 = lean_array_push(x_3, x_92);
x_97 = lean_array_push(x_96, x_93);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_11, 0, x_98);
return x_11;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_93);
lean_dec(x_92);
x_99 = lean_box(4);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_3);
lean_ctor_set(x_11, 0, x_100);
return x_11;
}
}
case 9:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_101 = lean_ctor_get(x_15, 0);
lean_inc(x_101);
lean_dec(x_15);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_3);
lean_ctor_set(x_11, 0, x_103);
return x_11;
}
case 11:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_free_object(x_11);
x_104 = lean_ctor_get(x_15, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_15, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_15, 2);
lean_inc(x_106);
x_107 = lean_st_ref_get(x_8, x_14);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_104);
x_111 = lean_is_class(x_110, x_104);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_13, x_112);
lean_inc(x_113);
x_114 = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_105);
lean_ctor_set(x_114, 2, x_113);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_113);
x_115 = l_Lean_Meta_getFunInfoNArgs(x_15, x_113, x_5, x_6, x_7, x_8, x_109);
if (x_111 == 0)
{
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_array_push(x_3, x_106);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec(x_116);
x_120 = lean_unsigned_to_nat(1u);
x_121 = lean_nat_sub(x_113, x_120);
lean_dec(x_113);
x_122 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_119, x_121, x_13, x_118, x_5, x_6, x_7, x_8, x_117);
lean_dec(x_119);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_114);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_122, 0, x_125);
return x_122;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_122, 0);
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_122);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_114);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_114);
x_130 = !lean_is_exclusive(x_122);
if (x_130 == 0)
{
return x_122;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_122, 0);
x_132 = lean_ctor_get(x_122, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_122);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_106);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_134 = !lean_is_exclusive(x_115);
if (x_134 == 0)
{
return x_115;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_115, 0);
x_136 = lean_ctor_get(x_115, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_115);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_ctor_get(x_115, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_115, 1);
lean_inc(x_139);
lean_dec(x_115);
x_140 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(x_106);
x_141 = lean_array_push(x_3, x_140);
x_142 = lean_ctor_get(x_138, 0);
lean_inc(x_142);
lean_dec(x_138);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_sub(x_113, x_143);
lean_dec(x_113);
x_145 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_142, x_144, x_13, x_141, x_5, x_6, x_7, x_8, x_139);
lean_dec(x_142);
if (lean_obj_tag(x_145) == 0)
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_145, 0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_114);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_145, 0, x_148);
return x_145;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_145, 0);
x_150 = lean_ctor_get(x_145, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_145);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_114);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
uint8_t x_153; 
lean_dec(x_114);
x_153 = !lean_is_exclusive(x_145);
if (x_153 == 0)
{
return x_145;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_145, 0);
x_155 = lean_ctor_get(x_145, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_145);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_106);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_115);
if (x_157 == 0)
{
return x_115;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_115, 0);
x_159 = lean_ctor_get(x_115, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_115);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
default: 
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_161 = lean_box(4);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_3);
lean_ctor_set(x_11, 0, x_162);
return x_11;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_11, 0);
x_164 = lean_ctor_get(x_11, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_11);
x_165 = l_Lean_Expr_getAppFn(x_163);
switch (lean_obj_tag(x_165)) {
case 1:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_unsigned_to_nat(0u);
x_168 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_163, x_167);
lean_inc(x_168);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_168);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_168);
x_170 = l_Lean_Meta_getFunInfoNArgs(x_165, x_168, x_5, x_6, x_7, x_8, x_164);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_nat_sub(x_168, x_174);
lean_dec(x_168);
x_176 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_173, x_175, x_163, x_3, x_5, x_6, x_7, x_8, x_172);
lean_dec(x_173);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_169);
lean_ctor_set(x_180, 1, x_177);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_169);
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_176, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_184 = x_176;
} else {
 lean_dec_ref(x_176);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_186 = lean_ctor_get(x_170, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_170, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_188 = x_170;
} else {
 lean_dec_ref(x_170);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
case 2:
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; 
lean_dec(x_163);
x_190 = lean_ctor_get(x_165, 0);
lean_inc(x_190);
lean_dec(x_165);
x_191 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId;
x_192 = lean_name_eq(x_190, x_191);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(x_190, x_5, x_6, x_7, x_8, x_164);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; uint8_t x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_unbox(x_194);
lean_dec(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_197 = x_193;
} else {
 lean_dec_ref(x_193);
 x_197 = lean_box(0);
}
x_198 = lean_box(3);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_3);
if (lean_is_scalar(x_197)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_197;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_196);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_193, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_202 = x_193;
} else {
 lean_dec_ref(x_193);
 x_202 = lean_box(0);
}
x_203 = lean_box(4);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_3);
if (lean_is_scalar(x_202)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_202;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_201);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_3);
x_206 = lean_ctor_get(x_193, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_193, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_208 = x_193;
} else {
 lean_dec_ref(x_193);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_190);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_210 = lean_box(3);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_3);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_164);
return x_212;
}
}
case 4:
{
if (x_2 == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_165, 0);
lean_inc(x_213);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_163);
x_214 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar(x_213, x_163, x_5, x_6, x_7, x_8, x_164);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_unbox(x_215);
lean_dec(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
lean_dec(x_214);
x_218 = lean_box(0);
x_219 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_163, x_1, x_213, x_165, x_3, x_218, x_5, x_6, x_7, x_8, x_217);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_213);
lean_dec(x_165);
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_220 = lean_ctor_get(x_214, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_221 = x_214;
} else {
 lean_dec_ref(x_214);
 x_221 = lean_box(0);
}
x_222 = lean_box(3);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_3);
if (lean_is_scalar(x_221)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_221;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_220);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_213);
lean_dec(x_165);
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_225 = lean_ctor_get(x_214, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_214, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_227 = x_214;
} else {
 lean_dec_ref(x_214);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_165, 0);
lean_inc(x_229);
x_230 = lean_box(0);
x_231 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_163, x_1, x_229, x_165, x_3, x_230, x_5, x_6, x_7, x_8, x_164);
return x_231;
}
}
case 7:
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; 
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_232 = lean_ctor_get(x_165, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_165, 2);
lean_inc(x_233);
lean_dec(x_165);
x_234 = l_Lean_Expr_hasLooseBVars(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_235 = lean_box(5);
x_236 = lean_array_push(x_3, x_232);
x_237 = lean_array_push(x_236, x_233);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_164);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_233);
lean_dec(x_232);
x_240 = lean_box(4);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_3);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_164);
return x_242;
}
}
case 9:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_243 = lean_ctor_get(x_165, 0);
lean_inc(x_243);
lean_dec(x_165);
x_244 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_244, 0, x_243);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_3);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_164);
return x_246;
}
case 11:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_247 = lean_ctor_get(x_165, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_165, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_165, 2);
lean_inc(x_249);
x_250 = lean_st_ref_get(x_8, x_164);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_247);
x_254 = lean_is_class(x_253, x_247);
x_255 = lean_unsigned_to_nat(0u);
x_256 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_163, x_255);
lean_inc(x_256);
x_257 = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(x_257, 0, x_247);
lean_ctor_set(x_257, 1, x_248);
lean_ctor_set(x_257, 2, x_256);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_256);
x_258 = l_Lean_Meta_getFunInfoNArgs(x_165, x_256, x_5, x_6, x_7, x_8, x_252);
if (x_254 == 0)
{
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_array_push(x_3, x_249);
x_262 = lean_ctor_get(x_259, 0);
lean_inc(x_262);
lean_dec(x_259);
x_263 = lean_unsigned_to_nat(1u);
x_264 = lean_nat_sub(x_256, x_263);
lean_dec(x_256);
x_265 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_262, x_264, x_163, x_261, x_5, x_6, x_7, x_8, x_260);
lean_dec(x_262);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_268 = x_265;
} else {
 lean_dec_ref(x_265);
 x_268 = lean_box(0);
}
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_257);
lean_ctor_set(x_269, 1, x_266);
if (lean_is_scalar(x_268)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_268;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_267);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_257);
x_271 = lean_ctor_get(x_265, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_265, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_273 = x_265;
} else {
 lean_dec_ref(x_265);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_249);
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_275 = lean_ctor_get(x_258, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_258, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_277 = x_258;
} else {
 lean_dec_ref(x_258);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_279 = lean_ctor_get(x_258, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_258, 1);
lean_inc(x_280);
lean_dec(x_258);
x_281 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(x_249);
x_282 = lean_array_push(x_3, x_281);
x_283 = lean_ctor_get(x_279, 0);
lean_inc(x_283);
lean_dec(x_279);
x_284 = lean_unsigned_to_nat(1u);
x_285 = lean_nat_sub(x_256, x_284);
lean_dec(x_256);
x_286 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_283, x_285, x_163, x_282, x_5, x_6, x_7, x_8, x_280);
lean_dec(x_283);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_289 = x_286;
} else {
 lean_dec_ref(x_286);
 x_289 = lean_box(0);
}
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_257);
lean_ctor_set(x_290, 1, x_287);
if (lean_is_scalar(x_289)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_289;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_288);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_257);
x_292 = lean_ctor_get(x_286, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_286, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_294 = x_286;
} else {
 lean_dec_ref(x_286);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_249);
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_296 = lean_ctor_get(x_258, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_258, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_298 = x_258;
} else {
 lean_dec_ref(x_258);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
}
default: 
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_165);
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_300 = lean_box(4);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_3);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_164);
return x_302;
}
}
}
}
else
{
uint8_t x_303; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_303 = !lean_is_exclusive(x_11);
if (x_303 == 0)
{
return x_11;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_11, 0);
x_305 = lean_ctor_get(x_11, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_11);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_307 = lean_box(3);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_3);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_9);
return x_309;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_instInhabitedExpr;
x_12 = l_Array_back___rarg(x_11, x_3);
x_13 = lean_array_pop(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(x_1, x_2, x_13, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_array_push(x_4, x_17);
x_20 = 0;
x_2 = x_20;
x_3 = x_18;
x_4 = x_19;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_DiscrTree_mkPathAux(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(8u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_mkPath___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity;
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Meta_DiscrTree_mkPath___closed__1;
x_9 = lean_array_push(x_8, x_2);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = 2;
lean_ctor_set_uint8(x_11, 5, x_13);
x_14 = 1;
x_15 = l_Lean_Meta_DiscrTree_mkPathAux(x_1, x_14, x_9, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_24 = lean_ctor_get_uint8(x_11, 0);
x_25 = lean_ctor_get_uint8(x_11, 1);
x_26 = lean_ctor_get_uint8(x_11, 2);
x_27 = lean_ctor_get_uint8(x_11, 3);
x_28 = lean_ctor_get_uint8(x_11, 4);
x_29 = lean_ctor_get_uint8(x_11, 6);
x_30 = lean_ctor_get_uint8(x_11, 7);
x_31 = lean_ctor_get_uint8(x_11, 8);
x_32 = lean_ctor_get_uint8(x_11, 9);
x_33 = lean_ctor_get_uint8(x_11, 10);
x_34 = lean_ctor_get_uint8(x_11, 11);
x_35 = lean_ctor_get_uint8(x_11, 12);
lean_dec(x_11);
x_36 = 2;
x_37 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_37, 0, x_24);
lean_ctor_set_uint8(x_37, 1, x_25);
lean_ctor_set_uint8(x_37, 2, x_26);
lean_ctor_set_uint8(x_37, 3, x_27);
lean_ctor_set_uint8(x_37, 4, x_28);
lean_ctor_set_uint8(x_37, 5, x_36);
lean_ctor_set_uint8(x_37, 6, x_29);
lean_ctor_set_uint8(x_37, 7, x_30);
lean_ctor_set_uint8(x_37, 8, x_31);
lean_ctor_set_uint8(x_37, 9, x_32);
lean_ctor_set_uint8(x_37, 10, x_33);
lean_ctor_set_uint8(x_37, 11, x_34);
lean_ctor_set_uint8(x_37, 12, x_35);
lean_ctor_set(x_3, 0, x_37);
x_38 = 1;
x_39 = l_Lean_Meta_DiscrTree_mkPathAux(x_1, x_38, x_9, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_46 = x_39;
} else {
 lean_dec_ref(x_39);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get(x_3, 1);
x_50 = lean_ctor_get(x_3, 2);
x_51 = lean_ctor_get(x_3, 3);
x_52 = lean_ctor_get(x_3, 4);
x_53 = lean_ctor_get(x_3, 5);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_3);
x_54 = lean_ctor_get_uint8(x_48, 0);
x_55 = lean_ctor_get_uint8(x_48, 1);
x_56 = lean_ctor_get_uint8(x_48, 2);
x_57 = lean_ctor_get_uint8(x_48, 3);
x_58 = lean_ctor_get_uint8(x_48, 4);
x_59 = lean_ctor_get_uint8(x_48, 6);
x_60 = lean_ctor_get_uint8(x_48, 7);
x_61 = lean_ctor_get_uint8(x_48, 8);
x_62 = lean_ctor_get_uint8(x_48, 9);
x_63 = lean_ctor_get_uint8(x_48, 10);
x_64 = lean_ctor_get_uint8(x_48, 11);
x_65 = lean_ctor_get_uint8(x_48, 12);
if (lean_is_exclusive(x_48)) {
 x_66 = x_48;
} else {
 lean_dec_ref(x_48);
 x_66 = lean_box(0);
}
x_67 = 2;
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 0, 13);
} else {
 x_68 = x_66;
}
lean_ctor_set_uint8(x_68, 0, x_54);
lean_ctor_set_uint8(x_68, 1, x_55);
lean_ctor_set_uint8(x_68, 2, x_56);
lean_ctor_set_uint8(x_68, 3, x_57);
lean_ctor_set_uint8(x_68, 4, x_58);
lean_ctor_set_uint8(x_68, 5, x_67);
lean_ctor_set_uint8(x_68, 6, x_59);
lean_ctor_set_uint8(x_68, 7, x_60);
lean_ctor_set_uint8(x_68, 8, x_61);
lean_ctor_set_uint8(x_68, 9, x_62);
lean_ctor_set_uint8(x_68, 10, x_63);
lean_ctor_set_uint8(x_68, 11, x_64);
lean_ctor_set_uint8(x_68, 12, x_65);
x_69 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_49);
lean_ctor_set(x_69, 2, x_50);
lean_ctor_set(x_69, 3, x_51);
lean_ctor_set(x_69, 4, x_52);
lean_ctor_set(x_69, 5, x_53);
x_70 = 1;
x_71 = l_Lean_Meta_DiscrTree_mkPathAux(x_1, x_70, x_9, x_8, x_69, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_78 = x_71;
} else {
 lean_dec_ref(x_71);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_DiscrTree_mkPath(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___closed__1;
x_9 = lean_array_push(x_8, x_4);
x_10 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_array_fget(x_3, x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_3, x_4, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___closed__1;
x_18 = lean_array_push(x_17, x_16);
x_19 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Array_contains___rarg(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_array_push(x_2, x_3);
return x_5;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_nat_add(x_9, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
lean_inc(x_8);
x_14 = lean_array_get(x_8, x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_10);
x_18 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_16, x_15);
lean_dec(x_15);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
x_19 = lean_array_get_size(x_7);
x_20 = lean_nat_dec_lt(x_13, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_array_fget(x_7, x_13);
x_22 = lean_box(0);
x_23 = lean_array_fset(x_7, x_13, x_22);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_21, 0);
lean_dec(x_26);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_5, x_27);
x_29 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_28, x_25);
lean_dec(x_28);
lean_ctor_set(x_21, 1, x_29);
lean_ctor_set(x_21, 0, x_6);
x_30 = lean_array_fset(x_23, x_13, x_21);
lean_dec(x_13);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_5, x_32);
x_34 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_33, x_31);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_array_fset(x_23, x_13, x_35);
lean_dec(x_13);
return x_36;
}
}
}
else
{
x_10 = x_13;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_16);
lean_dec(x_15);
x_38 = lean_nat_dec_eq(x_13, x_9);
if (x_38 == 0)
{
lean_dec(x_9);
x_9 = x_13;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
x_42 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_3, x_4, x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_nat_add(x_9, x_40);
lean_dec(x_9);
x_45 = l_Array_insertAt_x21___rarg(x_7, x_44, x_43);
lean_dec(x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_34; uint8_t x_67; 
x_67 = l_Array_isEmpty___rarg(x_7);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
x_69 = lean_array_get(x_8, x_7, x_68);
x_70 = lean_ctor_get(x_8, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_70, x_71);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_71, x_70);
lean_dec(x_70);
lean_dec(x_71);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = 1;
x_34 = x_74;
goto block_66;
}
else
{
uint8_t x_75; 
x_75 = 0;
x_34 = x_75;
goto block_66;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_8);
lean_dec(x_2);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_add(x_5, x_76);
x_78 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_3, x_4, x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_6);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Array_insertAt_x21___rarg(x_7, x_68, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_8);
lean_dec(x_2);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_5, x_81);
x_83 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_3, x_4, x_82);
lean_dec(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_6);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_array_push(x_7, x_84);
return x_85;
}
block_33:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_8);
x_15 = lean_array_get_size(x_7);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
x_18 = lean_nat_dec_lt(x_17, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_array_fget(x_7, x_17);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_7, x_17, x_20);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = lean_nat_add(x_5, x_16);
x_26 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_25, x_23);
lean_dec(x_25);
lean_ctor_set(x_19, 1, x_26);
lean_ctor_set(x_19, 0, x_6);
x_27 = lean_array_fset(x_21, x_17, x_19);
lean_dec(x_17);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_nat_add(x_5, x_16);
x_30 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_29, x_28);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_fset(x_21, x_17, x_31);
lean_dec(x_17);
return x_32;
}
}
}
}
block_66:
{
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_8);
x_35 = l_Array_back___rarg(x_8, x_7);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
x_38 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_36, x_37);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_37, x_36);
lean_dec(x_36);
lean_dec(x_37);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = 1;
x_9 = x_40;
goto block_33;
}
else
{
uint8_t x_41; 
x_41 = 0;
x_9 = x_41;
goto block_33;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_2);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_5, x_42);
x_44 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_3, x_4, x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_6);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_push(x_7, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_8);
x_47 = lean_array_get_size(x_7);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_47);
lean_dec(x_47);
if (x_49 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_array_fget(x_7, x_48);
x_51 = lean_box(0);
x_52 = lean_array_fset(x_7, x_48, x_51);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_50, 1);
x_55 = lean_ctor_get(x_50, 0);
lean_dec(x_55);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_5, x_56);
x_58 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_57, x_54);
lean_dec(x_57);
lean_ctor_set(x_50, 1, x_58);
lean_ctor_set(x_50, 0, x_6);
x_59 = lean_array_fset(x_52, x_48, x_50);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_dec(x_50);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_5, x_61);
x_63 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_62, x_60);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_6);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_array_fset(x_52, x_48, x_64);
return x_65;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg(x_2, x_8, x_4);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_fget(x_3, x_5);
x_14 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_14);
lean_inc(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_6);
x_16 = l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_13, x_9, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_array_get_size(x_3);
x_21 = lean_nat_dec_lt(x_5, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg(x_2, x_18, x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_array_fget(x_3, x_5);
x_25 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_24, x_19, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_array_fget(x_3, x_6);
x_11 = lean_array_fget(x_4, x_6);
x_12 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_10);
x_13 = lean_uint64_to_usize(x_12);
x_14 = 1;
x_15 = lean_usize_sub(x_2, x_14);
x_16 = 5;
x_17 = lean_usize_mul(x_16, x_15);
x_18 = lean_usize_shift_right(x_13, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_21 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_1, x_7, x_18, x_2, x_10, x_11);
x_5 = lean_box(0);
x_6 = x_20;
x_7 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = lean_array_push(x_6, x_4);
x_14 = lean_array_push(x_7, x_5);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_array_push(x_7, x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_fget(x_6, x_3);
x_19 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_2, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 0);
lean_dec(x_25);
x_26 = lean_array_fset(x_6, x_3, x_4);
x_27 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_28 = lean_array_fset(x_6, x_3, x_4);
x_29 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg___boxed), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = 1;
x_10 = 5;
x_11 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_12 = lean_usize_land(x_3, x_11);
x_13 = lean_usize_to_nat(x_12);
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget(x_8, x_13);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_8, x_13, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
x_22 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_16);
x_23 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_20, x_21, x_5, x_6);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_array_fset(x_18, x_13, x_24);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
else
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 0, x_5);
x_26 = lean_array_fset(x_18, x_13, x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_27, x_28, x_5, x_6);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_array_fset(x_18, x_13, x_31);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_array_fset(x_18, x_13, x_33);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
}
}
case 1:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_usize_shift_right(x_3, x_10);
x_38 = lean_usize_add(x_4, x_9);
x_39 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_1, x_36, x_37, x_38, x_5, x_6);
lean_ctor_set(x_16, 0, x_39);
x_40 = lean_array_fset(x_18, x_13, x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_40);
return x_2;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_16, 0);
lean_inc(x_41);
lean_dec(x_16);
x_42 = lean_usize_shift_right(x_3, x_10);
x_43 = lean_usize_add(x_4, x_9);
x_44 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_1, x_41, x_42, x_43, x_5, x_6);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_array_fset(x_18, x_13, x_45);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_46);
return x_2;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_6);
x_48 = lean_array_fset(x_18, x_13, x_47);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_48);
return x_2;
}
}
}
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = 1;
x_51 = 5;
x_52 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_53 = lean_usize_land(x_3, x_52);
x_54 = lean_usize_to_nat(x_53);
x_55 = lean_array_get_size(x_49);
x_56 = lean_nat_dec_lt(x_54, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_6);
lean_dec(x_5);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_49);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_array_fget(x_49, x_54);
x_59 = lean_box(0);
x_60 = lean_array_fset(x_49, x_54, x_59);
switch (lean_obj_tag(x_58)) {
case 0:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_63 = x_58;
} else {
 lean_dec_ref(x_58);
 x_63 = lean_box(0);
}
x_64 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
x_65 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_61, x_62, x_5, x_6);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_array_fset(x_60, x_54, x_66);
lean_dec(x_54);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_62);
lean_dec(x_61);
if (lean_is_scalar(x_63)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_63;
}
lean_ctor_set(x_69, 0, x_5);
lean_ctor_set(x_69, 1, x_6);
x_70 = lean_array_fset(x_60, x_54, x_69);
lean_dec(x_54);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
case 1:
{
lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_58, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_73 = x_58;
} else {
 lean_dec_ref(x_58);
 x_73 = lean_box(0);
}
x_74 = lean_usize_shift_right(x_3, x_51);
x_75 = lean_usize_add(x_4, x_50);
x_76 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_1, x_72, x_74, x_75, x_5, x_6);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_array_fset(x_60, x_54, x_77);
lean_dec(x_54);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
default: 
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_6);
x_81 = lean_array_fset(x_60, x_54, x_80);
lean_dec(x_54);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_2);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; size_t x_86; uint8_t x_87; 
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(x_1, x_2, x_84, x_5, x_6);
x_86 = 7;
x_87 = lean_usize_dec_le(x_86, x_4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_85);
x_89 = lean_unsigned_to_nat(4u);
x_90 = lean_nat_dec_lt(x_88, x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_dec(x_85);
x_93 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_94 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(x_1, x_4, x_91, x_92, lean_box(0), x_84, x_93);
lean_dec(x_92);
lean_dec(x_91);
return x_94;
}
else
{
return x_85;
}
}
else
{
return x_85;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; size_t x_100; uint8_t x_101; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_2);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(x_1, x_97, x_98, x_5, x_6);
x_100 = 7;
x_101 = lean_usize_dec_le(x_100, x_4);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_99);
x_103 = lean_unsigned_to_nat(4u);
x_104 = lean_nat_dec_lt(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_dec(x_99);
x_107 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_108 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(x_1, x_4, x_105, x_106, lean_box(0), x_98, x_107);
lean_dec(x_106);
lean_dec(x_105);
return x_108;
}
else
{
return x_99;
}
}
else
{
return x_99;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_9 = lean_uint64_to_usize(x_8);
x_10 = 1;
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_1, x_6, x_9, x_10, x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_17 = lean_uint64_to_usize(x_16);
x_18 = 1;
x_19 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_1, x_14, x_17, x_18, x_3, x_4);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_15, x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_array_fget(x_3, x_6);
x_11 = lean_array_fget(x_4, x_6);
x_12 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_10);
x_13 = lean_uint64_to_usize(x_12);
x_14 = 1;
x_15 = lean_usize_sub(x_2, x_14);
x_16 = 5;
x_17 = lean_usize_mul(x_16, x_15);
x_18 = lean_usize_shift_right(x_13, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_21 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_1, x_7, x_18, x_2, x_10, x_11);
x_5 = lean_box(0);
x_6 = x_20;
x_7 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = lean_array_push(x_6, x_4);
x_14 = lean_array_push(x_7, x_5);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_array_push(x_7, x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_fget(x_6, x_3);
x_19 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_2, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 0);
lean_dec(x_25);
x_26 = lean_array_fset(x_6, x_3, x_4);
x_27 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_28 = lean_array_fset(x_6, x_3, x_4);
x_29 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = 1;
x_10 = 5;
x_11 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_12 = lean_usize_land(x_3, x_11);
x_13 = lean_usize_to_nat(x_12);
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget(x_8, x_13);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_8, x_13, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
x_22 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_16);
x_23 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_20, x_21, x_5, x_6);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_array_fset(x_18, x_13, x_24);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
else
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 0, x_5);
x_26 = lean_array_fset(x_18, x_13, x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_27, x_28, x_5, x_6);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_array_fset(x_18, x_13, x_31);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_array_fset(x_18, x_13, x_33);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
}
}
case 1:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_usize_shift_right(x_3, x_10);
x_38 = lean_usize_add(x_4, x_9);
x_39 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_1, x_36, x_37, x_38, x_5, x_6);
lean_ctor_set(x_16, 0, x_39);
x_40 = lean_array_fset(x_18, x_13, x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_40);
return x_2;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_16, 0);
lean_inc(x_41);
lean_dec(x_16);
x_42 = lean_usize_shift_right(x_3, x_10);
x_43 = lean_usize_add(x_4, x_9);
x_44 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_1, x_41, x_42, x_43, x_5, x_6);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_array_fset(x_18, x_13, x_45);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_46);
return x_2;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_6);
x_48 = lean_array_fset(x_18, x_13, x_47);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_48);
return x_2;
}
}
}
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = 1;
x_51 = 5;
x_52 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_53 = lean_usize_land(x_3, x_52);
x_54 = lean_usize_to_nat(x_53);
x_55 = lean_array_get_size(x_49);
x_56 = lean_nat_dec_lt(x_54, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_6);
lean_dec(x_5);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_49);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_array_fget(x_49, x_54);
x_59 = lean_box(0);
x_60 = lean_array_fset(x_49, x_54, x_59);
switch (lean_obj_tag(x_58)) {
case 0:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_63 = x_58;
} else {
 lean_dec_ref(x_58);
 x_63 = lean_box(0);
}
x_64 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
x_65 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_61, x_62, x_5, x_6);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_array_fset(x_60, x_54, x_66);
lean_dec(x_54);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_62);
lean_dec(x_61);
if (lean_is_scalar(x_63)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_63;
}
lean_ctor_set(x_69, 0, x_5);
lean_ctor_set(x_69, 1, x_6);
x_70 = lean_array_fset(x_60, x_54, x_69);
lean_dec(x_54);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
case 1:
{
lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_58, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_73 = x_58;
} else {
 lean_dec_ref(x_58);
 x_73 = lean_box(0);
}
x_74 = lean_usize_shift_right(x_3, x_51);
x_75 = lean_usize_add(x_4, x_50);
x_76 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_1, x_72, x_74, x_75, x_5, x_6);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_array_fset(x_60, x_54, x_77);
lean_dec(x_54);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
default: 
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_6);
x_81 = lean_array_fset(x_60, x_54, x_80);
lean_dec(x_54);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_2);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; size_t x_86; uint8_t x_87; 
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(x_1, x_2, x_84, x_5, x_6);
x_86 = 7;
x_87 = lean_usize_dec_le(x_86, x_4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_85);
x_89 = lean_unsigned_to_nat(4u);
x_90 = lean_nat_dec_lt(x_88, x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_dec(x_85);
x_93 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_94 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(x_1, x_4, x_91, x_92, lean_box(0), x_84, x_93);
lean_dec(x_92);
lean_dec(x_91);
return x_94;
}
else
{
return x_85;
}
}
else
{
return x_85;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; size_t x_100; uint8_t x_101; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_2);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(x_1, x_97, x_98, x_5, x_6);
x_100 = 7;
x_101 = lean_usize_dec_le(x_100, x_4);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_99);
x_103 = lean_unsigned_to_nat(4u);
x_104 = lean_nat_dec_lt(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_dec(x_99);
x_107 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_108 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(x_1, x_4, x_105, x_106, lean_box(0), x_98, x_107);
lean_dec(x_106);
lean_dec(x_105);
return x_108;
}
else
{
return x_99;
}
}
else
{
return x_99;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_9 = lean_uint64_to_usize(x_8);
x_10 = 1;
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_1, x_6, x_9, x_10, x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_17 = lean_uint64_to_usize(x_16);
x_18 = 1;
x_19 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_1, x_14, x_17, x_18, x_3, x_4);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_15, x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__14___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__14___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__13___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__14___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__13___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__13___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__17___rarg(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_array_fget(x_3, x_6);
x_11 = lean_array_fget(x_4, x_6);
x_12 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_10);
x_13 = lean_uint64_to_usize(x_12);
x_14 = 1;
x_15 = lean_usize_sub(x_2, x_14);
x_16 = 5;
x_17 = lean_usize_mul(x_16, x_15);
x_18 = lean_usize_shift_right(x_13, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_21 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg(x_1, x_7, x_18, x_2, x_10, x_11);
x_5 = lean_box(0);
x_6 = x_20;
x_7 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__17(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__17___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__18___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = lean_array_push(x_6, x_4);
x_14 = lean_array_push(x_7, x_5);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_array_push(x_7, x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_fget(x_6, x_3);
x_19 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_2, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 0);
lean_dec(x_25);
x_26 = lean_array_fset(x_6, x_3, x_4);
x_27 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_28 = lean_array_fset(x_6, x_3, x_4);
x_29 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__18(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__18___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = 1;
x_10 = 5;
x_11 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_12 = lean_usize_land(x_3, x_11);
x_13 = lean_usize_to_nat(x_12);
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget(x_8, x_13);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_8, x_13, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
x_22 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_16);
x_23 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_20, x_21, x_5, x_6);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_array_fset(x_18, x_13, x_24);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
else
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 0, x_5);
x_26 = lean_array_fset(x_18, x_13, x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_27, x_28, x_5, x_6);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_array_fset(x_18, x_13, x_31);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_array_fset(x_18, x_13, x_33);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
}
}
case 1:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_usize_shift_right(x_3, x_10);
x_38 = lean_usize_add(x_4, x_9);
x_39 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg(x_1, x_36, x_37, x_38, x_5, x_6);
lean_ctor_set(x_16, 0, x_39);
x_40 = lean_array_fset(x_18, x_13, x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_40);
return x_2;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_16, 0);
lean_inc(x_41);
lean_dec(x_16);
x_42 = lean_usize_shift_right(x_3, x_10);
x_43 = lean_usize_add(x_4, x_9);
x_44 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg(x_1, x_41, x_42, x_43, x_5, x_6);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_array_fset(x_18, x_13, x_45);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_46);
return x_2;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_6);
x_48 = lean_array_fset(x_18, x_13, x_47);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_48);
return x_2;
}
}
}
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = 1;
x_51 = 5;
x_52 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_53 = lean_usize_land(x_3, x_52);
x_54 = lean_usize_to_nat(x_53);
x_55 = lean_array_get_size(x_49);
x_56 = lean_nat_dec_lt(x_54, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_6);
lean_dec(x_5);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_49);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_array_fget(x_49, x_54);
x_59 = lean_box(0);
x_60 = lean_array_fset(x_49, x_54, x_59);
switch (lean_obj_tag(x_58)) {
case 0:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_63 = x_58;
} else {
 lean_dec_ref(x_58);
 x_63 = lean_box(0);
}
x_64 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
x_65 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_61, x_62, x_5, x_6);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_array_fset(x_60, x_54, x_66);
lean_dec(x_54);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_62);
lean_dec(x_61);
if (lean_is_scalar(x_63)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_63;
}
lean_ctor_set(x_69, 0, x_5);
lean_ctor_set(x_69, 1, x_6);
x_70 = lean_array_fset(x_60, x_54, x_69);
lean_dec(x_54);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
case 1:
{
lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_58, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_73 = x_58;
} else {
 lean_dec_ref(x_58);
 x_73 = lean_box(0);
}
x_74 = lean_usize_shift_right(x_3, x_51);
x_75 = lean_usize_add(x_4, x_50);
x_76 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg(x_1, x_72, x_74, x_75, x_5, x_6);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_array_fset(x_60, x_54, x_77);
lean_dec(x_54);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
default: 
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_6);
x_81 = lean_array_fset(x_60, x_54, x_80);
lean_dec(x_54);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_2);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; size_t x_86; uint8_t x_87; 
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__18___rarg(x_1, x_2, x_84, x_5, x_6);
x_86 = 7;
x_87 = lean_usize_dec_le(x_86, x_4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_85);
x_89 = lean_unsigned_to_nat(4u);
x_90 = lean_nat_dec_lt(x_88, x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_dec(x_85);
x_93 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_94 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__17___rarg(x_1, x_4, x_91, x_92, lean_box(0), x_84, x_93);
lean_dec(x_92);
lean_dec(x_91);
return x_94;
}
else
{
return x_85;
}
}
else
{
return x_85;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; size_t x_100; uint8_t x_101; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_2);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__18___rarg(x_1, x_97, x_98, x_5, x_6);
x_100 = 7;
x_101 = lean_usize_dec_le(x_100, x_4);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_99);
x_103 = lean_unsigned_to_nat(4u);
x_104 = lean_nat_dec_lt(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_dec(x_99);
x_107 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_108 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__17___rarg(x_1, x_4, x_105, x_106, lean_box(0), x_98, x_107);
lean_dec(x_106);
lean_dec(x_105);
return x_108;
}
else
{
return x_99;
}
}
else
{
return x_99;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__15___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_9 = lean_uint64_to_usize(x_8);
x_10 = 1;
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg(x_1, x_6, x_9, x_10, x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_17 = lean_uint64_to_usize(x_16);
x_18 = 1;
x_19 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg(x_1, x_14, x_17, x_18, x_3, x_4);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_15, x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__15___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__21___rarg(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_array_fget(x_3, x_6);
x_11 = lean_array_fget(x_4, x_6);
x_12 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_10);
x_13 = lean_uint64_to_usize(x_12);
x_14 = 1;
x_15 = lean_usize_sub(x_2, x_14);
x_16 = 5;
x_17 = lean_usize_mul(x_16, x_15);
x_18 = lean_usize_shift_right(x_13, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_21 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg(x_1, x_7, x_18, x_2, x_10, x_11);
x_5 = lean_box(0);
x_6 = x_20;
x_7 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__21___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__22___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = lean_array_push(x_6, x_4);
x_14 = lean_array_push(x_7, x_5);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_array_push(x_7, x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_fget(x_6, x_3);
x_19 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_2, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 0);
lean_dec(x_25);
x_26 = lean_array_fset(x_6, x_3, x_4);
x_27 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_28 = lean_array_fset(x_6, x_3, x_4);
x_29 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__22(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__22___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = 1;
x_10 = 5;
x_11 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_12 = lean_usize_land(x_3, x_11);
x_13 = lean_usize_to_nat(x_12);
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget(x_8, x_13);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_8, x_13, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
x_22 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_16);
x_23 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_20, x_21, x_5, x_6);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_array_fset(x_18, x_13, x_24);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
else
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 0, x_5);
x_26 = lean_array_fset(x_18, x_13, x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_27, x_28, x_5, x_6);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_array_fset(x_18, x_13, x_31);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_array_fset(x_18, x_13, x_33);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
}
}
case 1:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_usize_shift_right(x_3, x_10);
x_38 = lean_usize_add(x_4, x_9);
x_39 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg(x_1, x_36, x_37, x_38, x_5, x_6);
lean_ctor_set(x_16, 0, x_39);
x_40 = lean_array_fset(x_18, x_13, x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_40);
return x_2;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_16, 0);
lean_inc(x_41);
lean_dec(x_16);
x_42 = lean_usize_shift_right(x_3, x_10);
x_43 = lean_usize_add(x_4, x_9);
x_44 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg(x_1, x_41, x_42, x_43, x_5, x_6);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_array_fset(x_18, x_13, x_45);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_46);
return x_2;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_6);
x_48 = lean_array_fset(x_18, x_13, x_47);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_48);
return x_2;
}
}
}
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = 1;
x_51 = 5;
x_52 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_53 = lean_usize_land(x_3, x_52);
x_54 = lean_usize_to_nat(x_53);
x_55 = lean_array_get_size(x_49);
x_56 = lean_nat_dec_lt(x_54, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_6);
lean_dec(x_5);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_49);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_array_fget(x_49, x_54);
x_59 = lean_box(0);
x_60 = lean_array_fset(x_49, x_54, x_59);
switch (lean_obj_tag(x_58)) {
case 0:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_63 = x_58;
} else {
 lean_dec_ref(x_58);
 x_63 = lean_box(0);
}
x_64 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_5, x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
x_65 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_61, x_62, x_5, x_6);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_array_fset(x_60, x_54, x_66);
lean_dec(x_54);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_62);
lean_dec(x_61);
if (lean_is_scalar(x_63)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_63;
}
lean_ctor_set(x_69, 0, x_5);
lean_ctor_set(x_69, 1, x_6);
x_70 = lean_array_fset(x_60, x_54, x_69);
lean_dec(x_54);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
case 1:
{
lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_58, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_73 = x_58;
} else {
 lean_dec_ref(x_58);
 x_73 = lean_box(0);
}
x_74 = lean_usize_shift_right(x_3, x_51);
x_75 = lean_usize_add(x_4, x_50);
x_76 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg(x_1, x_72, x_74, x_75, x_5, x_6);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_array_fset(x_60, x_54, x_77);
lean_dec(x_54);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
default: 
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_6);
x_81 = lean_array_fset(x_60, x_54, x_80);
lean_dec(x_54);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_2);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; size_t x_86; uint8_t x_87; 
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__22___rarg(x_1, x_2, x_84, x_5, x_6);
x_86 = 7;
x_87 = lean_usize_dec_le(x_86, x_4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_85);
x_89 = lean_unsigned_to_nat(4u);
x_90 = lean_nat_dec_lt(x_88, x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_dec(x_85);
x_93 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_94 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__21___rarg(x_1, x_4, x_91, x_92, lean_box(0), x_84, x_93);
lean_dec(x_92);
lean_dec(x_91);
return x_94;
}
else
{
return x_85;
}
}
else
{
return x_85;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; size_t x_100; uint8_t x_101; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_2);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__22___rarg(x_1, x_97, x_98, x_5, x_6);
x_100 = 7;
x_101 = lean_usize_dec_le(x_100, x_4);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_99);
x_103 = lean_unsigned_to_nat(4u);
x_104 = lean_nat_dec_lt(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_dec(x_99);
x_107 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_108 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__21___rarg(x_1, x_4, x_105, x_106, lean_box(0), x_98, x_107);
lean_dec(x_106);
lean_dec(x_105);
return x_108;
}
else
{
return x_99;
}
}
else
{
return x_99;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__19___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_9 = lean_uint64_to_usize(x_8);
x_10 = 1;
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg(x_1, x_6, x_9, x_10, x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_17 = lean_uint64_to_usize(x_16);
x_18 = 1;
x_19 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg(x_1, x_14, x_17, x_18, x_3, x_4);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_15, x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__19(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__19___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__23___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_box(0), x_1);
x_4 = lean_panic_fn(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__23(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__23___rarg___boxed), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.DiscrTree", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.DiscrTree.insertCore", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid key sequence", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1;
x_2 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2;
x_3 = lean_unsigned_to_nat(366u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEmpty___rarg(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_box(0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_8, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l___private_Init_Util_0__outOfBounds___rarg(x_9);
lean_inc(x_12);
lean_inc(x_3);
x_13 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg(x_1, x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_4, x_5, x_14);
lean_dec(x_4);
x_16 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg(x_1, x_3, x_12, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_4, x_5, x_18, x_17);
lean_dec(x_4);
x_20 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg(x_1, x_3, x_12, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
x_21 = lean_array_fget(x_4, x_8);
lean_inc(x_21);
lean_inc(x_3);
x_22 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg(x_1, x_3, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(1u);
x_24 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_4, x_5, x_23);
lean_dec(x_4);
x_25 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__15___rarg(x_1, x_3, x_21, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_unsigned_to_nat(1u);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_4, x_5, x_27, x_26);
lean_dec(x_4);
x_29 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__19___rarg(x_1, x_3, x_21, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4;
x_31 = l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__23___rarg(x_1, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_insertCore___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__14___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__13___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__17___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__17___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__18___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__18___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__16___rarg(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__15___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__21___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__22___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__22___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__20___rarg(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__19___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__19___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__23___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__23___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Meta_DiscrTree_insertCore___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_DiscrTree_mkPath(x_1, x_4, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_Meta_DiscrTree_insertCore___rarg(x_1, x_2, x_3, x_13, x_5);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l_Lean_Meta_DiscrTree_insertCore___rarg(x_1, x_2, x_3, x_15, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_insert___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_DiscrTree_insert___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_isRecCore(x_10, x_1);
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_isRecCore(x_15, x_1);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_array_uget(x_12, x_3);
x_14 = l_Lean_Expr_hasExprMVar(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_box(0);
x_3 = x_16;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_9);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_10);
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_empty_array_with_capacity(x_11);
lean_dec(x_11);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(uint8_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_DiscrTree_reduceDT(x_2, x_4, x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Expr_getAppFn(x_12);
switch (lean_obj_tag(x_14)) {
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_16);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_empty_array_with_capacity(x_17);
lean_dec(x_17);
x_20 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_12, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
case 2:
{
lean_dec(x_12);
if (x_3 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_22, 4);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_10);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(x_24, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_box(3);
x_31 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_box(3);
x_35 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_25, 0);
lean_dec(x_39);
x_40 = lean_box(4);
x_41 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_25, 0, x_42);
return x_25;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_dec(x_25);
x_44 = lean_box(4);
x_45 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_25);
if (x_48 == 0)
{
return x_25;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_25, 0);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_25);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = lean_box(3);
x_53 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_10, 0, x_54);
return x_10;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_55 = lean_box(4);
x_56 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_10, 0, x_57);
return x_10;
}
}
case 4:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_117; 
lean_free_object(x_10);
x_58 = lean_ctor_get(x_14, 0);
lean_inc(x_58);
lean_dec(x_14);
x_59 = l_Lean_Meta_getConfig(x_5, x_6, x_7, x_8, x_13);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_117 = lean_ctor_get_uint8(x_60, 4);
lean_dec(x_60);
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = 0;
x_62 = x_118;
goto block_116;
}
else
{
uint8_t x_119; 
x_119 = l_Lean_Expr_hasExprMVar(x_12);
x_62 = x_119;
goto block_116;
}
block_116:
{
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_box(0);
x_64 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_12, x_1, x_58, x_63, x_5, x_6, x_7, x_8, x_61);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_inc(x_58);
x_65 = l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(x_58, x_5, x_6, x_7, x_8, x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_st_ref_get(x_8, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Meta_isMatcherAppCore_x3f(x_72, x_12);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_inc(x_58);
x_74 = l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(x_58, x_5, x_6, x_7, x_8, x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_box(0);
x_79 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_12, x_1, x_58, x_78, x_5, x_6, x_7, x_8, x_77);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_58);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_dec(x_74);
x_81 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_80);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_81);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; lean_object* x_100; size_t x_101; lean_object* x_102; lean_object* x_103; 
x_86 = lean_ctor_get(x_73, 0);
lean_inc(x_86);
lean_dec(x_73);
x_87 = lean_unsigned_to_nat(0u);
x_88 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_87);
x_89 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
lean_inc(x_88);
x_90 = lean_mk_array(x_88, x_89);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_sub(x_88, x_91);
lean_dec(x_88);
lean_inc(x_12);
x_93 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_90, x_92);
x_94 = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(x_86);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
lean_dec(x_86);
x_96 = lean_nat_add(x_94, x_95);
lean_dec(x_95);
x_97 = l_Array_toSubarray___rarg(x_93, x_94, x_96);
x_98 = lean_ctor_get(x_97, 2);
lean_inc(x_98);
x_99 = lean_usize_of_nat(x_98);
lean_dec(x_98);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
x_101 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_102 = lean_box(0);
x_103 = l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2(x_97, x_99, x_101, x_102, x_5, x_6, x_7, x_8, x_71);
lean_dec(x_97);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_12, x_1, x_58, x_102, x_5, x_6, x_7, x_8, x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_105;
}
else
{
uint8_t x_106; 
lean_dec(x_58);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
return x_103;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_103, 0);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_103);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_58);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_110 = lean_ctor_get(x_65, 1);
lean_inc(x_110);
lean_dec(x_65);
x_111 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_110);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_111);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
case 7:
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_120 = lean_ctor_get(x_14, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_14, 2);
lean_inc(x_121);
lean_dec(x_14);
x_122 = l_Lean_Expr_hasLooseBVars(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_box(5);
x_124 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
x_125 = lean_array_push(x_124, x_120);
x_126 = lean_array_push(x_125, x_121);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_10, 0, x_127);
return x_10;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_121);
lean_dec(x_120);
x_128 = lean_box(4);
x_129 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_10, 0, x_130);
return x_10;
}
}
case 9:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_131 = lean_ctor_get(x_14, 0);
lean_inc(x_131);
lean_dec(x_14);
x_132 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_10, 0, x_134);
return x_10;
}
case 11:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_135 = lean_ctor_get(x_14, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_14, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_14, 2);
lean_inc(x_137);
lean_dec(x_14);
x_138 = lean_unsigned_to_nat(0u);
x_139 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_138);
lean_inc(x_139);
x_140 = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(x_140, 0, x_135);
lean_ctor_set(x_140, 1, x_136);
lean_ctor_set(x_140, 2, x_139);
x_141 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___closed__1;
x_142 = lean_array_push(x_141, x_137);
x_143 = lean_mk_empty_array_with_capacity(x_139);
lean_dec(x_139);
x_144 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_12, x_143);
x_145 = l_Array_append___rarg(x_142, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_10, 0, x_146);
return x_10;
}
default: 
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_147 = lean_box(4);
x_148 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_10, 0, x_149);
return x_10;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_10, 0);
x_151 = lean_ctor_get(x_10, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_10);
x_152 = l_Lean_Expr_getAppFn(x_150);
switch (lean_obj_tag(x_152)) {
case 1:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_unsigned_to_nat(0u);
x_155 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_150, x_154);
lean_inc(x_155);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_mk_empty_array_with_capacity(x_155);
lean_dec(x_155);
x_158 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_150, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_151);
return x_160;
}
case 2:
{
lean_dec(x_150);
if (x_3 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_ctor_get(x_5, 0);
lean_inc(x_161);
x_162 = lean_ctor_get_uint8(x_161, 4);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_152, 0);
lean_inc(x_163);
lean_dec(x_152);
x_164 = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(x_163, x_5, x_6, x_7, x_8, x_151);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_unbox(x_165);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
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
x_169 = lean_box(3);
x_170 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
if (lean_is_scalar(x_168)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_168;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_173 = lean_ctor_get(x_164, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_174 = x_164;
} else {
 lean_dec_ref(x_164);
 x_174 = lean_box(0);
}
x_175 = lean_box(4);
x_176 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
if (lean_is_scalar(x_174)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_174;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_173);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_164, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_164, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_181 = x_164;
} else {
 lean_dec_ref(x_164);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_152);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_183 = lean_box(3);
x_184 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_151);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_152);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_187 = lean_box(4);
x_188 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_151);
return x_190;
}
}
case 4:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_250; 
x_191 = lean_ctor_get(x_152, 0);
lean_inc(x_191);
lean_dec(x_152);
x_192 = l_Lean_Meta_getConfig(x_5, x_6, x_7, x_8, x_151);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_250 = lean_ctor_get_uint8(x_193, 4);
lean_dec(x_193);
if (x_250 == 0)
{
uint8_t x_251; 
x_251 = 0;
x_195 = x_251;
goto block_249;
}
else
{
uint8_t x_252; 
x_252 = l_Lean_Expr_hasExprMVar(x_150);
x_195 = x_252;
goto block_249;
}
block_249:
{
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_box(0);
x_197 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_150, x_1, x_191, x_196, x_5, x_6, x_7, x_8, x_194);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_inc(x_191);
x_198 = l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(x_191, x_5, x_6, x_7, x_8, x_194);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_unbox(x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
x_202 = lean_st_ref_get(x_8, x_201);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
lean_dec(x_203);
x_206 = l_Lean_Meta_isMatcherAppCore_x3f(x_205, x_150);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
lean_inc(x_191);
x_207 = l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(x_191, x_5, x_6, x_7, x_8, x_204);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
lean_dec(x_207);
x_211 = lean_box(0);
x_212 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_150, x_1, x_191, x_211, x_5, x_6, x_7, x_8, x_210);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_191);
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_213 = lean_ctor_get(x_207, 1);
lean_inc(x_213);
lean_dec(x_207);
x_214 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_213);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_217 = x_214;
} else {
 lean_dec_ref(x_214);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; size_t x_232; lean_object* x_233; size_t x_234; lean_object* x_235; lean_object* x_236; 
x_219 = lean_ctor_get(x_206, 0);
lean_inc(x_219);
lean_dec(x_206);
x_220 = lean_unsigned_to_nat(0u);
x_221 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_150, x_220);
x_222 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
lean_inc(x_221);
x_223 = lean_mk_array(x_221, x_222);
x_224 = lean_unsigned_to_nat(1u);
x_225 = lean_nat_sub(x_221, x_224);
lean_dec(x_221);
lean_inc(x_150);
x_226 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_150, x_223, x_225);
x_227 = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(x_219);
x_228 = lean_ctor_get(x_219, 1);
lean_inc(x_228);
lean_dec(x_219);
x_229 = lean_nat_add(x_227, x_228);
lean_dec(x_228);
x_230 = l_Array_toSubarray___rarg(x_226, x_227, x_229);
x_231 = lean_ctor_get(x_230, 2);
lean_inc(x_231);
x_232 = lean_usize_of_nat(x_231);
lean_dec(x_231);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
x_234 = lean_usize_of_nat(x_233);
lean_dec(x_233);
x_235 = lean_box(0);
x_236 = l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2(x_230, x_232, x_234, x_235, x_5, x_6, x_7, x_8, x_204);
lean_dec(x_230);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_238 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_150, x_1, x_191, x_235, x_5, x_6, x_7, x_8, x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_191);
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_241 = x_236;
} else {
 lean_dec_ref(x_236);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_191);
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_243 = lean_ctor_get(x_198, 1);
lean_inc(x_243);
lean_dec(x_198);
x_244 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
}
}
case 7:
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; 
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_253 = lean_ctor_get(x_152, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_152, 2);
lean_inc(x_254);
lean_dec(x_152);
x_255 = l_Lean_Expr_hasLooseBVars(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_256 = lean_box(5);
x_257 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
x_258 = lean_array_push(x_257, x_253);
x_259 = lean_array_push(x_258, x_254);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_256);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_151);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_254);
lean_dec(x_253);
x_262 = lean_box(4);
x_263 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_151);
return x_265;
}
}
case 9:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_266 = lean_ctor_get(x_152, 0);
lean_inc(x_266);
lean_dec(x_152);
x_267 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_267, 0, x_266);
x_268 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_151);
return x_270;
}
case 11:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_271 = lean_ctor_get(x_152, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_152, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_152, 2);
lean_inc(x_273);
lean_dec(x_152);
x_274 = lean_unsigned_to_nat(0u);
x_275 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_150, x_274);
lean_inc(x_275);
x_276 = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(x_276, 0, x_271);
lean_ctor_set(x_276, 1, x_272);
lean_ctor_set(x_276, 2, x_275);
x_277 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___closed__1;
x_278 = lean_array_push(x_277, x_273);
x_279 = lean_mk_empty_array_with_capacity(x_275);
lean_dec(x_275);
x_280 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_150, x_279);
x_281 = l_Array_append___rarg(x_278, x_280);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_276);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_151);
return x_283;
}
default: 
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_284 = lean_box(4);
x_285 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_151);
return x_287;
}
}
}
}
else
{
uint8_t x_288; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_288 = !lean_is_exclusive(x_10);
if (x_288 == 0)
{
return x_10;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_10, 0);
x_290 = lean_ctor_get(x_10, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_10);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_10, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs(x_9, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(x_9, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(3);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1___rarg(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Meta_DiscrTree_mkPath___closed__1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_DiscrTree_mkPath___closed__1;
x_9 = l_Array_append___rarg(x_8, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_nat_add(x_6, x_7);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
lean_inc(x_5);
x_13 = lean_array_get(x_5, x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_7);
x_17 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_15, x_14);
lean_dec(x_14);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_13);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_12, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_12, x_21);
lean_dec(x_12);
x_2 = lean_box(0);
x_7 = x_22;
goto _start;
}
else
{
lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_box(0);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_12, x_25);
lean_dec(x_12);
x_2 = lean_box(0);
x_6 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_get_size(x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_8);
lean_dec(x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1(x_1, lean_box(0), x_14, x_3, x_7, x_11, x_10);
lean_dec(x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_12 = x_3;
} else {
 lean_dec_ref(x_3);
 x_12 = lean_box(0);
}
x_13 = l_Array_isEmpty___rarg(x_2);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_10);
x_14 = l_Array_isEmpty___rarg(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_15 = l_Lean_instInhabitedExpr;
x_16 = l_Array_back___rarg(x_15, x_2);
x_17 = lean_array_pop(x_2);
x_171 = lean_box(0);
x_172 = lean_unsigned_to_nat(0u);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_array_get_size(x_11);
x_177 = lean_nat_dec_lt(x_172, x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; 
x_178 = l___private_Init_Util_0__outOfBounds___rarg(x_175);
x_18 = x_178;
goto block_170;
}
else
{
lean_object* x_179; 
lean_dec(x_175);
x_179 = lean_array_fget(x_11, x_172);
x_18 = x_179;
goto block_170;
}
block_170:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = 1;
x_20 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_16, x_19, x_20, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_27 = x_22;
} else {
 lean_dec_ref(x_22);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
x_29 = lean_box(3);
x_30 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_dec(x_18);
x_31 = x_4;
x_32 = x_23;
goto block_157;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_18, 1);
lean_inc(x_158);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_159 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(x_1, x_17, x_158, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_31 = x_160;
x_32 = x_161;
goto block_157;
}
else
{
uint8_t x_162; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_162 = !lean_is_exclusive(x_159);
if (x_162 == 0)
{
return x_159;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_159, 0);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_159);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
block_157:
{
lean_object* x_33; 
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_12);
x_65 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_25);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_get_size(x_11);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_sub(x_68, x_69);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_lt(x_71, x_68);
lean_dec(x_68);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_31);
lean_ctor_set(x_73, 1, x_32);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_box(0);
x_75 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg(x_1, x_74, x_11, x_67, x_71, x_70);
lean_dec(x_11);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_31);
lean_ctor_set(x_76, 1, x_32);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Array_append___rarg(x_17, x_26);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_2 = x_78;
x_3 = x_79;
x_4 = x_31;
x_9 = x_32;
goto _start;
}
}
}
case 1:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_12);
x_81 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_25);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_array_get_size(x_11);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_sub(x_84, x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_dec_lt(x_87, x_84);
lean_dec(x_84);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_86);
lean_dec(x_83);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_31);
lean_ctor_set(x_89, 1, x_32);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_box(0);
x_91 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg(x_1, x_90, x_11, x_83, x_87, x_86);
lean_dec(x_11);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_31);
lean_ctor_set(x_92, 1, x_32);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Array_append___rarg(x_17, x_26);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_2 = x_94;
x_3 = x_95;
x_4 = x_31;
x_9 = x_32;
goto _start;
}
}
}
case 2:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_12);
x_97 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_25);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_array_get_size(x_11);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_sub(x_100, x_101);
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_nat_dec_lt(x_103, x_100);
lean_dec(x_100);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_102);
lean_dec(x_99);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_31);
lean_ctor_set(x_105, 1, x_32);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_box(0);
x_107 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg(x_1, x_106, x_11, x_99, x_103, x_102);
lean_dec(x_11);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_31);
lean_ctor_set(x_108, 1, x_32);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Array_append___rarg(x_17, x_26);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_2 = x_110;
x_3 = x_111;
x_4 = x_31;
x_9 = x_32;
goto _start;
}
}
}
case 3:
{
lean_object* x_113; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_31);
lean_ctor_set(x_113, 1, x_32);
return x_113;
}
case 4:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_12);
x_114 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_25);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_array_get_size(x_11);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_sub(x_117, x_118);
x_120 = lean_unsigned_to_nat(0u);
x_121 = lean_nat_dec_lt(x_120, x_117);
lean_dec(x_117);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_119);
lean_dec(x_116);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_31);
lean_ctor_set(x_122, 1, x_32);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_box(0);
x_124 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg(x_1, x_123, x_11, x_116, x_120, x_119);
lean_dec(x_11);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_31);
lean_ctor_set(x_125, 1, x_32);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Array_append___rarg(x_17, x_26);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_2 = x_127;
x_3 = x_128;
x_4 = x_31;
x_9 = x_32;
goto _start;
}
}
}
case 5:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_130 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_25);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_array_get_size(x_11);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_sub(x_133, x_134);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_lt(x_136, x_133);
lean_dec(x_133);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_135);
lean_dec(x_132);
x_138 = lean_box(0);
x_33 = x_138;
goto block_64;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_box(0);
x_140 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg(x_1, x_139, x_11, x_132, x_136, x_135);
x_33 = x_140;
goto block_64;
}
}
default: 
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_12);
x_141 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_25);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_array_get_size(x_11);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_sub(x_144, x_145);
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_nat_dec_lt(x_147, x_144);
lean_dec(x_144);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec(x_146);
lean_dec(x_143);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_31);
lean_ctor_set(x_149, 1, x_32);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_box(0);
x_151 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg(x_1, x_150, x_11, x_143, x_147, x_146);
lean_dec(x_11);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_31);
lean_ctor_set(x_152, 1, x_32);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Array_append___rarg(x_17, x_26);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_2 = x_154;
x_3 = x_155;
x_4 = x_31;
x_9 = x_32;
goto _start;
}
}
}
}
block_64:
{
lean_object* x_34; lean_object* x_35; 
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_26);
x_34 = x_31;
x_35 = x_32;
goto block_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_33, 0);
lean_inc(x_54);
lean_dec(x_33);
lean_inc(x_17);
x_55 = l_Array_append___rarg(x_17, x_26);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(x_1, x_55, x_56, x_31, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_34 = x_58;
x_35 = x_59;
goto block_53;
}
else
{
uint8_t x_60; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_57);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
block_53:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_36 = lean_box(4);
x_37 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_12)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_12;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_37);
if (lean_is_scalar(x_27)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_27;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_get_size(x_11);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_sub(x_40, x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_40);
lean_dec(x_40);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_24)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_24;
}
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_35);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
x_47 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg(x_1, x_46, x_11, x_39, x_43, x_42);
lean_dec(x_11);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_24)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_24;
}
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set(x_48, 1, x_35);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_24);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Array_append___rarg(x_17, x_37);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_2 = x_50;
x_3 = x_51;
x_4 = x_34;
x_9 = x_35;
goto _start;
}
}
}
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_166 = !lean_is_exclusive(x_21);
if (x_166 == 0)
{
return x_21;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_21, 0);
x_168 = lean_ctor_get(x_21, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_21);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
else
{
lean_object* x_180; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_4);
lean_ctor_set(x_180, 1, x_9);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_181 = l_Array_append___rarg(x_4, x_10);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_9);
return x_182;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1___rarg(x_1, x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(x_1, x_4, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchCore___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = 2;
lean_ctor_set_uint8(x_11, 5, x_13);
x_14 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_3, x_14, x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_17)) {
case 3:
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
lean_ctor_set(x_16, 1, x_9);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
lean_ctor_set(x_16, 1, x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_26 = x_15;
} else {
 lean_dec_ref(x_15);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_9);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
case 5:
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_dec(x_15);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_16, 1);
x_32 = lean_ctor_get(x_16, 0);
lean_dec(x_32);
x_33 = lean_box(4);
x_34 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_35 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_33, x_34, x_9, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_17, x_31, x_36, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_ctor_set(x_16, 1, x_40);
lean_ctor_set(x_38, 0, x_16);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
lean_ctor_set(x_16, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_free_object(x_16);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_16);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_35, 0);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_35);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_dec(x_16);
x_53 = lean_box(4);
x_54 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_55 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_53, x_54, x_9, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_17, x_52, x_56, x_4, x_5, x_6, x_7, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_17);
lean_ctor_set(x_62, 1, x_59);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_66 = x_58;
} else {
 lean_dec_ref(x_58);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_52);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_68 = lean_ctor_get(x_55, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_55, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_70 = x_55;
} else {
 lean_dec_ref(x_55);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
default: 
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_15, 1);
lean_inc(x_72);
lean_dec(x_15);
x_73 = !lean_is_exclusive(x_16);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_16, 1);
x_75 = lean_ctor_get(x_16, 0);
lean_dec(x_75);
lean_inc(x_17);
x_76 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_17, x_74, x_9, x_4, x_5, x_6, x_7, x_72);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_ctor_set(x_16, 1, x_78);
lean_ctor_set(x_76, 0, x_16);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_76, 0);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_76);
lean_ctor_set(x_16, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_16);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_free_object(x_16);
lean_dec(x_17);
x_82 = !lean_is_exclusive(x_76);
if (x_82 == 0)
{
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_76, 0);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_76);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_16, 1);
lean_inc(x_86);
lean_dec(x_16);
lean_inc(x_17);
x_87 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_17, x_86, x_9, x_4, x_5, x_6, x_7, x_72);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_17);
lean_ctor_set(x_91, 1, x_88);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_17);
x_93 = lean_ctor_get(x_87, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_95 = x_87;
} else {
 lean_dec_ref(x_87);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_4);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_15);
if (x_97 == 0)
{
return x_15;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_15, 0);
x_99 = lean_ctor_get(x_15, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_15);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_101 = lean_ctor_get_uint8(x_11, 0);
x_102 = lean_ctor_get_uint8(x_11, 1);
x_103 = lean_ctor_get_uint8(x_11, 2);
x_104 = lean_ctor_get_uint8(x_11, 3);
x_105 = lean_ctor_get_uint8(x_11, 4);
x_106 = lean_ctor_get_uint8(x_11, 6);
x_107 = lean_ctor_get_uint8(x_11, 7);
x_108 = lean_ctor_get_uint8(x_11, 8);
x_109 = lean_ctor_get_uint8(x_11, 9);
x_110 = lean_ctor_get_uint8(x_11, 10);
x_111 = lean_ctor_get_uint8(x_11, 11);
x_112 = lean_ctor_get_uint8(x_11, 12);
lean_dec(x_11);
x_113 = 2;
x_114 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_114, 0, x_101);
lean_ctor_set_uint8(x_114, 1, x_102);
lean_ctor_set_uint8(x_114, 2, x_103);
lean_ctor_set_uint8(x_114, 3, x_104);
lean_ctor_set_uint8(x_114, 4, x_105);
lean_ctor_set_uint8(x_114, 5, x_113);
lean_ctor_set_uint8(x_114, 6, x_106);
lean_ctor_set_uint8(x_114, 7, x_107);
lean_ctor_set_uint8(x_114, 8, x_108);
lean_ctor_set_uint8(x_114, 9, x_109);
lean_ctor_set_uint8(x_114, 10, x_110);
lean_ctor_set_uint8(x_114, 11, x_111);
lean_ctor_set_uint8(x_114, 12, x_112);
lean_ctor_set(x_4, 0, x_114);
x_115 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_116 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_3, x_115, x_115, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
switch (lean_obj_tag(x_118)) {
case 3:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_121 = x_116;
} else {
 lean_dec_ref(x_116);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_9);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
case 5:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_116, 1);
lean_inc(x_124);
lean_dec(x_116);
x_125 = lean_ctor_get(x_117, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_126 = x_117;
} else {
 lean_dec_ref(x_117);
 x_126 = lean_box(0);
}
x_127 = lean_box(4);
x_128 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_129 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_127, x_128, x_9, x_4, x_5, x_6, x_7, x_124);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_118, x_125, x_130, x_4, x_5, x_6, x_7, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_126;
}
lean_ctor_set(x_136, 0, x_118);
lean_ctor_set(x_136, 1, x_133);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_126);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_142 = lean_ctor_get(x_129, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_129, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_144 = x_129;
} else {
 lean_dec_ref(x_129);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
default: 
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_116, 1);
lean_inc(x_146);
lean_dec(x_116);
x_147 = lean_ctor_get(x_117, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_148 = x_117;
} else {
 lean_dec_ref(x_117);
 x_148 = lean_box(0);
}
lean_inc(x_118);
x_149 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_118, x_147, x_9, x_4, x_5, x_6, x_7, x_146);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_148;
}
lean_ctor_set(x_153, 0, x_118);
lean_ctor_set(x_153, 1, x_150);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_148);
lean_dec(x_118);
x_155 = lean_ctor_get(x_149, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_149, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_157 = x_149;
} else {
 lean_dec_ref(x_149);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_4);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_159 = lean_ctor_get(x_116, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_116, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_161 = x_116;
} else {
 lean_dec_ref(x_116);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
x_163 = lean_ctor_get(x_4, 0);
x_164 = lean_ctor_get(x_4, 1);
x_165 = lean_ctor_get(x_4, 2);
x_166 = lean_ctor_get(x_4, 3);
x_167 = lean_ctor_get(x_4, 4);
x_168 = lean_ctor_get(x_4, 5);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_4);
x_169 = lean_ctor_get_uint8(x_163, 0);
x_170 = lean_ctor_get_uint8(x_163, 1);
x_171 = lean_ctor_get_uint8(x_163, 2);
x_172 = lean_ctor_get_uint8(x_163, 3);
x_173 = lean_ctor_get_uint8(x_163, 4);
x_174 = lean_ctor_get_uint8(x_163, 6);
x_175 = lean_ctor_get_uint8(x_163, 7);
x_176 = lean_ctor_get_uint8(x_163, 8);
x_177 = lean_ctor_get_uint8(x_163, 9);
x_178 = lean_ctor_get_uint8(x_163, 10);
x_179 = lean_ctor_get_uint8(x_163, 11);
x_180 = lean_ctor_get_uint8(x_163, 12);
if (lean_is_exclusive(x_163)) {
 x_181 = x_163;
} else {
 lean_dec_ref(x_163);
 x_181 = lean_box(0);
}
x_182 = 2;
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 0, 13);
} else {
 x_183 = x_181;
}
lean_ctor_set_uint8(x_183, 0, x_169);
lean_ctor_set_uint8(x_183, 1, x_170);
lean_ctor_set_uint8(x_183, 2, x_171);
lean_ctor_set_uint8(x_183, 3, x_172);
lean_ctor_set_uint8(x_183, 4, x_173);
lean_ctor_set_uint8(x_183, 5, x_182);
lean_ctor_set_uint8(x_183, 6, x_174);
lean_ctor_set_uint8(x_183, 7, x_175);
lean_ctor_set_uint8(x_183, 8, x_176);
lean_ctor_set_uint8(x_183, 9, x_177);
lean_ctor_set_uint8(x_183, 10, x_178);
lean_ctor_set_uint8(x_183, 11, x_179);
lean_ctor_set_uint8(x_183, 12, x_180);
x_184 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_164);
lean_ctor_set(x_184, 2, x_165);
lean_ctor_set(x_184, 3, x_166);
lean_ctor_set(x_184, 4, x_167);
lean_ctor_set(x_184, 5, x_168);
x_185 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_184);
x_186 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_3, x_185, x_185, x_184, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
switch (lean_obj_tag(x_188)) {
case 3:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_184);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_191 = x_186;
} else {
 lean_dec_ref(x_186);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_189;
}
lean_ctor_set(x_192, 0, x_188);
lean_ctor_set(x_192, 1, x_9);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
case 5:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_194 = lean_ctor_get(x_186, 1);
lean_inc(x_194);
lean_dec(x_186);
x_195 = lean_ctor_get(x_187, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_196 = x_187;
} else {
 lean_dec_ref(x_187);
 x_196 = lean_box(0);
}
x_197 = lean_box(4);
x_198 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_184);
lean_inc(x_2);
x_199 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_197, x_198, x_9, x_184, x_5, x_6, x_7, x_194);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_188, x_195, x_200, x_184, x_5, x_6, x_7, x_201);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_196;
}
lean_ctor_set(x_206, 0, x_188);
lean_ctor_set(x_206, 1, x_203);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_196);
x_208 = lean_ctor_get(x_202, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_202, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_210 = x_202;
} else {
 lean_dec_ref(x_202);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_184);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_212 = lean_ctor_get(x_199, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_199, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_214 = x_199;
} else {
 lean_dec_ref(x_199);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
default: 
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_186, 1);
lean_inc(x_216);
lean_dec(x_186);
x_217 = lean_ctor_get(x_187, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_218 = x_187;
} else {
 lean_dec_ref(x_187);
 x_218 = lean_box(0);
}
lean_inc(x_188);
x_219 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_188, x_217, x_9, x_184, x_5, x_6, x_7, x_216);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_218;
}
lean_ctor_set(x_223, 0, x_188);
lean_ctor_set(x_223, 1, x_220);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_218);
lean_dec(x_188);
x_225 = lean_ctor_get(x_219, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_219, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_227 = x_219;
} else {
 lean_dec_ref(x_219);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_229 = lean_ctor_get(x_186, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_186, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_231 = x_186;
} else {
 lean_dec_ref(x_186);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchCore___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchCore___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchCore___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatch___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_DiscrTree_getMatch___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__3___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__2___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__3___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__2___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__6___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__6___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__5___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__6___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__4___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__5___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__9___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__9___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__8___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__9___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__8___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__7___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__8___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__7___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
lean_ctor_set(x_3, 1, x_15);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__1___rarg(x_1, x_2, x_3);
if (lean_obj_tag(x_16) == 0)
{
goto _start;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_3);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_25, x_28);
lean_dec(x_25);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_30);
lean_inc(x_2);
x_31 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__1___rarg(x_1, x_2, x_30);
if (lean_obj_tag(x_31) == 0)
{
x_3 = x_30;
goto _start;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_2);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
}
else
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
x_36 = 0;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_8);
return x_38;
}
}
}
case 1:
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_3);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_41, x_44);
lean_dec(x_41);
lean_ctor_set(x_3, 1, x_45);
lean_inc(x_3);
lean_inc(x_2);
x_46 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__4___rarg(x_1, x_2, x_3);
if (lean_obj_tag(x_46) == 0)
{
goto _start;
}
else
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_48 = 1;
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_8);
return x_50;
}
}
else
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_3);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_2);
x_51 = 0;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_8);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_3, 0);
x_55 = lean_ctor_get(x_3, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_3);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_eq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_55, x_58);
lean_dec(x_55);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
lean_inc(x_60);
lean_inc(x_2);
x_61 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__4___rarg(x_1, x_2, x_60);
if (lean_obj_tag(x_61) == 0)
{
x_3 = x_60;
goto _start;
}
else
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_2);
x_63 = 1;
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_8);
return x_65;
}
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_2);
x_66 = 0;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
return x_68;
}
}
}
case 6:
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_3);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_3, 0);
x_71 = lean_ctor_get(x_3, 1);
x_72 = lean_ctor_get(x_3, 2);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_nat_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_72, x_75);
lean_dec(x_72);
lean_ctor_set(x_3, 2, x_76);
lean_inc(x_3);
lean_inc(x_2);
x_77 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__7___rarg(x_1, x_2, x_3);
if (lean_obj_tag(x_77) == 0)
{
goto _start;
}
else
{
uint8_t x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_77);
lean_dec(x_3);
lean_dec(x_2);
x_79 = 1;
x_80 = lean_box(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_8);
return x_81;
}
}
else
{
uint8_t x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_3);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_2);
x_82 = 0;
x_83 = lean_box(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_8);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_3, 0);
x_86 = lean_ctor_get(x_3, 1);
x_87 = lean_ctor_get(x_3, 2);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_3);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_sub(x_87, x_90);
lean_dec(x_87);
x_92 = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_86);
lean_ctor_set(x_92, 2, x_91);
lean_inc(x_92);
lean_inc(x_2);
x_93 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__7___rarg(x_1, x_2, x_92);
if (lean_obj_tag(x_93) == 0)
{
x_3 = x_92;
goto _start;
}
else
{
uint8_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_2);
x_95 = 1;
x_96 = lean_box(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_8);
return x_97;
}
}
else
{
uint8_t x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_2);
x_98 = 0;
x_99 = lean_box(x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_8);
return x_100;
}
}
}
default: 
{
uint8_t x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_3);
lean_dec(x_2);
x_101 = 0;
x_102 = lean_box(x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_8);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__3___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__2___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__6___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__5___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__4___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__9___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__8___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__7___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_go___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_go___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_go___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_DiscrTree_getMatch___rarg(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_array_get_size(x_13);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_4);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_go___spec__1___rarg(x_4, x_16, x_17, x_13);
x_19 = l_Array_append___rarg(x_5, x_18);
x_20 = l_Lean_Expr_isApp(x_3);
if (x_20 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_11);
x_21 = l_Lean_Expr_appFn_x21(x_3);
lean_dec(x_3);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_dec(x_4);
x_3 = x_21;
x_4 = x_23;
x_5 = x_19;
x_10 = x_14;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_array_get_size(x_25);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
lean_inc(x_4);
x_30 = l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_go___spec__1___rarg(x_4, x_28, x_29, x_25);
x_31 = l_Array_append___rarg(x_5, x_30);
x_32 = l_Lean_Expr_isApp(x_3);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_Expr_appFn_x21(x_3);
lean_dec(x_3);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_3 = x_34;
x_4 = x_36;
x_5 = x_31;
x_10 = x_26;
goto _start;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatchWithExtra_go___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_go___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_go___spec__1___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_DiscrTree_getMatchWithExtra_go___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1___rarg(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchCore___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1___rarg(x_16, x_17, x_14);
x_19 = l_Lean_Expr_isApp(x_3);
if (x_19 == 0)
{
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_9);
lean_inc(x_2);
x_20 = l_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___rarg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = l_Lean_Expr_appFn_x21(x_3);
lean_dec(x_3);
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_Meta_DiscrTree_getMatchWithExtra_go___rarg(x_1, x_2, x_28, x_29, x_18, x_4, x_5, x_6, x_7, x_27);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_array_get_size(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1___rarg(x_36, x_37, x_34);
x_39 = l_Lean_Expr_isApp(x_3);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_2);
x_41 = l_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___rarg(x_1, x_2, x_33, x_4, x_5, x_6, x_7, x_32);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_45 = x_41;
} else {
 lean_dec_ref(x_41);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_dec(x_41);
x_48 = l_Lean_Expr_appFn_x21(x_3);
lean_dec(x_3);
x_49 = lean_unsigned_to_nat(1u);
x_50 = l_Lean_Meta_DiscrTree_getMatchWithExtra_go___rarg(x_1, x_2, x_48, x_49, x_38, x_4, x_5, x_6, x_7, x_47);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_9);
if (x_51 == 0)
{
return x_9;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_9, 0);
x_53 = lean_ctor_get(x_9, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_9);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_DiscrTree_Key_arity___rarg(x_14);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_17 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_16, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_6 = x_18;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_4);
x_12 = lean_array_get(x_4, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_5, x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_uget(x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_DiscrTree_Key_arity___rarg(x_15);
lean_dec(x_15);
x_18 = lean_nat_add(x_3, x_17);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_19 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_18, x_2, x_16, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_7 = x_20;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg___boxed), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify_process___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_2, x_13);
lean_dec(x_2);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l_Array_isEmpty___rarg(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_lt(x_11, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(x_1, x_3, x_14, x_15, x_22, x_23, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_15);
lean_dec(x_14);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_2);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_28 = x_4;
} else {
 lean_dec_ref(x_4);
 x_28 = lean_box(0);
}
x_29 = l_Array_isEmpty___rarg(x_3);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_26);
x_30 = l_Array_isEmpty___rarg(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = l_Lean_instInhabitedExpr;
x_32 = l_Array_back___rarg(x_31, x_3);
x_33 = lean_array_pop(x_3);
x_34 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_35 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_32, x_34, x_34, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
switch (lean_obj_tag(x_37)) {
case 0:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_36, 1);
x_42 = lean_ctor_get(x_36, 0);
lean_dec(x_42);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_11);
x_45 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
lean_ctor_set(x_36, 1, x_45);
lean_ctor_set(x_36, 0, x_44);
x_46 = lean_array_get_size(x_27);
x_47 = lean_nat_dec_lt(x_11, x_46);
x_48 = lean_box(3);
if (x_47 == 0)
{
lean_object* x_77; 
x_77 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_49 = x_77;
goto block_76;
}
else
{
lean_object* x_78; 
lean_dec(x_36);
x_78 = lean_array_fget(x_27, x_11);
x_49 = x_78;
goto block_76;
}
block_76:
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_50, x_48);
lean_dec(x_50);
if (x_51 == 0)
{
lean_dec(x_49);
x_52 = x_5;
x_53 = x_38;
goto block_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_49, 1);
lean_inc(x_68);
lean_dec(x_49);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_69 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_68, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_52 = x_70;
x_53 = x_71;
goto block_67;
}
else
{
uint8_t x_72; 
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
block_67:
{
if (x_47 == 0)
{
lean_object* x_54; 
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_39)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_39;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_28;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_37);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_46, x_58);
lean_dec(x_46);
x_60 = lean_box(0);
x_61 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(x_1, x_60, x_27, x_57, x_11, x_59);
lean_dec(x_27);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_39)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_39;
}
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_53);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_39);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Array_append___rarg(x_33, x_41);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_2 = x_11;
x_3 = x_64;
x_4 = x_65;
x_5 = x_52;
x_10 = x_53;
goto _start;
}
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_36, 1);
lean_inc(x_79);
lean_dec(x_36);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_11);
x_82 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_array_get_size(x_27);
x_85 = lean_nat_dec_lt(x_11, x_84);
x_86 = lean_box(3);
if (x_85 == 0)
{
lean_object* x_115; 
x_115 = l___private_Init_Util_0__outOfBounds___rarg(x_83);
x_87 = x_115;
goto block_114;
}
else
{
lean_object* x_116; 
lean_dec(x_83);
x_116 = lean_array_fget(x_27, x_11);
x_87 = x_116;
goto block_114;
}
block_114:
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_88, x_86);
lean_dec(x_88);
if (x_89 == 0)
{
lean_dec(x_87);
x_90 = x_5;
x_91 = x_38;
goto block_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_87, 1);
lean_inc(x_106);
lean_dec(x_87);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_107 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_106, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_90 = x_108;
x_91 = x_109;
goto block_105;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_84);
lean_dec(x_79);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_112 = x_107;
} else {
 lean_dec_ref(x_107);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
block_105:
{
if (x_85 == 0)
{
lean_object* x_92; 
lean_dec(x_84);
lean_dec(x_79);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_39)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_39;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_28;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_37);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_sub(x_84, x_96);
lean_dec(x_84);
x_98 = lean_box(0);
x_99 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(x_1, x_98, x_27, x_95, x_11, x_97);
lean_dec(x_27);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
lean_dec(x_79);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_39)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_39;
}
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_91);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_39);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Array_append___rarg(x_33, x_79);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_2 = x_11;
x_3 = x_102;
x_4 = x_103;
x_5 = x_90;
x_10 = x_91;
goto _start;
}
}
}
}
}
}
case 1:
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_35, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_118 = x_35;
} else {
 lean_dec_ref(x_35);
 x_118 = lean_box(0);
}
x_119 = !lean_is_exclusive(x_36);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_36, 1);
x_121 = lean_ctor_get(x_36, 0);
lean_dec(x_121);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_11);
x_124 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
lean_ctor_set(x_36, 1, x_124);
lean_ctor_set(x_36, 0, x_123);
x_125 = lean_array_get_size(x_27);
x_126 = lean_nat_dec_lt(x_11, x_125);
x_127 = lean_box(3);
if (x_126 == 0)
{
lean_object* x_156; 
x_156 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_128 = x_156;
goto block_155;
}
else
{
lean_object* x_157; 
lean_dec(x_36);
x_157 = lean_array_fget(x_27, x_11);
x_128 = x_157;
goto block_155;
}
block_155:
{
lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_129, x_127);
lean_dec(x_129);
if (x_130 == 0)
{
lean_dec(x_128);
x_131 = x_5;
x_132 = x_117;
goto block_146;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_128, 1);
lean_inc(x_147);
lean_dec(x_128);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_148 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_147, x_5, x_6, x_7, x_8, x_9, x_117);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_131 = x_149;
x_132 = x_150;
goto block_146;
}
else
{
uint8_t x_151; 
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_151 = !lean_is_exclusive(x_148);
if (x_151 == 0)
{
return x_148;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_148, 0);
x_153 = lean_ctor_get(x_148, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_148);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
block_146:
{
if (x_126 == 0)
{
lean_object* x_133; 
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_118)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_118;
}
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_28;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_37);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_sub(x_125, x_137);
lean_dec(x_125);
x_139 = lean_box(0);
x_140 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_1, x_139, x_27, x_136, x_11, x_138);
lean_dec(x_27);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
lean_dec(x_120);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_118)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_118;
}
lean_ctor_set(x_141, 0, x_131);
lean_ctor_set(x_141, 1, x_132);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_118);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Array_append___rarg(x_33, x_120);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_2 = x_11;
x_3 = x_143;
x_4 = x_144;
x_5 = x_131;
x_10 = x_132;
goto _start;
}
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; 
x_158 = lean_ctor_get(x_36, 1);
lean_inc(x_158);
lean_dec(x_36);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_11);
x_161 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_array_get_size(x_27);
x_164 = lean_nat_dec_lt(x_11, x_163);
x_165 = lean_box(3);
if (x_164 == 0)
{
lean_object* x_194; 
x_194 = l___private_Init_Util_0__outOfBounds___rarg(x_162);
x_166 = x_194;
goto block_193;
}
else
{
lean_object* x_195; 
lean_dec(x_162);
x_195 = lean_array_fget(x_27, x_11);
x_166 = x_195;
goto block_193;
}
block_193:
{
lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_167, x_165);
lean_dec(x_167);
if (x_168 == 0)
{
lean_dec(x_166);
x_169 = x_5;
x_170 = x_117;
goto block_184;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_166, 1);
lean_inc(x_185);
lean_dec(x_166);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_186 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_185, x_5, x_6, x_7, x_8, x_9, x_117);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_169 = x_187;
x_170 = x_188;
goto block_184;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_118);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_189 = lean_ctor_get(x_186, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_191 = x_186;
} else {
 lean_dec_ref(x_186);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
block_184:
{
if (x_164 == 0)
{
lean_object* x_171; 
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_118)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_118;
}
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_28;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_37);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_sub(x_163, x_175);
lean_dec(x_163);
x_177 = lean_box(0);
x_178 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_1, x_177, x_27, x_174, x_11, x_176);
lean_dec(x_27);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
lean_dec(x_158);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_118)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_118;
}
lean_ctor_set(x_179, 0, x_169);
lean_ctor_set(x_179, 1, x_170);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_118);
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
lean_dec(x_178);
x_181 = l_Array_append___rarg(x_33, x_158);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_2 = x_11;
x_3 = x_181;
x_4 = x_182;
x_5 = x_169;
x_10 = x_170;
goto _start;
}
}
}
}
}
}
case 2:
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_35, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_197 = x_35;
} else {
 lean_dec_ref(x_35);
 x_197 = lean_box(0);
}
x_198 = !lean_is_exclusive(x_36);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; 
x_199 = lean_ctor_get(x_36, 1);
x_200 = lean_ctor_get(x_36, 0);
lean_dec(x_200);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_11);
x_203 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
lean_ctor_set(x_36, 1, x_203);
lean_ctor_set(x_36, 0, x_202);
x_204 = lean_array_get_size(x_27);
x_205 = lean_nat_dec_lt(x_11, x_204);
x_206 = lean_box(3);
if (x_205 == 0)
{
lean_object* x_235; 
x_235 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_207 = x_235;
goto block_234;
}
else
{
lean_object* x_236; 
lean_dec(x_36);
x_236 = lean_array_fget(x_27, x_11);
x_207 = x_236;
goto block_234;
}
block_234:
{
lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_208, x_206);
lean_dec(x_208);
if (x_209 == 0)
{
lean_dec(x_207);
x_210 = x_5;
x_211 = x_196;
goto block_225;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_207, 1);
lean_inc(x_226);
lean_dec(x_207);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_227 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_226, x_5, x_6, x_7, x_8, x_9, x_196);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_210 = x_228;
x_211 = x_229;
goto block_225;
}
else
{
uint8_t x_230; 
lean_dec(x_204);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_230 = !lean_is_exclusive(x_227);
if (x_230 == 0)
{
return x_227;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_227, 0);
x_232 = lean_ctor_get(x_227, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_227);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
block_225:
{
if (x_205 == 0)
{
lean_object* x_212; 
lean_dec(x_204);
lean_dec(x_199);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_197)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_197;
}
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_213 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_28;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_37);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_unsigned_to_nat(1u);
x_217 = lean_nat_sub(x_204, x_216);
lean_dec(x_204);
x_218 = lean_box(0);
x_219 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(x_1, x_218, x_27, x_215, x_11, x_217);
lean_dec(x_27);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
lean_dec(x_199);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_197)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_197;
}
lean_ctor_set(x_220, 0, x_210);
lean_ctor_set(x_220, 1, x_211);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_197);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
lean_dec(x_219);
x_222 = l_Array_append___rarg(x_33, x_199);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_2 = x_11;
x_3 = x_222;
x_4 = x_223;
x_5 = x_210;
x_10 = x_211;
goto _start;
}
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; 
x_237 = lean_ctor_get(x_36, 1);
lean_inc(x_237);
lean_dec(x_36);
x_238 = lean_box(0);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_11);
x_240 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_array_get_size(x_27);
x_243 = lean_nat_dec_lt(x_11, x_242);
x_244 = lean_box(3);
if (x_243 == 0)
{
lean_object* x_273; 
x_273 = l___private_Init_Util_0__outOfBounds___rarg(x_241);
x_245 = x_273;
goto block_272;
}
else
{
lean_object* x_274; 
lean_dec(x_241);
x_274 = lean_array_fget(x_27, x_11);
x_245 = x_274;
goto block_272;
}
block_272:
{
lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_246, x_244);
lean_dec(x_246);
if (x_247 == 0)
{
lean_dec(x_245);
x_248 = x_5;
x_249 = x_196;
goto block_263;
}
else
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_245, 1);
lean_inc(x_264);
lean_dec(x_245);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_265 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_264, x_5, x_6, x_7, x_8, x_9, x_196);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_248 = x_266;
x_249 = x_267;
goto block_263;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_242);
lean_dec(x_237);
lean_dec(x_197);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_268 = lean_ctor_get(x_265, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_270 = x_265;
} else {
 lean_dec_ref(x_265);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
block_263:
{
if (x_243 == 0)
{
lean_object* x_250; 
lean_dec(x_242);
lean_dec(x_237);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_197)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_197;
}
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_251 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_28;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_37);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_unsigned_to_nat(1u);
x_255 = lean_nat_sub(x_242, x_254);
lean_dec(x_242);
x_256 = lean_box(0);
x_257 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(x_1, x_256, x_27, x_253, x_11, x_255);
lean_dec(x_27);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; 
lean_dec(x_237);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_197)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_197;
}
lean_ctor_set(x_258, 0, x_248);
lean_ctor_set(x_258, 1, x_249);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_197);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
lean_dec(x_257);
x_260 = l_Array_append___rarg(x_33, x_237);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_2 = x_11;
x_3 = x_260;
x_4 = x_261;
x_5 = x_248;
x_10 = x_249;
goto _start;
}
}
}
}
}
}
case 3:
{
uint8_t x_275; 
lean_dec(x_36);
lean_dec(x_28);
x_275 = !lean_is_exclusive(x_35);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_276 = lean_ctor_get(x_35, 1);
x_277 = lean_ctor_get(x_35, 0);
lean_dec(x_277);
x_278 = lean_array_get_size(x_27);
x_279 = lean_nat_dec_lt(x_11, x_278);
if (x_279 == 0)
{
lean_dec(x_278);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_35, 0, x_5);
return x_35;
}
else
{
uint8_t x_280; 
x_280 = lean_nat_dec_le(x_278, x_278);
if (x_280 == 0)
{
lean_dec(x_278);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_35, 0, x_5);
return x_35;
}
else
{
size_t x_281; size_t x_282; lean_object* x_283; 
lean_free_object(x_35);
x_281 = 0;
x_282 = lean_usize_of_nat(x_278);
lean_dec(x_278);
x_283 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_1, x_33, x_27, x_281, x_282, x_5, x_6, x_7, x_8, x_9, x_276);
lean_dec(x_27);
return x_283;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_284 = lean_ctor_get(x_35, 1);
lean_inc(x_284);
lean_dec(x_35);
x_285 = lean_array_get_size(x_27);
x_286 = lean_nat_dec_lt(x_11, x_285);
if (x_286 == 0)
{
lean_object* x_287; 
lean_dec(x_285);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_5);
lean_ctor_set(x_287, 1, x_284);
return x_287;
}
else
{
uint8_t x_288; 
x_288 = lean_nat_dec_le(x_285, x_285);
if (x_288 == 0)
{
lean_object* x_289; 
lean_dec(x_285);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_5);
lean_ctor_set(x_289, 1, x_284);
return x_289;
}
else
{
size_t x_290; size_t x_291; lean_object* x_292; 
x_290 = 0;
x_291 = lean_usize_of_nat(x_285);
lean_dec(x_285);
x_292 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_1, x_33, x_27, x_290, x_291, x_5, x_6, x_7, x_8, x_9, x_284);
lean_dec(x_27);
return x_292;
}
}
}
}
case 4:
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_293 = lean_ctor_get(x_35, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_294 = x_35;
} else {
 lean_dec_ref(x_35);
 x_294 = lean_box(0);
}
x_295 = !lean_is_exclusive(x_36);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; 
x_296 = lean_ctor_get(x_36, 1);
x_297 = lean_ctor_get(x_36, 0);
lean_dec(x_297);
x_298 = lean_box(0);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_11);
x_300 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
lean_ctor_set(x_36, 1, x_300);
lean_ctor_set(x_36, 0, x_299);
x_301 = lean_array_get_size(x_27);
x_302 = lean_nat_dec_lt(x_11, x_301);
x_303 = lean_box(3);
if (x_302 == 0)
{
lean_object* x_332; 
x_332 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_304 = x_332;
goto block_331;
}
else
{
lean_object* x_333; 
lean_dec(x_36);
x_333 = lean_array_fget(x_27, x_11);
x_304 = x_333;
goto block_331;
}
block_331:
{
lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_305, x_303);
lean_dec(x_305);
if (x_306 == 0)
{
lean_dec(x_304);
x_307 = x_5;
x_308 = x_293;
goto block_322;
}
else
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_304, 1);
lean_inc(x_323);
lean_dec(x_304);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_324 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_323, x_5, x_6, x_7, x_8, x_9, x_293);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_307 = x_325;
x_308 = x_326;
goto block_322;
}
else
{
uint8_t x_327; 
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_294);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_327 = !lean_is_exclusive(x_324);
if (x_327 == 0)
{
return x_324;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_324, 0);
x_329 = lean_ctor_get(x_324, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_324);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
block_322:
{
if (x_302 == 0)
{
lean_object* x_309; 
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_294)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_294;
}
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_310 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_28;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_37);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_unsigned_to_nat(1u);
x_314 = lean_nat_sub(x_301, x_313);
lean_dec(x_301);
x_315 = lean_box(0);
x_316 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(x_1, x_315, x_27, x_312, x_11, x_314);
lean_dec(x_27);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; 
lean_dec(x_296);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_294)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_294;
}
lean_ctor_set(x_317, 0, x_307);
lean_ctor_set(x_317, 1, x_308);
return x_317;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_294);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
lean_dec(x_316);
x_319 = l_Array_append___rarg(x_33, x_296);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_2 = x_11;
x_3 = x_319;
x_4 = x_320;
x_5 = x_307;
x_10 = x_308;
goto _start;
}
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; lean_object* x_342; 
x_334 = lean_ctor_get(x_36, 1);
lean_inc(x_334);
lean_dec(x_36);
x_335 = lean_box(0);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_11);
x_337 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
x_339 = lean_array_get_size(x_27);
x_340 = lean_nat_dec_lt(x_11, x_339);
x_341 = lean_box(3);
if (x_340 == 0)
{
lean_object* x_370; 
x_370 = l___private_Init_Util_0__outOfBounds___rarg(x_338);
x_342 = x_370;
goto block_369;
}
else
{
lean_object* x_371; 
lean_dec(x_338);
x_371 = lean_array_fget(x_27, x_11);
x_342 = x_371;
goto block_369;
}
block_369:
{
lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_343, x_341);
lean_dec(x_343);
if (x_344 == 0)
{
lean_dec(x_342);
x_345 = x_5;
x_346 = x_293;
goto block_360;
}
else
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_342, 1);
lean_inc(x_361);
lean_dec(x_342);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_362 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_361, x_5, x_6, x_7, x_8, x_9, x_293);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_345 = x_363;
x_346 = x_364;
goto block_360;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_339);
lean_dec(x_334);
lean_dec(x_294);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_365 = lean_ctor_get(x_362, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_362, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_367 = x_362;
} else {
 lean_dec_ref(x_362);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
block_360:
{
if (x_340 == 0)
{
lean_object* x_347; 
lean_dec(x_339);
lean_dec(x_334);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_294)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_294;
}
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_348 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_28;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_348);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_37);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_unsigned_to_nat(1u);
x_352 = lean_nat_sub(x_339, x_351);
lean_dec(x_339);
x_353 = lean_box(0);
x_354 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(x_1, x_353, x_27, x_350, x_11, x_352);
lean_dec(x_27);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; 
lean_dec(x_334);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_294)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_294;
}
lean_ctor_set(x_355, 0, x_345);
lean_ctor_set(x_355, 1, x_346);
return x_355;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_294);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
lean_dec(x_354);
x_357 = l_Array_append___rarg(x_33, x_334);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_2 = x_11;
x_3 = x_357;
x_4 = x_358;
x_5 = x_345;
x_10 = x_346;
goto _start;
}
}
}
}
}
}
case 5:
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_372 = lean_ctor_get(x_35, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_373 = x_35;
} else {
 lean_dec_ref(x_35);
 x_373 = lean_box(0);
}
x_374 = !lean_is_exclusive(x_36);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; lean_object* x_383; 
x_375 = lean_ctor_get(x_36, 1);
x_376 = lean_ctor_get(x_36, 0);
lean_dec(x_376);
x_377 = lean_box(0);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_11);
x_379 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
lean_ctor_set(x_36, 1, x_379);
lean_ctor_set(x_36, 0, x_378);
x_380 = lean_array_get_size(x_27);
x_381 = lean_nat_dec_lt(x_11, x_380);
x_382 = lean_box(3);
if (x_381 == 0)
{
lean_object* x_428; 
x_428 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_383 = x_428;
goto block_427;
}
else
{
lean_object* x_429; 
lean_dec(x_36);
x_429 = lean_array_fget(x_27, x_11);
x_383 = x_429;
goto block_427;
}
block_427:
{
lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_384, x_382);
lean_dec(x_384);
if (x_385 == 0)
{
lean_dec(x_383);
x_386 = x_5;
x_387 = x_372;
goto block_418;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_383, 1);
lean_inc(x_419);
lean_dec(x_383);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_420 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_419, x_5, x_6, x_7, x_8, x_9, x_372);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_386 = x_421;
x_387 = x_422;
goto block_418;
}
else
{
uint8_t x_423; 
lean_dec(x_380);
lean_dec(x_375);
lean_dec(x_373);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_423 = !lean_is_exclusive(x_420);
if (x_423 == 0)
{
return x_420;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_420, 0);
x_425 = lean_ctor_get(x_420, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_420);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
}
block_418:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_388 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_28;
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_388);
lean_inc(x_389);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_37);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_unsigned_to_nat(1u);
x_392 = lean_nat_sub(x_380, x_391);
lean_dec(x_380);
if (x_381 == 0)
{
lean_dec(x_390);
lean_dec(x_375);
x_393 = x_386;
x_394 = x_387;
goto block_405;
}
else
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_box(0);
lean_inc(x_392);
x_407 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(x_1, x_406, x_27, x_390, x_11, x_392);
if (lean_obj_tag(x_407) == 0)
{
lean_dec(x_375);
x_393 = x_386;
x_394 = x_387;
goto block_405;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
lean_dec(x_407);
lean_inc(x_33);
x_409 = l_Array_append___rarg(x_33, x_375);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_411 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_409, x_410, x_386, x_6, x_7, x_8, x_9, x_387);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_393 = x_412;
x_394 = x_413;
goto block_405;
}
else
{
uint8_t x_414; 
lean_dec(x_392);
lean_dec(x_389);
lean_dec(x_373);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_414 = !lean_is_exclusive(x_411);
if (x_414 == 0)
{
return x_411;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_411, 0);
x_416 = lean_ctor_get(x_411, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_411);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
}
block_405:
{
if (x_381 == 0)
{
lean_object* x_395; 
lean_dec(x_392);
lean_dec(x_389);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_373)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_373;
}
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_396 = lean_box(4);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_389);
x_398 = lean_box(0);
x_399 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_1, x_398, x_27, x_397, x_11, x_392);
lean_dec(x_27);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_373)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_373;
}
lean_ctor_set(x_400, 0, x_393);
lean_ctor_set(x_400, 1, x_394);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_373);
x_401 = lean_ctor_get(x_399, 0);
lean_inc(x_401);
lean_dec(x_399);
x_402 = l_Array_append___rarg(x_33, x_388);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_2 = x_11;
x_3 = x_402;
x_4 = x_403;
x_5 = x_393;
x_10 = x_394;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; lean_object* x_438; 
x_430 = lean_ctor_get(x_36, 1);
lean_inc(x_430);
lean_dec(x_36);
x_431 = lean_box(0);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_11);
x_433 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
x_435 = lean_array_get_size(x_27);
x_436 = lean_nat_dec_lt(x_11, x_435);
x_437 = lean_box(3);
if (x_436 == 0)
{
lean_object* x_483; 
x_483 = l___private_Init_Util_0__outOfBounds___rarg(x_434);
x_438 = x_483;
goto block_482;
}
else
{
lean_object* x_484; 
lean_dec(x_434);
x_484 = lean_array_fget(x_27, x_11);
x_438 = x_484;
goto block_482;
}
block_482:
{
lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_439, x_437);
lean_dec(x_439);
if (x_440 == 0)
{
lean_dec(x_438);
x_441 = x_5;
x_442 = x_372;
goto block_473;
}
else
{
lean_object* x_474; lean_object* x_475; 
x_474 = lean_ctor_get(x_438, 1);
lean_inc(x_474);
lean_dec(x_438);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_475 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_474, x_5, x_6, x_7, x_8, x_9, x_372);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
x_441 = x_476;
x_442 = x_477;
goto block_473;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_435);
lean_dec(x_430);
lean_dec(x_373);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_478 = lean_ctor_get(x_475, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_475, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_480 = x_475;
} else {
 lean_dec_ref(x_475);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_481 = lean_alloc_ctor(1, 2, 0);
} else {
 x_481 = x_480;
}
lean_ctor_set(x_481, 0, x_478);
lean_ctor_set(x_481, 1, x_479);
return x_481;
}
}
block_473:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_443 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_28;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_443);
lean_inc(x_444);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_37);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_unsigned_to_nat(1u);
x_447 = lean_nat_sub(x_435, x_446);
lean_dec(x_435);
if (x_436 == 0)
{
lean_dec(x_445);
lean_dec(x_430);
x_448 = x_441;
x_449 = x_442;
goto block_460;
}
else
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_box(0);
lean_inc(x_447);
x_462 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(x_1, x_461, x_27, x_445, x_11, x_447);
if (lean_obj_tag(x_462) == 0)
{
lean_dec(x_430);
x_448 = x_441;
x_449 = x_442;
goto block_460;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
lean_dec(x_462);
lean_inc(x_33);
x_464 = l_Array_append___rarg(x_33, x_430);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_466 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_464, x_465, x_441, x_6, x_7, x_8, x_9, x_442);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
x_448 = x_467;
x_449 = x_468;
goto block_460;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_447);
lean_dec(x_444);
lean_dec(x_373);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_469 = lean_ctor_get(x_466, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_466, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_471 = x_466;
} else {
 lean_dec_ref(x_466);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_470);
return x_472;
}
}
}
block_460:
{
if (x_436 == 0)
{
lean_object* x_450; 
lean_dec(x_447);
lean_dec(x_444);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_373)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_373;
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_451 = lean_box(4);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_444);
x_453 = lean_box(0);
x_454 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_1, x_453, x_27, x_452, x_11, x_447);
lean_dec(x_27);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_373)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_373;
}
lean_ctor_set(x_455, 0, x_448);
lean_ctor_set(x_455, 1, x_449);
return x_455;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_373);
x_456 = lean_ctor_get(x_454, 0);
lean_inc(x_456);
lean_dec(x_454);
x_457 = l_Array_append___rarg(x_33, x_443);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_2 = x_11;
x_3 = x_457;
x_4 = x_458;
x_5 = x_448;
x_10 = x_449;
goto _start;
}
}
}
}
}
}
}
default: 
{
lean_object* x_485; lean_object* x_486; uint8_t x_487; 
x_485 = lean_ctor_get(x_35, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_486 = x_35;
} else {
 lean_dec_ref(x_35);
 x_486 = lean_box(0);
}
x_487 = !lean_is_exclusive(x_36);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; lean_object* x_495; lean_object* x_496; 
x_488 = lean_ctor_get(x_36, 1);
x_489 = lean_ctor_get(x_36, 0);
lean_dec(x_489);
x_490 = lean_box(0);
x_491 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_11);
x_492 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
lean_ctor_set(x_36, 1, x_492);
lean_ctor_set(x_36, 0, x_491);
x_493 = lean_array_get_size(x_27);
x_494 = lean_nat_dec_lt(x_11, x_493);
x_495 = lean_box(3);
if (x_494 == 0)
{
lean_object* x_524; 
x_524 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_496 = x_524;
goto block_523;
}
else
{
lean_object* x_525; 
lean_dec(x_36);
x_525 = lean_array_fget(x_27, x_11);
x_496 = x_525;
goto block_523;
}
block_523:
{
lean_object* x_497; uint8_t x_498; lean_object* x_499; lean_object* x_500; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_497, x_495);
lean_dec(x_497);
if (x_498 == 0)
{
lean_dec(x_496);
x_499 = x_5;
x_500 = x_485;
goto block_514;
}
else
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_ctor_get(x_496, 1);
lean_inc(x_515);
lean_dec(x_496);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_516 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_515, x_5, x_6, x_7, x_8, x_9, x_485);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; 
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_516, 1);
lean_inc(x_518);
lean_dec(x_516);
x_499 = x_517;
x_500 = x_518;
goto block_514;
}
else
{
uint8_t x_519; 
lean_dec(x_493);
lean_dec(x_488);
lean_dec(x_486);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_519 = !lean_is_exclusive(x_516);
if (x_519 == 0)
{
return x_516;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_520 = lean_ctor_get(x_516, 0);
x_521 = lean_ctor_get(x_516, 1);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_516);
x_522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_522, 0, x_520);
lean_ctor_set(x_522, 1, x_521);
return x_522;
}
}
}
block_514:
{
if (x_494 == 0)
{
lean_object* x_501; 
lean_dec(x_493);
lean_dec(x_488);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_486)) {
 x_501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_501 = x_486;
}
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
return x_501;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_502 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_503 = lean_alloc_ctor(0, 2, 0);
} else {
 x_503 = x_28;
}
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_502);
x_504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_504, 0, x_37);
lean_ctor_set(x_504, 1, x_503);
x_505 = lean_unsigned_to_nat(1u);
x_506 = lean_nat_sub(x_493, x_505);
lean_dec(x_493);
x_507 = lean_box(0);
x_508 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(x_1, x_507, x_27, x_504, x_11, x_506);
lean_dec(x_27);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; 
lean_dec(x_488);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_486)) {
 x_509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_509 = x_486;
}
lean_ctor_set(x_509, 0, x_499);
lean_ctor_set(x_509, 1, x_500);
return x_509;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_486);
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
lean_dec(x_508);
x_511 = l_Array_append___rarg(x_33, x_488);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_2 = x_11;
x_3 = x_511;
x_4 = x_512;
x_5 = x_499;
x_10 = x_500;
goto _start;
}
}
}
}
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; lean_object* x_533; lean_object* x_534; 
x_526 = lean_ctor_get(x_36, 1);
lean_inc(x_526);
lean_dec(x_36);
x_527 = lean_box(0);
x_528 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_11);
x_529 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_530 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set(x_530, 1, x_529);
x_531 = lean_array_get_size(x_27);
x_532 = lean_nat_dec_lt(x_11, x_531);
x_533 = lean_box(3);
if (x_532 == 0)
{
lean_object* x_562; 
x_562 = l___private_Init_Util_0__outOfBounds___rarg(x_530);
x_534 = x_562;
goto block_561;
}
else
{
lean_object* x_563; 
lean_dec(x_530);
x_563 = lean_array_fget(x_27, x_11);
x_534 = x_563;
goto block_561;
}
block_561:
{
lean_object* x_535; uint8_t x_536; lean_object* x_537; lean_object* x_538; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_535, x_533);
lean_dec(x_535);
if (x_536 == 0)
{
lean_dec(x_534);
x_537 = x_5;
x_538 = x_485;
goto block_552;
}
else
{
lean_object* x_553; lean_object* x_554; 
x_553 = lean_ctor_get(x_534, 1);
lean_inc(x_553);
lean_dec(x_534);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_554 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_553, x_5, x_6, x_7, x_8, x_9, x_485);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_537 = x_555;
x_538 = x_556;
goto block_552;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_dec(x_531);
lean_dec(x_526);
lean_dec(x_486);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_557 = lean_ctor_get(x_554, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_554, 1);
lean_inc(x_558);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 x_559 = x_554;
} else {
 lean_dec_ref(x_554);
 x_559 = lean_box(0);
}
if (lean_is_scalar(x_559)) {
 x_560 = lean_alloc_ctor(1, 2, 0);
} else {
 x_560 = x_559;
}
lean_ctor_set(x_560, 0, x_557);
lean_ctor_set(x_560, 1, x_558);
return x_560;
}
}
block_552:
{
if (x_532 == 0)
{
lean_object* x_539; 
lean_dec(x_531);
lean_dec(x_526);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_486)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_486;
}
lean_ctor_set(x_539, 0, x_537);
lean_ctor_set(x_539, 1, x_538);
return x_539;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_540 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_541 = lean_alloc_ctor(0, 2, 0);
} else {
 x_541 = x_28;
}
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_540);
x_542 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_542, 0, x_37);
lean_ctor_set(x_542, 1, x_541);
x_543 = lean_unsigned_to_nat(1u);
x_544 = lean_nat_sub(x_531, x_543);
lean_dec(x_531);
x_545 = lean_box(0);
x_546 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(x_1, x_545, x_27, x_542, x_11, x_544);
lean_dec(x_27);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; 
lean_dec(x_526);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_486)) {
 x_547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_547 = x_486;
}
lean_ctor_set(x_547, 0, x_537);
lean_ctor_set(x_547, 1, x_538);
return x_547;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_486);
x_548 = lean_ctor_get(x_546, 0);
lean_inc(x_548);
lean_dec(x_546);
x_549 = l_Array_append___rarg(x_33, x_526);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_2 = x_11;
x_3 = x_549;
x_4 = x_550;
x_5 = x_537;
x_10 = x_538;
goto _start;
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
uint8_t x_564; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_564 = !lean_is_exclusive(x_35);
if (x_564 == 0)
{
return x_35;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_35, 0);
x_566 = lean_ctor_get(x_35, 1);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_35);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_566);
return x_567;
}
}
}
else
{
lean_object* x_568; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_568, 0, x_5);
lean_ctor_set(x_568, 1, x_10);
return x_568;
}
}
else
{
lean_object* x_569; lean_object* x_570; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_569 = l_Array_append___rarg(x_5, x_26);
x_570 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_570, 0, x_569);
lean_ctor_set(x_570, 1, x_10);
return x_570;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify_process(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getUnify_process___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_12, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(x_13, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify_process___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_8(x_1, x_5, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
case 1:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_26 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg(x_1, x_25, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_3 = x_30;
x_5 = x_27;
x_10 = x_28;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
default: 
{
size_t x_36; size_t x_37; 
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_3 = x_37;
goto _start;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg___boxed), 10, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_2, x_5);
x_16 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = lean_apply_8(x_1, x_6, x_15, x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_21;
x_6 = x_18;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg___boxed), 11, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg(x_1, x_9, x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg(x_1, x_19, x_20, lean_box(0), x_21, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_20);
lean_dec(x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg), 8, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_8 = lean_usize_land(x_3, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_usize_shift_right(x_3, x_6);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Meta_DiscrTree_Key_arity___rarg(x_3);
x_11 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_12 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_10, x_11, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_19; 
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_22 = 2;
lean_ctor_set_uint8(x_20, 5, x_22);
x_23 = 0;
x_24 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_3, x_23, x_24, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
switch (lean_obj_tag(x_27)) {
case 0:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
lean_inc(x_2);
x_32 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_33 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_32);
x_9 = x_25;
goto block_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_25);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_35, x_31, x_34, x_32, x_4, x_5, x_6, x_7, x_29);
x_9 = x_36;
goto block_18;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
lean_inc(x_2);
x_39 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_40 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_37);
x_9 = x_41;
goto block_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_43, x_38, x_42, x_39, x_4, x_5, x_6, x_7, x_37);
x_9 = x_44;
goto block_18;
}
}
}
case 1:
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_25);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_25, 1);
x_47 = lean_ctor_get(x_25, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_26, 1);
lean_inc(x_48);
lean_dec(x_26);
lean_inc(x_2);
x_49 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_50 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_50) == 0)
{
lean_dec(x_48);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_49);
x_9 = x_25;
goto block_18;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_25);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_52, x_48, x_51, x_49, x_4, x_5, x_6, x_7, x_46);
x_9 = x_53;
goto block_18;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_25, 1);
lean_inc(x_54);
lean_dec(x_25);
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_dec(x_26);
lean_inc(x_2);
x_56 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_57 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_54);
x_9 = x_58;
goto block_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_60, x_55, x_59, x_56, x_4, x_5, x_6, x_7, x_54);
x_9 = x_61;
goto block_18;
}
}
}
case 2:
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_25);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_25, 1);
x_64 = lean_ctor_get(x_25, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_26, 1);
lean_inc(x_65);
lean_dec(x_26);
lean_inc(x_2);
x_66 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_67 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_67) == 0)
{
lean_dec(x_65);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_66);
x_9 = x_25;
goto block_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_25);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_69, x_65, x_68, x_66, x_4, x_5, x_6, x_7, x_63);
x_9 = x_70;
goto block_18;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_25, 1);
lean_inc(x_71);
lean_dec(x_25);
x_72 = lean_ctor_get(x_26, 1);
lean_inc(x_72);
lean_dec(x_26);
lean_inc(x_2);
x_73 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_74 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_dec(x_72);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_71);
x_9 = x_75;
goto block_18;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_77, x_72, x_76, x_73, x_4, x_5, x_6, x_7, x_71);
x_9 = x_78;
goto block_18;
}
}
}
case 3:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_26);
x_79 = lean_ctor_get(x_25, 1);
lean_inc(x_79);
lean_dec(x_25);
x_80 = lean_box(x_1);
x_81 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getUnify___rarg___lambda__1___boxed), 9, 1);
lean_closure_set(x_81, 0, x_80);
x_82 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_83 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg(x_2, x_81, x_82, x_4, x_5, x_6, x_7, x_79);
x_9 = x_83;
goto block_18;
}
case 4:
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_25);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_25, 1);
x_86 = lean_ctor_get(x_25, 0);
lean_dec(x_86);
x_87 = lean_ctor_get(x_26, 1);
lean_inc(x_87);
lean_dec(x_26);
lean_inc(x_2);
x_88 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_89 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_89) == 0)
{
lean_dec(x_87);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_88);
x_9 = x_25;
goto block_18;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_25);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_91, x_87, x_90, x_88, x_4, x_5, x_6, x_7, x_85);
x_9 = x_92;
goto block_18;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_25, 1);
lean_inc(x_93);
lean_dec(x_25);
x_94 = lean_ctor_get(x_26, 1);
lean_inc(x_94);
lean_dec(x_26);
lean_inc(x_2);
x_95 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_96 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
lean_dec(x_94);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_93);
x_9 = x_97;
goto block_18;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_99, x_94, x_98, x_95, x_4, x_5, x_6, x_7, x_93);
x_9 = x_100;
goto block_18;
}
}
}
case 5:
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_25);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_25, 1);
x_103 = lean_ctor_get(x_25, 0);
lean_dec(x_103);
x_104 = lean_ctor_get(x_26, 1);
lean_inc(x_104);
lean_dec(x_26);
lean_inc(x_2);
x_105 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_106 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_106) == 0)
{
lean_dec(x_104);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_105);
x_9 = x_25;
goto block_18;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_free_object(x_25);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_unsigned_to_nat(0u);
x_109 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_108, x_104, x_107, x_105, x_4, x_5, x_6, x_7, x_102);
x_9 = x_109;
goto block_18;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_25, 1);
lean_inc(x_110);
lean_dec(x_25);
x_111 = lean_ctor_get(x_26, 1);
lean_inc(x_111);
lean_dec(x_26);
lean_inc(x_2);
x_112 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_113 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
lean_dec(x_111);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_110);
x_9 = x_114;
goto block_18;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_116, x_111, x_115, x_112, x_4, x_5, x_6, x_7, x_110);
x_9 = x_117;
goto block_18;
}
}
}
default: 
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_25);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_25, 1);
x_120 = lean_ctor_get(x_25, 0);
lean_dec(x_120);
x_121 = lean_ctor_get(x_26, 1);
lean_inc(x_121);
lean_dec(x_26);
lean_inc(x_2);
x_122 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_123 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_123) == 0)
{
lean_dec(x_121);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_122);
x_9 = x_25;
goto block_18;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_free_object(x_25);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_unsigned_to_nat(0u);
x_126 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_125, x_121, x_124, x_122, x_4, x_5, x_6, x_7, x_119);
x_9 = x_126;
goto block_18;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_25, 1);
lean_inc(x_127);
lean_dec(x_25);
x_128 = lean_ctor_get(x_26, 1);
lean_inc(x_128);
lean_dec(x_26);
lean_inc(x_2);
x_129 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_130 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(x_1, x_2, x_27);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
lean_dec(x_128);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_127);
x_9 = x_131;
goto block_18;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_133, x_128, x_132, x_129, x_4, x_5, x_6, x_7, x_127);
x_9 = x_134;
goto block_18;
}
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_135 = !lean_is_exclusive(x_25);
if (x_135 == 0)
{
x_9 = x_25;
goto block_18;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_25, 0);
x_137 = lean_ctor_get(x_25, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_25);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_9 = x_138;
goto block_18;
}
}
}
else
{
uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; lean_object* x_155; 
x_139 = lean_ctor_get_uint8(x_20, 0);
x_140 = lean_ctor_get_uint8(x_20, 1);
x_141 = lean_ctor_get_uint8(x_20, 2);
x_142 = lean_ctor_get_uint8(x_20, 3);
x_143 = lean_ctor_get_uint8(x_20, 4);
x_144 = lean_ctor_get_uint8(x_20, 6);
x_145 = lean_ctor_get_uint8(x_20, 7);
x_146 = lean_ctor_get_uint8(x_20, 8);
x_147 = lean_ctor_get_uint8(x_20, 9);
x_148 = lean_ctor_get_uint8(x_20, 10);
x_149 = lean_ctor_get_uint8(x_20, 11);
x_150 = lean_ctor_get_uint8(x_20, 12);
lean_dec(x_20);
x_151 = 2;
x_152 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_152, 0, x_139);
lean_ctor_set_uint8(x_152, 1, x_140);
lean_ctor_set_uint8(x_152, 2, x_141);
lean_ctor_set_uint8(x_152, 3, x_142);
lean_ctor_set_uint8(x_152, 4, x_143);
lean_ctor_set_uint8(x_152, 5, x_151);
lean_ctor_set_uint8(x_152, 6, x_144);
lean_ctor_set_uint8(x_152, 7, x_145);
lean_ctor_set_uint8(x_152, 8, x_146);
lean_ctor_set_uint8(x_152, 9, x_147);
lean_ctor_set_uint8(x_152, 10, x_148);
lean_ctor_set_uint8(x_152, 11, x_149);
lean_ctor_set_uint8(x_152, 12, x_150);
lean_ctor_set(x_4, 0, x_152);
x_153 = 0;
x_154 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_155 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_3, x_153, x_154, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
switch (lean_obj_tag(x_157)) {
case 0:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_159 = x_155;
} else {
 lean_dec_ref(x_155);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_156, 1);
lean_inc(x_160);
lean_dec(x_156);
lean_inc(x_2);
x_161 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_162 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_2, x_157);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
lean_dec(x_160);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_159)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_159;
}
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_158);
x_9 = x_163;
goto block_18;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_159);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_unsigned_to_nat(0u);
x_166 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_165, x_160, x_164, x_161, x_4, x_5, x_6, x_7, x_158);
x_9 = x_166;
goto block_18;
}
}
case 1:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_155, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_168 = x_155;
} else {
 lean_dec_ref(x_155);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_156, 1);
lean_inc(x_169);
lean_dec(x_156);
lean_inc(x_2);
x_170 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_171 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_2, x_157);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
lean_dec(x_169);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_168)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_168;
}
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_167);
x_9 = x_172;
goto block_18;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_168);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_unsigned_to_nat(0u);
x_175 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_174, x_169, x_173, x_170, x_4, x_5, x_6, x_7, x_167);
x_9 = x_175;
goto block_18;
}
}
case 2:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_155, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_177 = x_155;
} else {
 lean_dec_ref(x_155);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_156, 1);
lean_inc(x_178);
lean_dec(x_156);
lean_inc(x_2);
x_179 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_180 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(x_1, x_2, x_157);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
lean_dec(x_178);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_177)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_177;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_176);
x_9 = x_181;
goto block_18;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_177);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_183, x_178, x_182, x_179, x_4, x_5, x_6, x_7, x_176);
x_9 = x_184;
goto block_18;
}
}
case 3:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_156);
x_185 = lean_ctor_get(x_155, 1);
lean_inc(x_185);
lean_dec(x_155);
x_186 = lean_box(x_1);
x_187 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getUnify___rarg___lambda__1___boxed), 9, 1);
lean_closure_set(x_187, 0, x_186);
x_188 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_189 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg(x_2, x_187, x_188, x_4, x_5, x_6, x_7, x_185);
x_9 = x_189;
goto block_18;
}
case 4:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_190 = lean_ctor_get(x_155, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_191 = x_155;
} else {
 lean_dec_ref(x_155);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_156, 1);
lean_inc(x_192);
lean_dec(x_156);
lean_inc(x_2);
x_193 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_194 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(x_1, x_2, x_157);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
lean_dec(x_192);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_191)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_191;
}
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_190);
x_9 = x_195;
goto block_18;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_191);
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_unsigned_to_nat(0u);
x_198 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_197, x_192, x_196, x_193, x_4, x_5, x_6, x_7, x_190);
x_9 = x_198;
goto block_18;
}
}
case 5:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_155, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_200 = x_155;
} else {
 lean_dec_ref(x_155);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_156, 1);
lean_inc(x_201);
lean_dec(x_156);
lean_inc(x_2);
x_202 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_203 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(x_1, x_2, x_157);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
lean_dec(x_201);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_200)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_200;
}
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_199);
x_9 = x_204;
goto block_18;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_200);
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_unsigned_to_nat(0u);
x_207 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_206, x_201, x_205, x_202, x_4, x_5, x_6, x_7, x_199);
x_9 = x_207;
goto block_18;
}
}
default: 
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_155, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_209 = x_155;
} else {
 lean_dec_ref(x_155);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_156, 1);
lean_inc(x_210);
lean_dec(x_156);
lean_inc(x_2);
x_211 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_212 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(x_1, x_2, x_157);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
lean_dec(x_210);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_209)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_209;
}
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_208);
x_9 = x_213;
goto block_18;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_209);
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_unsigned_to_nat(0u);
x_216 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_215, x_210, x_214, x_211, x_4, x_5, x_6, x_7, x_208);
x_9 = x_216;
goto block_18;
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_217 = lean_ctor_get(x_155, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_155, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_219 = x_155;
} else {
 lean_dec_ref(x_155);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
x_9 = x_220;
goto block_18;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_244; lean_object* x_245; 
x_221 = lean_ctor_get(x_4, 0);
x_222 = lean_ctor_get(x_4, 1);
x_223 = lean_ctor_get(x_4, 2);
x_224 = lean_ctor_get(x_4, 3);
x_225 = lean_ctor_get(x_4, 4);
x_226 = lean_ctor_get(x_4, 5);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_4);
x_227 = lean_ctor_get_uint8(x_221, 0);
x_228 = lean_ctor_get_uint8(x_221, 1);
x_229 = lean_ctor_get_uint8(x_221, 2);
x_230 = lean_ctor_get_uint8(x_221, 3);
x_231 = lean_ctor_get_uint8(x_221, 4);
x_232 = lean_ctor_get_uint8(x_221, 6);
x_233 = lean_ctor_get_uint8(x_221, 7);
x_234 = lean_ctor_get_uint8(x_221, 8);
x_235 = lean_ctor_get_uint8(x_221, 9);
x_236 = lean_ctor_get_uint8(x_221, 10);
x_237 = lean_ctor_get_uint8(x_221, 11);
x_238 = lean_ctor_get_uint8(x_221, 12);
if (lean_is_exclusive(x_221)) {
 x_239 = x_221;
} else {
 lean_dec_ref(x_221);
 x_239 = lean_box(0);
}
x_240 = 2;
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(0, 0, 13);
} else {
 x_241 = x_239;
}
lean_ctor_set_uint8(x_241, 0, x_227);
lean_ctor_set_uint8(x_241, 1, x_228);
lean_ctor_set_uint8(x_241, 2, x_229);
lean_ctor_set_uint8(x_241, 3, x_230);
lean_ctor_set_uint8(x_241, 4, x_231);
lean_ctor_set_uint8(x_241, 5, x_240);
lean_ctor_set_uint8(x_241, 6, x_232);
lean_ctor_set_uint8(x_241, 7, x_233);
lean_ctor_set_uint8(x_241, 8, x_234);
lean_ctor_set_uint8(x_241, 9, x_235);
lean_ctor_set_uint8(x_241, 10, x_236);
lean_ctor_set_uint8(x_241, 11, x_237);
lean_ctor_set_uint8(x_241, 12, x_238);
x_242 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_222);
lean_ctor_set(x_242, 2, x_223);
lean_ctor_set(x_242, 3, x_224);
lean_ctor_set(x_242, 4, x_225);
lean_ctor_set(x_242, 5, x_226);
x_243 = 0;
x_244 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_242);
x_245 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_3, x_243, x_244, x_242, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
switch (lean_obj_tag(x_247)) {
case 0:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_249 = x_245;
} else {
 lean_dec_ref(x_245);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
lean_dec(x_246);
lean_inc(x_2);
x_251 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_252 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_2, x_247);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; 
lean_dec(x_250);
lean_dec(x_242);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_249)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_249;
}
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_248);
x_9 = x_253;
goto block_18;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_249);
x_254 = lean_ctor_get(x_252, 0);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_unsigned_to_nat(0u);
x_256 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_255, x_250, x_254, x_251, x_242, x_5, x_6, x_7, x_248);
x_9 = x_256;
goto block_18;
}
}
case 1:
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_257 = lean_ctor_get(x_245, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_258 = x_245;
} else {
 lean_dec_ref(x_245);
 x_258 = lean_box(0);
}
x_259 = lean_ctor_get(x_246, 1);
lean_inc(x_259);
lean_dec(x_246);
lean_inc(x_2);
x_260 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_261 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_2, x_247);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
lean_dec(x_259);
lean_dec(x_242);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_258)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_258;
}
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_257);
x_9 = x_262;
goto block_18;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_258);
x_263 = lean_ctor_get(x_261, 0);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_unsigned_to_nat(0u);
x_265 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_264, x_259, x_263, x_260, x_242, x_5, x_6, x_7, x_257);
x_9 = x_265;
goto block_18;
}
}
case 2:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_ctor_get(x_245, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_267 = x_245;
} else {
 lean_dec_ref(x_245);
 x_267 = lean_box(0);
}
x_268 = lean_ctor_get(x_246, 1);
lean_inc(x_268);
lean_dec(x_246);
lean_inc(x_2);
x_269 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_270 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(x_1, x_2, x_247);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; 
lean_dec(x_268);
lean_dec(x_242);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_267)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_267;
}
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_266);
x_9 = x_271;
goto block_18;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_267);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_unsigned_to_nat(0u);
x_274 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_273, x_268, x_272, x_269, x_242, x_5, x_6, x_7, x_266);
x_9 = x_274;
goto block_18;
}
}
case 3:
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_246);
x_275 = lean_ctor_get(x_245, 1);
lean_inc(x_275);
lean_dec(x_245);
x_276 = lean_box(x_1);
x_277 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getUnify___rarg___lambda__1___boxed), 9, 1);
lean_closure_set(x_277, 0, x_276);
x_278 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_279 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg(x_2, x_277, x_278, x_242, x_5, x_6, x_7, x_275);
x_9 = x_279;
goto block_18;
}
case 4:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_280 = lean_ctor_get(x_245, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_281 = x_245;
} else {
 lean_dec_ref(x_245);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_246, 1);
lean_inc(x_282);
lean_dec(x_246);
lean_inc(x_2);
x_283 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_284 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(x_1, x_2, x_247);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; 
lean_dec(x_282);
lean_dec(x_242);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_281)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_281;
}
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_280);
x_9 = x_285;
goto block_18;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_281);
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_unsigned_to_nat(0u);
x_288 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_287, x_282, x_286, x_283, x_242, x_5, x_6, x_7, x_280);
x_9 = x_288;
goto block_18;
}
}
case 5:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_289 = lean_ctor_get(x_245, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_290 = x_245;
} else {
 lean_dec_ref(x_245);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_246, 1);
lean_inc(x_291);
lean_dec(x_246);
lean_inc(x_2);
x_292 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_293 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(x_1, x_2, x_247);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; 
lean_dec(x_291);
lean_dec(x_242);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_290)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_290;
}
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_289);
x_9 = x_294;
goto block_18;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_290);
x_295 = lean_ctor_get(x_293, 0);
lean_inc(x_295);
lean_dec(x_293);
x_296 = lean_unsigned_to_nat(0u);
x_297 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_296, x_291, x_295, x_292, x_242, x_5, x_6, x_7, x_289);
x_9 = x_297;
goto block_18;
}
}
default: 
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_298 = lean_ctor_get(x_245, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_299 = x_245;
} else {
 lean_dec_ref(x_245);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_246, 1);
lean_inc(x_300);
lean_dec(x_246);
lean_inc(x_2);
x_301 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1, x_2);
x_302 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(x_1, x_2, x_247);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; 
lean_dec(x_300);
lean_dec(x_242);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_299)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_299;
}
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_298);
x_9 = x_303;
goto block_18;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_299);
x_304 = lean_ctor_get(x_302, 0);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_unsigned_to_nat(0u);
x_306 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_305, x_300, x_304, x_301, x_242, x_5, x_6, x_7, x_298);
x_9 = x_306;
goto block_18;
}
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_242);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_307 = lean_ctor_get(x_245, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_245, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_309 = x_245;
} else {
 lean_dec_ref(x_245);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
x_9 = x_310;
goto block_18;
}
}
block_18:
{
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getUnify___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Meta_DiscrTree_getUnify___rarg___lambda__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_DiscrTree_getUnify___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DiscrTreeTypes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTreeTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_DiscrTree_Key_format___rarg___closed__1 = _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___rarg___closed__1);
l_Lean_Meta_DiscrTree_Key_format___rarg___closed__2 = _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___rarg___closed__2);
l_Lean_Meta_DiscrTree_Key_format___rarg___closed__3 = _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___rarg___closed__3);
l_Lean_Meta_DiscrTree_Key_format___rarg___closed__4 = _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___rarg___closed__4);
l_Lean_Meta_DiscrTree_Key_format___rarg___closed__5 = _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___rarg___closed__5);
l_Lean_Meta_DiscrTree_Key_format___rarg___closed__6 = _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__6();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___rarg___closed__6);
l_Lean_Meta_DiscrTree_Key_format___rarg___closed__7 = _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__7();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___rarg___closed__7);
l_Lean_Meta_DiscrTree_Key_format___rarg___closed__8 = _init_l_Lean_Meta_DiscrTree_Key_format___rarg___closed__8();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___rarg___closed__8);
l_Lean_Meta_DiscrTree_instToFormatKey___closed__1 = _init_l_Lean_Meta_DiscrTree_instToFormatKey___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instToFormatKey___closed__1);
l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1 = _init_l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1);
l_Lean_Meta_DiscrTree_empty___closed__1 = _init_l_Lean_Meta_DiscrTree_empty___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_empty___closed__1);
l_Lean_Meta_DiscrTree_empty___closed__2 = _init_l_Lean_Meta_DiscrTree_empty___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_empty___closed__2);
l_Lean_Meta_DiscrTree_empty___closed__3 = _init_l_Lean_Meta_DiscrTree_empty___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_empty___closed__3);
l_Lean_Meta_DiscrTree_empty___closed__4 = _init_l_Lean_Meta_DiscrTree_empty___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_empty___closed__4);
l_Lean_Meta_DiscrTree_empty___closed__5 = _init_l_Lean_Meta_DiscrTree_empty___closed__5();
lean_mark_persistent(l_Lean_Meta_DiscrTree_empty___closed__5);
l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1 = _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1);
l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2 = _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2);
l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3 = _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3);
l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4 = _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4);
l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5 = _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5);
l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6 = _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6);
l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7 = _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7);
l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8 = _init_l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8);
l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1 = _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1);
l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2 = _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2);
l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__3 = _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__3);
l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__4 = _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__4);
l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__5 = _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__5);
l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__6 = _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__6();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__6);
l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__7 = _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__7();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__7);
l_Lean_Meta_DiscrTree_format___rarg___closed__1 = _init_l_Lean_Meta_DiscrTree_format___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_format___rarg___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__2 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__2();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__2);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__5 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__5();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__5);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__7 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__7();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__7);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__2 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__2();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__2);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__4 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__4();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__4);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__5 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__5();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__5);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__6 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__6();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__6);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7);
l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1 = _init_l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1);
l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2 = _init_l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity);
l_Lean_Meta_DiscrTree_mkPath___closed__1 = _init_l_Lean_Meta_DiscrTree_mkPath___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_mkPath___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___closed__1);
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
