// Lean compiler output
// Module: Lean.Meta.DiscrTree
// Imports: Init Lean.Meta.WHNF Lean.Meta.Transform Lean.Meta.DiscrTreeTypes
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__6;
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___rarg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__21(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__22(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__2;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
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
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1(lean_object*, uint8_t);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey(uint8_t);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchCore___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_headBeta(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f(lean_object*);
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
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__1;
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
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Expr_getAppFn(x_1);
x_4 = l_Lean_Expr_isConst(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_30; uint8_t x_31; 
x_6 = l_Lean_Expr_constName_x21(x_3);
lean_dec(x_3);
x_30 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
x_31 = lean_name_eq(x_6, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
x_7 = x_32;
goto block_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_33);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_dec_eq(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_7 = x_37;
goto block_29;
}
else
{
lean_object* x_38; 
lean_dec(x_6);
x_38 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_1 = x_38;
goto _start;
}
}
block_29:
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_7);
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3;
x_9 = lean_name_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6;
x_11 = lean_name_eq(x_6, x_10);
lean_dec(x_6);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_13);
lean_dec(x_1);
x_15 = lean_nat_dec_eq(x_14, x_13);
lean_dec(x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_1);
x_20 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6;
x_21 = lean_name_eq(x_6, x_20);
lean_dec(x_6);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_17);
x_22 = 0;
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_17, x_16);
lean_dec(x_17);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_17, x_24);
lean_dec(x_17);
x_26 = lean_nat_sub(x_25, x_24);
lean_dec(x_25);
x_27 = l_Lean_Expr_getRevArg_x21(x_1, x_26);
x_1 = x_27;
goto _start;
}
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = 1;
return x_40;
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
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn(x_1);
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_3; lean_object* x_4; lean_object* x_31; uint8_t x_32; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_31 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
x_32 = lean_name_eq(x_3, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_4 = x_33;
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
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
x_4 = x_38;
goto block_30;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_39 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_40 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_box(0);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_nat_add(x_43, x_36);
lean_dec(x_43);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_nat_add(x_45, x_36);
lean_dec(x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
block_30:
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_4);
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3;
x_6 = lean_name_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6;
x_8 = lean_name_eq(x_3, x_7);
lean_dec(x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_10);
lean_dec(x_1);
x_12 = lean_nat_dec_eq(x_11, x_10);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__1;
return x_14;
}
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
x_20 = lean_name_eq(x_3, x_19);
lean_dec(x_3);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
x_21 = lean_box(0);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_16, x_15);
lean_dec(x_16);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__1;
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_16, x_25);
lean_dec(x_16);
x_27 = lean_nat_sub(x_26, x_25);
lean_dec(x_26);
x_28 = l_Lean_Expr_getRevArg_x21(x_1, x_27);
x_1 = x_28;
goto _start;
}
}
}
}
case 9:
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
lean_dec(x_2);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_48);
x_51 = lean_box(0);
return x_51;
}
}
default: 
{
lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
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
lean_object* x_8; lean_object* x_65; uint8_t x_66; 
x_65 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__5;
x_66 = lean_name_eq(x_1, x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7;
x_68 = lean_name_eq(x_1, x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_box(0);
x_8 = x_69;
goto block_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_unsigned_to_nat(0u);
x_71 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_70);
x_72 = lean_unsigned_to_nat(4u);
x_73 = lean_nat_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_71);
x_74 = lean_box(0);
x_8 = x_74;
goto block_64;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_nat_sub(x_71, x_70);
lean_dec(x_71);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_sub(x_75, x_76);
lean_dec(x_75);
lean_inc(x_2);
x_78 = l_Lean_Expr_getRevArg_x21(x_2, x_77);
x_79 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType(x_78, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
uint8_t x_82; 
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_79, 0);
lean_dec(x_83);
x_84 = 0;
x_85 = lean_box(x_84);
lean_ctor_set(x_79, 0, x_85);
return x_79;
}
else
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = 0;
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_79);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_79, 0);
lean_dec(x_91);
x_92 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_93 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_92);
x_94 = lean_box(x_93);
lean_ctor_set(x_79, 0, x_94);
return x_79;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_dec(x_79);
x_96 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_97 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_96);
x_98 = lean_box(x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_95);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_79);
if (x_100 == 0)
{
return x_79;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_79, 0);
x_102 = lean_ctor_get(x_79, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_79);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_unsigned_to_nat(0u);
x_105 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_104);
x_106 = lean_unsigned_to_nat(2u);
x_107 = lean_nat_dec_eq(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7;
x_109 = lean_name_eq(x_1, x_108);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_105);
x_110 = lean_box(0);
x_8 = x_110;
goto block_64;
}
else
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_unsigned_to_nat(4u);
x_112 = lean_nat_dec_eq(x_105, x_111);
if (x_112 == 0)
{
lean_object* x_113; 
lean_dec(x_105);
x_113 = lean_box(0);
x_8 = x_113;
goto block_64;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_nat_sub(x_105, x_104);
lean_dec(x_105);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_sub(x_114, x_115);
lean_dec(x_114);
lean_inc(x_2);
x_117 = l_Lean_Expr_getRevArg_x21(x_2, x_116);
x_118 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType(x_117, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
uint8_t x_121; 
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_118);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_118, 0);
lean_dec(x_122);
x_123 = 0;
x_124 = lean_box(x_123);
lean_ctor_set(x_118, 0, x_124);
return x_118;
}
else
{
lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
lean_dec(x_118);
x_126 = 0;
x_127 = lean_box(x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_118);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_118, 0);
lean_dec(x_130);
x_131 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_132 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_131);
x_133 = lean_box(x_132);
lean_ctor_set(x_118, 0, x_133);
return x_118;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_118, 1);
lean_inc(x_134);
lean_dec(x_118);
x_135 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_136 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_135);
x_137 = lean_box(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_134);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_118);
if (x_139 == 0)
{
return x_118;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_118, 0);
x_141 = lean_ctor_get(x_118, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_118);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
}
else
{
lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_105);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_143 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_144 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_143);
x_145 = lean_box(x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_7);
return x_146;
}
}
block_64:
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_8);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3;
x_10 = lean_name_eq(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
x_12 = lean_name_eq(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_16);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_17);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_22);
x_24 = lean_unsigned_to_nat(6u);
x_25 = lean_nat_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
x_27 = lean_name_eq(x_1, x_26);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_eq(x_23, x_31);
lean_dec(x_23);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_sub(x_23, x_35);
lean_dec(x_23);
x_37 = lean_nat_sub(x_36, x_35);
lean_dec(x_36);
lean_inc(x_2);
x_38 = l_Lean_Expr_getRevArg_x21(x_2, x_37);
x_39 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType(x_38, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = 0;
x_45 = lean_box(x_44);
lean_ctor_set(x_39, 0, x_45);
return x_39;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_dec(x_39);
x_47 = 0;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_39, 0);
lean_dec(x_51);
x_52 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_53 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_52);
x_54 = lean_box(x_53);
lean_ctor_set(x_39, 0, x_54);
return x_39;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
lean_dec(x_39);
x_56 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_57 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_56);
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_39);
if (x_60 == 0)
{
return x_39;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_39, 0);
x_62 = lean_ctor_get(x_39, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_39);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
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
lean_object* x_8; 
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
uint8_t x_8; uint8_t x_9; 
x_8 = 0;
x_9 = l_Lean_Expr_isHeadBetaTarget(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_headBeta(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__1;
x_6 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__2;
x_7 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = lean_apply_6(x_3, x_16, x_7, x_8, x_9, x_10, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = lean_box(3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_box(3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasLooseBVars(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_box(5);
x_12 = lean_array_push(x_2, x_3);
x_13 = lean_array_push(x_12, x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_box(4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
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
if (x_2 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_15, 0);
lean_inc(x_70);
x_71 = lean_box(x_1);
lean_inc(x_3);
lean_inc(x_70);
lean_inc(x_13);
x_72 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1___boxed), 11, 5);
lean_closure_set(x_72, 0, x_13);
lean_closure_set(x_72, 1, x_71);
lean_closure_set(x_72, 2, x_70);
lean_closure_set(x_72, 3, x_15);
lean_closure_set(x_72, 4, x_3);
lean_inc(x_13);
x_73 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f(x_13);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_free_object(x_11);
x_74 = lean_box(0);
x_75 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__2(x_70, x_13, x_72, x_1, x_3, x_74, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_70);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_3);
lean_ctor_set(x_11, 0, x_78);
return x_11;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_11);
x_79 = lean_ctor_get(x_15, 0);
lean_inc(x_79);
x_80 = lean_box(0);
x_81 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_13, x_1, x_79, x_15, x_3, x_80, x_5, x_6, x_7, x_8, x_14);
return x_81;
}
}
case 7:
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_free_object(x_11);
lean_dec(x_13);
x_82 = lean_ctor_get(x_15, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_15, 2);
lean_inc(x_83);
lean_dec(x_15);
x_84 = l_Lean_Expr_hasLooseBVars(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__3(x_1, x_3, x_82, x_83, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__1;
x_87 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__2;
lean_inc(x_8);
lean_inc(x_7);
x_88 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_83, x_86, x_87, x_7, x_8, x_14);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__3(x_1, x_3, x_82, x_89, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_82);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
return x_88;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_88);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
case 9:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_96 = lean_ctor_get(x_15, 0);
lean_inc(x_96);
lean_dec(x_15);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_3);
lean_ctor_set(x_11, 0, x_98);
return x_11;
}
case 11:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_free_object(x_11);
x_99 = lean_ctor_get(x_15, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_15, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_15, 2);
lean_inc(x_101);
x_102 = lean_st_ref_get(x_8, x_14);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_99);
x_106 = lean_is_class(x_105, x_99);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_13, x_107);
lean_inc(x_108);
x_109 = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_100);
lean_ctor_set(x_109, 2, x_108);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_108);
x_110 = l_Lean_Meta_getFunInfoNArgs(x_15, x_108, x_5, x_6, x_7, x_8, x_104);
if (x_106 == 0)
{
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_array_push(x_3, x_101);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_sub(x_108, x_115);
lean_dec(x_108);
x_117 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_114, x_116, x_13, x_113, x_5, x_6, x_7, x_8, x_112);
lean_dec(x_114);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_109);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_117, 0, x_120);
return x_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_117, 0);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_117);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_109);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
uint8_t x_125; 
lean_dec(x_109);
x_125 = !lean_is_exclusive(x_117);
if (x_125 == 0)
{
return x_117;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_117, 0);
x_127 = lean_ctor_get(x_117, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_117);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_101);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_110);
if (x_129 == 0)
{
return x_110;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_110, 0);
x_131 = lean_ctor_get(x_110, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_110);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_133 = lean_ctor_get(x_110, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_110, 1);
lean_inc(x_134);
lean_dec(x_110);
x_135 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(x_101);
x_136 = lean_array_push(x_3, x_135);
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
lean_dec(x_133);
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_sub(x_108, x_138);
lean_dec(x_108);
x_140 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_137, x_139, x_13, x_136, x_5, x_6, x_7, x_8, x_134);
lean_dec(x_137);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_109);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_140, 0, x_143);
return x_140;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_140, 0);
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_140);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_109);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
uint8_t x_148; 
lean_dec(x_109);
x_148 = !lean_is_exclusive(x_140);
if (x_148 == 0)
{
return x_140;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_140, 0);
x_150 = lean_ctor_get(x_140, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_140);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_101);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_152 = !lean_is_exclusive(x_110);
if (x_152 == 0)
{
return x_110;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_110, 0);
x_154 = lean_ctor_get(x_110, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_110);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
default: 
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_156 = lean_box(4);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_3);
lean_ctor_set(x_11, 0, x_157);
return x_11;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_11, 0);
x_159 = lean_ctor_get(x_11, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_11);
x_160 = l_Lean_Expr_getAppFn(x_158);
switch (lean_obj_tag(x_160)) {
case 1:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unsigned_to_nat(0u);
x_163 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_158, x_162);
lean_inc(x_163);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_163);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_163);
x_165 = l_Lean_Meta_getFunInfoNArgs(x_160, x_163, x_5, x_6, x_7, x_8, x_159);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_unsigned_to_nat(1u);
x_170 = lean_nat_sub(x_163, x_169);
lean_dec(x_163);
x_171 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_168, x_170, x_158, x_3, x_5, x_6, x_7, x_8, x_167);
lean_dec(x_168);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_164);
lean_ctor_set(x_175, 1, x_172);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_174;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_164);
x_177 = lean_ctor_get(x_171, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_171, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_179 = x_171;
} else {
 lean_dec_ref(x_171);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_181 = lean_ctor_get(x_165, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_165, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_183 = x_165;
} else {
 lean_dec_ref(x_165);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
case 2:
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_dec(x_158);
x_185 = lean_ctor_get(x_160, 0);
lean_inc(x_185);
lean_dec(x_160);
x_186 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId;
x_187 = lean_name_eq(x_185, x_186);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(x_185, x_5, x_6, x_7, x_8, x_159);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_192 = x_188;
} else {
 lean_dec_ref(x_188);
 x_192 = lean_box(0);
}
x_193 = lean_box(3);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_3);
if (lean_is_scalar(x_192)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_192;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_191);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_188, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_197 = x_188;
} else {
 lean_dec_ref(x_188);
 x_197 = lean_box(0);
}
x_198 = lean_box(4);
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
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_3);
x_201 = lean_ctor_get(x_188, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_188, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_203 = x_188;
} else {
 lean_dec_ref(x_188);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_185);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_205 = lean_box(3);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_3);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_159);
return x_207;
}
}
case 4:
{
if (x_2 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_160, 0);
lean_inc(x_208);
x_209 = lean_box(x_1);
lean_inc(x_3);
lean_inc(x_208);
lean_inc(x_158);
x_210 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1___boxed), 11, 5);
lean_closure_set(x_210, 0, x_158);
lean_closure_set(x_210, 1, x_209);
lean_closure_set(x_210, 2, x_208);
lean_closure_set(x_210, 3, x_160);
lean_closure_set(x_210, 4, x_3);
lean_inc(x_158);
x_211 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f(x_158);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_box(0);
x_213 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__2(x_208, x_158, x_210, x_1, x_3, x_212, x_5, x_6, x_7, x_8, x_159);
lean_dec(x_208);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_158);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_214 = lean_ctor_get(x_211, 0);
lean_inc(x_214);
lean_dec(x_211);
x_215 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_3);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_159);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_160, 0);
lean_inc(x_218);
x_219 = lean_box(0);
x_220 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_158, x_1, x_218, x_160, x_3, x_219, x_5, x_6, x_7, x_8, x_159);
return x_220;
}
}
case 7:
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_158);
x_221 = lean_ctor_get(x_160, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_160, 2);
lean_inc(x_222);
lean_dec(x_160);
x_223 = l_Lean_Expr_hasLooseBVars(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__3(x_1, x_3, x_221, x_222, x_5, x_6, x_7, x_8, x_159);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__1;
x_226 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__2;
lean_inc(x_8);
lean_inc(x_7);
x_227 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_222, x_225, x_226, x_7, x_8, x_159);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__3(x_1, x_3, x_221, x_228, x_5, x_6, x_7, x_8, x_229);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_221);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_231 = lean_ctor_get(x_227, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_227, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_233 = x_227;
} else {
 lean_dec_ref(x_227);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
}
case 9:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_158);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_235 = lean_ctor_get(x_160, 0);
lean_inc(x_235);
lean_dec(x_160);
x_236 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_236, 0, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_3);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_159);
return x_238;
}
case 11:
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_239 = lean_ctor_get(x_160, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_160, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_160, 2);
lean_inc(x_241);
x_242 = lean_st_ref_get(x_8, x_159);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_ctor_get(x_243, 0);
lean_inc(x_245);
lean_dec(x_243);
lean_inc(x_239);
x_246 = lean_is_class(x_245, x_239);
x_247 = lean_unsigned_to_nat(0u);
x_248 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_158, x_247);
lean_inc(x_248);
x_249 = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(x_249, 0, x_239);
lean_ctor_set(x_249, 1, x_240);
lean_ctor_set(x_249, 2, x_248);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_248);
x_250 = l_Lean_Meta_getFunInfoNArgs(x_160, x_248, x_5, x_6, x_7, x_8, x_244);
if (x_246 == 0)
{
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_array_push(x_3, x_241);
x_254 = lean_ctor_get(x_251, 0);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_unsigned_to_nat(1u);
x_256 = lean_nat_sub(x_248, x_255);
lean_dec(x_248);
x_257 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_254, x_256, x_158, x_253, x_5, x_6, x_7, x_8, x_252);
lean_dec(x_254);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_260 = x_257;
} else {
 lean_dec_ref(x_257);
 x_260 = lean_box(0);
}
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_249);
lean_ctor_set(x_261, 1, x_258);
if (lean_is_scalar(x_260)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_260;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_259);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_249);
x_263 = lean_ctor_get(x_257, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_257, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_265 = x_257;
} else {
 lean_dec_ref(x_257);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_158);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_267 = lean_ctor_get(x_250, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_250, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_269 = x_250;
} else {
 lean_dec_ref(x_250);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
else
{
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_271 = lean_ctor_get(x_250, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_250, 1);
lean_inc(x_272);
lean_dec(x_250);
x_273 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(x_241);
x_274 = lean_array_push(x_3, x_273);
x_275 = lean_ctor_get(x_271, 0);
lean_inc(x_275);
lean_dec(x_271);
x_276 = lean_unsigned_to_nat(1u);
x_277 = lean_nat_sub(x_248, x_276);
lean_dec(x_248);
x_278 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_275, x_277, x_158, x_274, x_5, x_6, x_7, x_8, x_272);
lean_dec(x_275);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_281 = x_278;
} else {
 lean_dec_ref(x_278);
 x_281 = lean_box(0);
}
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_249);
lean_ctor_set(x_282, 1, x_279);
if (lean_is_scalar(x_281)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_281;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_280);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_249);
x_284 = lean_ctor_get(x_278, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_278, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_286 = x_278;
} else {
 lean_dec_ref(x_278);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_158);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_288 = lean_ctor_get(x_250, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_250, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_290 = x_250;
} else {
 lean_dec_ref(x_250);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
}
}
default: 
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_292 = lean_box(4);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_3);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_159);
return x_294;
}
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_295 = !lean_is_exclusive(x_11);
if (x_295 == 0)
{
return x_11;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_11, 0);
x_297 = lean_ctor_get(x_11, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_11);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_299 = lean_box(3);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_3);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_9);
return x_301;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__2(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__3(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
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
uint8_t x_9; 
x_9 = l_Array_isEmpty___rarg(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
x_11 = lean_array_get(x_8, x_7, x_10);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_13, x_12);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_8);
x_16 = lean_array_get_size(x_7);
x_17 = lean_nat_dec_lt(x_10, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_array_fget(x_7, x_10);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_7, x_10, x_19);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
x_26 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_25, x_22);
lean_dec(x_25);
lean_ctor_set(x_18, 1, x_26);
lean_ctor_set(x_18, 0, x_6);
x_27 = lean_array_fset(x_20, x_10, x_18);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
x_31 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_30, x_28);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_fset(x_20, x_10, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_inc(x_8);
x_34 = l_Array_back___rarg(x_8, x_7);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_35, x_12);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_12, x_35);
lean_dec(x_35);
lean_dec(x_12);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_8);
x_38 = lean_array_get_size(x_7);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_38, x_39);
x_41 = lean_nat_dec_lt(x_40, x_38);
lean_dec(x_38);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_array_fget(x_7, x_40);
x_43 = lean_box(0);
x_44 = lean_array_fset(x_7, x_40, x_43);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
x_48 = lean_nat_add(x_5, x_39);
x_49 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_48, x_46);
lean_dec(x_48);
lean_ctor_set(x_42, 1, x_49);
lean_ctor_set(x_42, 0, x_6);
x_50 = lean_array_fset(x_44, x_40, x_42);
lean_dec(x_40);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_nat_add(x_5, x_39);
x_53 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_52, x_51);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_6);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_fset(x_44, x_40, x_54);
lean_dec(x_40);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_array_get_size(x_7);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_56, x_57);
lean_dec(x_56);
x_59 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_2);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_5, x_60);
x_62 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_3, x_4, x_61);
lean_dec(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_6);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_array_push(x_7, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_2);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_5, x_65);
x_67 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_3, x_4, x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_6);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Array_insertAt_x21___rarg(x_7, x_10, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_8);
lean_dec(x_2);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_5, x_70);
x_72 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_3, x_4, x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_push(x_7, x_73);
return x_74;
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
x_3 = lean_unsigned_to_nat(422u);
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
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_hasLooseBVars(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_box(5);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2___closed__1;
x_12 = lean_array_push(x_11, x_2);
x_13 = lean_array_push(x_12, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(4);
x_17 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = l_Lean_Expr_getAppFn(x_1);
switch (lean_obj_tag(x_10)) {
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_12);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
case 2:
{
lean_dec(x_1);
if (x_3 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, 4);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(x_21, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_box(3);
x_28 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_22, 0, x_29);
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_box(3);
x_32 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_22, 0);
lean_dec(x_36);
x_37 = lean_box(4);
x_38 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_box(4);
x_42 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_22);
if (x_45 == 0)
{
return x_22;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_22, 0);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_22);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_49 = lean_box(3);
x_50 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_9);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_53 = lean_box(4);
x_54 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_9);
return x_56;
}
}
case 4:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_10, 0);
lean_inc(x_57);
lean_dec(x_10);
x_58 = l_Lean_Meta_getConfig(x_5, x_6, x_7, x_8, x_9);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_59, 4);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_box(0);
x_63 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_1, x_2, x_57, x_62, x_5, x_6, x_7, x_8, x_61);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_63;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = l_Lean_Expr_hasExprMVar(x_1);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(0);
x_67 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_1, x_2, x_57, x_66, x_5, x_6, x_7, x_8, x_64);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_inc(x_57);
x_68 = l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(x_57, x_5, x_6, x_7, x_8, x_64);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_st_ref_get(x_8, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_isMatcherAppCore_x3f(x_75, x_1);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_inc(x_57);
x_77 = l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(x_57, x_5, x_6, x_7, x_8, x_74);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_box(0);
x_82 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_1, x_2, x_57, x_81, x_5, x_6, x_7, x_8, x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_dec(x_77);
x_84 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_83);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
return x_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_84);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; lean_object* x_103; size_t x_104; lean_object* x_105; lean_object* x_106; 
x_89 = lean_ctor_get(x_76, 0);
lean_inc(x_89);
lean_dec(x_76);
x_90 = lean_unsigned_to_nat(0u);
x_91 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_90);
x_92 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3___closed__1;
lean_inc(x_91);
x_93 = lean_mk_array(x_91, x_92);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_sub(x_91, x_94);
lean_dec(x_91);
lean_inc(x_1);
x_96 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_93, x_95);
x_97 = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(x_89);
x_98 = lean_ctor_get(x_89, 1);
lean_inc(x_98);
lean_dec(x_89);
x_99 = lean_nat_add(x_97, x_98);
lean_dec(x_98);
x_100 = l_Array_toSubarray___rarg(x_96, x_97, x_99);
x_101 = lean_ctor_get(x_100, 2);
lean_inc(x_101);
x_102 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
x_104 = lean_usize_of_nat(x_103);
lean_dec(x_103);
x_105 = lean_box(0);
x_106 = l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2(x_100, x_102, x_104, x_105, x_5, x_6, x_7, x_8, x_74);
lean_dec(x_100);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_1, x_2, x_57, x_105, x_5, x_6, x_7, x_8, x_107);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_108;
}
else
{
uint8_t x_109; 
lean_dec(x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec(x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_113 = lean_ctor_get(x_68, 1);
lean_inc(x_113);
lean_dec(x_68);
x_114 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_113);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
return x_114;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_114);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
case 7:
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_1);
x_119 = lean_ctor_get(x_10, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_10, 2);
lean_inc(x_120);
lean_dec(x_10);
x_121 = l_Lean_Expr_hasLooseBVars(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2(x_2, x_119, x_120, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__1;
x_124 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__2;
lean_inc(x_8);
lean_inc(x_7);
x_125 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_120, x_123, x_124, x_7, x_8, x_9);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2(x_2, x_119, x_126, x_5, x_6, x_7, x_8, x_127);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_128;
}
else
{
uint8_t x_129; 
lean_dec(x_119);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
return x_125;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_125);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
case 9:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_133 = lean_ctor_get(x_10, 0);
lean_inc(x_133);
lean_dec(x_10);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_9);
return x_137;
}
case 11:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_138 = lean_ctor_get(x_10, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_10, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_10, 2);
lean_inc(x_140);
lean_dec(x_10);
x_141 = lean_unsigned_to_nat(0u);
x_142 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_141);
lean_inc(x_142);
x_143 = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(x_143, 0, x_138);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set(x_143, 2, x_142);
x_144 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___closed__1;
x_145 = lean_array_push(x_144, x_140);
x_146 = lean_mk_empty_array_with_capacity(x_142);
lean_dec(x_142);
x_147 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_146);
x_148 = l_Array_append___rarg(x_145, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_9);
return x_150;
}
default: 
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_151 = lean_box(4);
x_152 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_9);
return x_154;
}
}
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
lean_inc(x_12);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_10);
x_15 = lean_box(0);
x_16 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3(x_12, x_1, x_3, x_15, x_5, x_6, x_7, x_8, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
lean_inc(x_21);
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3(x_21, x_1, x_3, x_24, x_5, x_6, x_7, x_8, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_15 = l_Lean_instInhabitedExpr;
x_16 = l_Array_back___rarg(x_15, x_2);
x_17 = lean_array_pop(x_2);
x_173 = lean_box(0);
x_174 = lean_unsigned_to_nat(0u);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_array_get_size(x_11);
x_179 = lean_nat_dec_lt(x_174, x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = l___private_Init_Util_0__outOfBounds___rarg(x_177);
x_18 = x_180;
goto block_172;
}
else
{
lean_object* x_181; 
lean_dec(x_177);
x_181 = lean_array_fget(x_11, x_174);
x_18 = x_181;
goto block_172;
}
block_172:
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
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
x_31 = x_20;
goto block_167;
}
else
{
x_31 = x_19;
goto block_167;
}
block_167:
{
lean_object* x_32; lean_object* x_33; 
if (x_31 == 0)
{
lean_dec(x_18);
x_32 = x_4;
x_33 = x_23;
goto block_158;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_18, 1);
lean_inc(x_159);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_160 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(x_1, x_17, x_159, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_32 = x_161;
x_33 = x_162;
goto block_158;
}
else
{
uint8_t x_163; 
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
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
return x_160;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_160, 0);
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_160);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
block_158:
{
lean_object* x_34; 
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_12);
x_66 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_25);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_array_get_size(x_11);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_69, x_70);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_lt(x_72, x_69);
lean_dec(x_69);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_32);
lean_ctor_set(x_74, 1, x_33);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_box(0);
x_76 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg(x_1, x_75, x_11, x_68, x_72, x_71);
lean_dec(x_11);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_32);
lean_ctor_set(x_77, 1, x_33);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Array_append___rarg(x_17, x_26);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_2 = x_79;
x_3 = x_80;
x_4 = x_32;
x_9 = x_33;
goto _start;
}
}
}
case 1:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_12);
x_82 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_25);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_array_get_size(x_11);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_85, x_86);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_dec_lt(x_88, x_85);
lean_dec(x_85);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_32);
lean_ctor_set(x_90, 1, x_33);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_box(0);
x_92 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg(x_1, x_91, x_11, x_84, x_88, x_87);
lean_dec(x_11);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_32);
lean_ctor_set(x_93, 1, x_33);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Array_append___rarg(x_17, x_26);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_2 = x_95;
x_3 = x_96;
x_4 = x_32;
x_9 = x_33;
goto _start;
}
}
}
case 2:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_12);
x_98 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_25);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_array_get_size(x_11);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_sub(x_101, x_102);
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_nat_dec_lt(x_104, x_101);
lean_dec(x_101);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_32);
lean_ctor_set(x_106, 1, x_33);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_box(0);
x_108 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg(x_1, x_107, x_11, x_100, x_104, x_103);
lean_dec(x_11);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_32);
lean_ctor_set(x_109, 1, x_33);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Array_append___rarg(x_17, x_26);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_2 = x_111;
x_3 = x_112;
x_4 = x_32;
x_9 = x_33;
goto _start;
}
}
}
case 3:
{
lean_object* x_114; 
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
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_32);
lean_ctor_set(x_114, 1, x_33);
return x_114;
}
case 4:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_12);
x_115 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_25);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_array_get_size(x_11);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_sub(x_118, x_119);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_nat_dec_lt(x_121, x_118);
lean_dec(x_118);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_32);
lean_ctor_set(x_123, 1, x_33);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_box(0);
x_125 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg(x_1, x_124, x_11, x_117, x_121, x_120);
lean_dec(x_11);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_32);
lean_ctor_set(x_126, 1, x_33);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Array_append___rarg(x_17, x_26);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_2 = x_128;
x_3 = x_129;
x_4 = x_32;
x_9 = x_33;
goto _start;
}
}
}
case 5:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_131 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_25);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_array_get_size(x_11);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_sub(x_134, x_135);
x_137 = lean_unsigned_to_nat(0u);
x_138 = lean_nat_dec_lt(x_137, x_134);
lean_dec(x_134);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_136);
lean_dec(x_133);
x_139 = lean_box(0);
x_34 = x_139;
goto block_65;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_box(0);
x_141 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg(x_1, x_140, x_11, x_133, x_137, x_136);
x_34 = x_141;
goto block_65;
}
}
default: 
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_12);
x_142 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_25);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_array_get_size(x_11);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_nat_sub(x_145, x_146);
x_148 = lean_unsigned_to_nat(0u);
x_149 = lean_nat_dec_lt(x_148, x_145);
lean_dec(x_145);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_32);
lean_ctor_set(x_150, 1, x_33);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_box(0);
x_152 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg(x_1, x_151, x_11, x_144, x_148, x_147);
lean_dec(x_11);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_32);
lean_ctor_set(x_153, 1, x_33);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Array_append___rarg(x_17, x_26);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_2 = x_155;
x_3 = x_156;
x_4 = x_32;
x_9 = x_33;
goto _start;
}
}
}
}
block_65:
{
lean_object* x_35; lean_object* x_36; 
if (lean_obj_tag(x_34) == 0)
{
lean_dec(x_26);
x_35 = x_32;
x_36 = x_33;
goto block_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_34, 0);
lean_inc(x_55);
lean_dec(x_34);
lean_inc(x_17);
x_56 = l_Array_append___rarg(x_17, x_26);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_58 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(x_1, x_56, x_57, x_32, x_5, x_6, x_7, x_8, x_33);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_35 = x_59;
x_36 = x_60;
goto block_54;
}
else
{
uint8_t x_61; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
block_54:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_37 = lean_box(4);
x_38 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_12)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_12;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_38);
if (lean_is_scalar(x_27)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_27;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_get_size(x_11);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_41, x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_lt(x_44, x_41);
lean_dec(x_41);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_24)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_24;
}
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_36);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_box(0);
x_48 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg(x_1, x_47, x_11, x_40, x_44, x_43);
lean_dec(x_11);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_24)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_24;
}
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_36);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_24);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Array_append___rarg(x_17, x_38);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_2 = x_51;
x_3 = x_52;
x_4 = x_35;
x_9 = x_36;
goto _start;
}
}
}
}
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_168 = !lean_is_exclusive(x_21);
if (x_168 == 0)
{
return x_21;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_21, 0);
x_170 = lean_ctor_get(x_21, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_21);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
}
else
{
lean_object* x_182; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_4);
lean_ctor_set(x_182, 1, x_9);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_183 = l_Array_append___rarg(x_4, x_10);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_9);
return x_184;
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
lean_object* x_80; 
x_80 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_49 = x_80;
goto block_79;
}
else
{
lean_object* x_81; 
lean_dec(x_36);
x_81 = lean_array_fget(x_27, x_11);
x_49 = x_81;
goto block_79;
}
block_79:
{
lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_50, x_48);
lean_dec(x_50);
if (x_51 == 0)
{
x_52 = x_34;
goto block_77;
}
else
{
uint8_t x_78; 
x_78 = 1;
x_52 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_53; lean_object* x_54; 
if (x_52 == 0)
{
lean_dec(x_49);
x_53 = x_5;
x_54 = x_38;
goto block_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
lean_dec(x_49);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_70 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_69, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_53 = x_71;
x_54 = x_72;
goto block_68;
}
else
{
uint8_t x_73; 
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
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
block_68:
{
if (x_47 == 0)
{
lean_object* x_55; 
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
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_39;
}
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_28;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_37);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_46, x_59);
lean_dec(x_46);
x_61 = lean_box(0);
x_62 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(x_1, x_61, x_27, x_58, x_11, x_60);
lean_dec(x_27);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
lean_dec(x_41);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_39)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_39;
}
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_54);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_39);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Array_append___rarg(x_33, x_41);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_2 = x_11;
x_3 = x_65;
x_4 = x_66;
x_5 = x_53;
x_10 = x_54;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_36, 1);
lean_inc(x_82);
lean_dec(x_36);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_11);
x_85 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_array_get_size(x_27);
x_88 = lean_nat_dec_lt(x_11, x_87);
x_89 = lean_box(3);
if (x_88 == 0)
{
lean_object* x_121; 
x_121 = l___private_Init_Util_0__outOfBounds___rarg(x_86);
x_90 = x_121;
goto block_120;
}
else
{
lean_object* x_122; 
lean_dec(x_86);
x_122 = lean_array_fget(x_27, x_11);
x_90 = x_122;
goto block_120;
}
block_120:
{
lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_91, x_89);
lean_dec(x_91);
if (x_92 == 0)
{
x_93 = x_34;
goto block_118;
}
else
{
uint8_t x_119; 
x_119 = 1;
x_93 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_94; lean_object* x_95; 
if (x_93 == 0)
{
lean_dec(x_90);
x_94 = x_5;
x_95 = x_38;
goto block_109;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_90, 1);
lean_inc(x_110);
lean_dec(x_90);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_111 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_110, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_94 = x_112;
x_95 = x_113;
goto block_109;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_87);
lean_dec(x_82);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_116 = x_111;
} else {
 lean_dec_ref(x_111);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
block_109:
{
if (x_88 == 0)
{
lean_object* x_96; 
lean_dec(x_87);
lean_dec(x_82);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_39)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_39;
}
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_28;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_37);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_sub(x_87, x_100);
lean_dec(x_87);
x_102 = lean_box(0);
x_103 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(x_1, x_102, x_27, x_99, x_11, x_101);
lean_dec(x_27);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
lean_dec(x_82);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_39)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_39;
}
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_95);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_39);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Array_append___rarg(x_33, x_82);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_2 = x_11;
x_3 = x_106;
x_4 = x_107;
x_5 = x_94;
x_10 = x_95;
goto _start;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_35, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_124 = x_35;
} else {
 lean_dec_ref(x_35);
 x_124 = lean_box(0);
}
x_125 = !lean_is_exclusive(x_36);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; 
x_126 = lean_ctor_get(x_36, 1);
x_127 = lean_ctor_get(x_36, 0);
lean_dec(x_127);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_11);
x_130 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
lean_ctor_set(x_36, 1, x_130);
lean_ctor_set(x_36, 0, x_129);
x_131 = lean_array_get_size(x_27);
x_132 = lean_nat_dec_lt(x_11, x_131);
x_133 = lean_box(3);
if (x_132 == 0)
{
lean_object* x_165; 
x_165 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_134 = x_165;
goto block_164;
}
else
{
lean_object* x_166; 
lean_dec(x_36);
x_166 = lean_array_fget(x_27, x_11);
x_134 = x_166;
goto block_164;
}
block_164:
{
lean_object* x_135; uint8_t x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_135, x_133);
lean_dec(x_135);
if (x_136 == 0)
{
x_137 = x_34;
goto block_162;
}
else
{
uint8_t x_163; 
x_163 = 1;
x_137 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_138; lean_object* x_139; 
if (x_137 == 0)
{
lean_dec(x_134);
x_138 = x_5;
x_139 = x_123;
goto block_153;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_134, 1);
lean_inc(x_154);
lean_dec(x_134);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_155 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_154, x_5, x_6, x_7, x_8, x_9, x_123);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_138 = x_156;
x_139 = x_157;
goto block_153;
}
else
{
uint8_t x_158; 
lean_dec(x_131);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_158 = !lean_is_exclusive(x_155);
if (x_158 == 0)
{
return x_155;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_155, 0);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_155);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
block_153:
{
if (x_132 == 0)
{
lean_object* x_140; 
lean_dec(x_131);
lean_dec(x_126);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_124)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_124;
}
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_28;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_37);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_sub(x_131, x_144);
lean_dec(x_131);
x_146 = lean_box(0);
x_147 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_1, x_146, x_27, x_143, x_11, x_145);
lean_dec(x_27);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
lean_dec(x_126);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_124)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_124;
}
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_139);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_124);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Array_append___rarg(x_33, x_126);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_2 = x_11;
x_3 = x_150;
x_4 = x_151;
x_5 = x_138;
x_10 = x_139;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; 
x_167 = lean_ctor_get(x_36, 1);
lean_inc(x_167);
lean_dec(x_36);
x_168 = lean_box(0);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_11);
x_170 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_array_get_size(x_27);
x_173 = lean_nat_dec_lt(x_11, x_172);
x_174 = lean_box(3);
if (x_173 == 0)
{
lean_object* x_206; 
x_206 = l___private_Init_Util_0__outOfBounds___rarg(x_171);
x_175 = x_206;
goto block_205;
}
else
{
lean_object* x_207; 
lean_dec(x_171);
x_207 = lean_array_fget(x_27, x_11);
x_175 = x_207;
goto block_205;
}
block_205:
{
lean_object* x_176; uint8_t x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_176, x_174);
lean_dec(x_176);
if (x_177 == 0)
{
x_178 = x_34;
goto block_203;
}
else
{
uint8_t x_204; 
x_204 = 1;
x_178 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_179; lean_object* x_180; 
if (x_178 == 0)
{
lean_dec(x_175);
x_179 = x_5;
x_180 = x_123;
goto block_194;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_175, 1);
lean_inc(x_195);
lean_dec(x_175);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_196 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_195, x_5, x_6, x_7, x_8, x_9, x_123);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_179 = x_197;
x_180 = x_198;
goto block_194;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_172);
lean_dec(x_167);
lean_dec(x_124);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_199 = lean_ctor_get(x_196, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_201 = x_196;
} else {
 lean_dec_ref(x_196);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
block_194:
{
if (x_173 == 0)
{
lean_object* x_181; 
lean_dec(x_172);
lean_dec(x_167);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_124)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_124;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_182 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_28;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_37);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_unsigned_to_nat(1u);
x_186 = lean_nat_sub(x_172, x_185);
lean_dec(x_172);
x_187 = lean_box(0);
x_188 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_1, x_187, x_27, x_184, x_11, x_186);
lean_dec(x_27);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
lean_dec(x_167);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_124)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_124;
}
lean_ctor_set(x_189, 0, x_179);
lean_ctor_set(x_189, 1, x_180);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_124);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Array_append___rarg(x_33, x_167);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_2 = x_11;
x_3 = x_191;
x_4 = x_192;
x_5 = x_179;
x_10 = x_180;
goto _start;
}
}
}
}
}
}
}
case 2:
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_35, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_209 = x_35;
} else {
 lean_dec_ref(x_35);
 x_209 = lean_box(0);
}
x_210 = !lean_is_exclusive(x_36);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; 
x_211 = lean_ctor_get(x_36, 1);
x_212 = lean_ctor_get(x_36, 0);
lean_dec(x_212);
x_213 = lean_box(0);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_11);
x_215 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
lean_ctor_set(x_36, 1, x_215);
lean_ctor_set(x_36, 0, x_214);
x_216 = lean_array_get_size(x_27);
x_217 = lean_nat_dec_lt(x_11, x_216);
x_218 = lean_box(3);
if (x_217 == 0)
{
lean_object* x_250; 
x_250 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_219 = x_250;
goto block_249;
}
else
{
lean_object* x_251; 
lean_dec(x_36);
x_251 = lean_array_fget(x_27, x_11);
x_219 = x_251;
goto block_249;
}
block_249:
{
lean_object* x_220; uint8_t x_221; uint8_t x_222; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_220, x_218);
lean_dec(x_220);
if (x_221 == 0)
{
x_222 = x_34;
goto block_247;
}
else
{
uint8_t x_248; 
x_248 = 1;
x_222 = x_248;
goto block_247;
}
block_247:
{
lean_object* x_223; lean_object* x_224; 
if (x_222 == 0)
{
lean_dec(x_219);
x_223 = x_5;
x_224 = x_208;
goto block_238;
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_219, 1);
lean_inc(x_239);
lean_dec(x_219);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_240 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_239, x_5, x_6, x_7, x_8, x_9, x_208);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_223 = x_241;
x_224 = x_242;
goto block_238;
}
else
{
uint8_t x_243; 
lean_dec(x_216);
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_243 = !lean_is_exclusive(x_240);
if (x_243 == 0)
{
return x_240;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_240, 0);
x_245 = lean_ctor_get(x_240, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_240);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
block_238:
{
if (x_217 == 0)
{
lean_object* x_225; 
lean_dec(x_216);
lean_dec(x_211);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_209)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_209;
}
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_226 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_28;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_37);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_unsigned_to_nat(1u);
x_230 = lean_nat_sub(x_216, x_229);
lean_dec(x_216);
x_231 = lean_box(0);
x_232 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(x_1, x_231, x_27, x_228, x_11, x_230);
lean_dec(x_27);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
lean_dec(x_211);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_209)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_209;
}
lean_ctor_set(x_233, 0, x_223);
lean_ctor_set(x_233, 1, x_224);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_209);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_Array_append___rarg(x_33, x_211);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_2 = x_11;
x_3 = x_235;
x_4 = x_236;
x_5 = x_223;
x_10 = x_224;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; 
x_252 = lean_ctor_get(x_36, 1);
lean_inc(x_252);
lean_dec(x_36);
x_253 = lean_box(0);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_11);
x_255 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_array_get_size(x_27);
x_258 = lean_nat_dec_lt(x_11, x_257);
x_259 = lean_box(3);
if (x_258 == 0)
{
lean_object* x_291; 
x_291 = l___private_Init_Util_0__outOfBounds___rarg(x_256);
x_260 = x_291;
goto block_290;
}
else
{
lean_object* x_292; 
lean_dec(x_256);
x_292 = lean_array_fget(x_27, x_11);
x_260 = x_292;
goto block_290;
}
block_290:
{
lean_object* x_261; uint8_t x_262; uint8_t x_263; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_261, x_259);
lean_dec(x_261);
if (x_262 == 0)
{
x_263 = x_34;
goto block_288;
}
else
{
uint8_t x_289; 
x_289 = 1;
x_263 = x_289;
goto block_288;
}
block_288:
{
lean_object* x_264; lean_object* x_265; 
if (x_263 == 0)
{
lean_dec(x_260);
x_264 = x_5;
x_265 = x_208;
goto block_279;
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_260, 1);
lean_inc(x_280);
lean_dec(x_260);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_281 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_280, x_5, x_6, x_7, x_8, x_9, x_208);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_264 = x_282;
x_265 = x_283;
goto block_279;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_257);
lean_dec(x_252);
lean_dec(x_209);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_284 = lean_ctor_get(x_281, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_281, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_286 = x_281;
} else {
 lean_dec_ref(x_281);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
block_279:
{
if (x_258 == 0)
{
lean_object* x_266; 
lean_dec(x_257);
lean_dec(x_252);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_209)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_209;
}
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_267 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_28;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_37);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_unsigned_to_nat(1u);
x_271 = lean_nat_sub(x_257, x_270);
lean_dec(x_257);
x_272 = lean_box(0);
x_273 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(x_1, x_272, x_27, x_269, x_11, x_271);
lean_dec(x_27);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
lean_dec(x_252);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_209)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_209;
}
lean_ctor_set(x_274, 0, x_264);
lean_ctor_set(x_274, 1, x_265);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_209);
x_275 = lean_ctor_get(x_273, 0);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l_Array_append___rarg(x_33, x_252);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_2 = x_11;
x_3 = x_276;
x_4 = x_277;
x_5 = x_264;
x_10 = x_265;
goto _start;
}
}
}
}
}
}
}
case 3:
{
uint8_t x_293; 
lean_dec(x_36);
lean_dec(x_28);
x_293 = !lean_is_exclusive(x_35);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_294 = lean_ctor_get(x_35, 1);
x_295 = lean_ctor_get(x_35, 0);
lean_dec(x_295);
x_296 = lean_array_get_size(x_27);
x_297 = lean_nat_dec_lt(x_11, x_296);
if (x_297 == 0)
{
lean_dec(x_296);
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
uint8_t x_298; 
x_298 = lean_nat_dec_le(x_296, x_296);
if (x_298 == 0)
{
lean_dec(x_296);
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
size_t x_299; size_t x_300; lean_object* x_301; 
lean_free_object(x_35);
x_299 = 0;
x_300 = lean_usize_of_nat(x_296);
lean_dec(x_296);
x_301 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_1, x_33, x_27, x_299, x_300, x_5, x_6, x_7, x_8, x_9, x_294);
lean_dec(x_27);
return x_301;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_302 = lean_ctor_get(x_35, 1);
lean_inc(x_302);
lean_dec(x_35);
x_303 = lean_array_get_size(x_27);
x_304 = lean_nat_dec_lt(x_11, x_303);
if (x_304 == 0)
{
lean_object* x_305; 
lean_dec(x_303);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_5);
lean_ctor_set(x_305, 1, x_302);
return x_305;
}
else
{
uint8_t x_306; 
x_306 = lean_nat_dec_le(x_303, x_303);
if (x_306 == 0)
{
lean_object* x_307; 
lean_dec(x_303);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_5);
lean_ctor_set(x_307, 1, x_302);
return x_307;
}
else
{
size_t x_308; size_t x_309; lean_object* x_310; 
x_308 = 0;
x_309 = lean_usize_of_nat(x_303);
lean_dec(x_303);
x_310 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_1, x_33, x_27, x_308, x_309, x_5, x_6, x_7, x_8, x_9, x_302);
lean_dec(x_27);
return x_310;
}
}
}
}
case 4:
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_311 = lean_ctor_get(x_35, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_312 = x_35;
} else {
 lean_dec_ref(x_35);
 x_312 = lean_box(0);
}
x_313 = !lean_is_exclusive(x_36);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; 
x_314 = lean_ctor_get(x_36, 1);
x_315 = lean_ctor_get(x_36, 0);
lean_dec(x_315);
x_316 = lean_box(0);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_11);
x_318 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
lean_ctor_set(x_36, 1, x_318);
lean_ctor_set(x_36, 0, x_317);
x_319 = lean_array_get_size(x_27);
x_320 = lean_nat_dec_lt(x_11, x_319);
x_321 = lean_box(3);
if (x_320 == 0)
{
lean_object* x_353; 
x_353 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_322 = x_353;
goto block_352;
}
else
{
lean_object* x_354; 
lean_dec(x_36);
x_354 = lean_array_fget(x_27, x_11);
x_322 = x_354;
goto block_352;
}
block_352:
{
lean_object* x_323; uint8_t x_324; uint8_t x_325; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_323, x_321);
lean_dec(x_323);
if (x_324 == 0)
{
x_325 = x_34;
goto block_350;
}
else
{
uint8_t x_351; 
x_351 = 1;
x_325 = x_351;
goto block_350;
}
block_350:
{
lean_object* x_326; lean_object* x_327; 
if (x_325 == 0)
{
lean_dec(x_322);
x_326 = x_5;
x_327 = x_311;
goto block_341;
}
else
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_322, 1);
lean_inc(x_342);
lean_dec(x_322);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_343 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_342, x_5, x_6, x_7, x_8, x_9, x_311);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_326 = x_344;
x_327 = x_345;
goto block_341;
}
else
{
uint8_t x_346; 
lean_dec(x_319);
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_346 = !lean_is_exclusive(x_343);
if (x_346 == 0)
{
return x_343;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_343, 0);
x_348 = lean_ctor_get(x_343, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_343);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
block_341:
{
if (x_320 == 0)
{
lean_object* x_328; 
lean_dec(x_319);
lean_dec(x_314);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_312)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_312;
}
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_329 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_28;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_329);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_37);
lean_ctor_set(x_331, 1, x_330);
x_332 = lean_unsigned_to_nat(1u);
x_333 = lean_nat_sub(x_319, x_332);
lean_dec(x_319);
x_334 = lean_box(0);
x_335 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(x_1, x_334, x_27, x_331, x_11, x_333);
lean_dec(x_27);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; 
lean_dec(x_314);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_312)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_312;
}
lean_ctor_set(x_336, 0, x_326);
lean_ctor_set(x_336, 1, x_327);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_312);
x_337 = lean_ctor_get(x_335, 0);
lean_inc(x_337);
lean_dec(x_335);
x_338 = l_Array_append___rarg(x_33, x_314);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_2 = x_11;
x_3 = x_338;
x_4 = x_339;
x_5 = x_326;
x_10 = x_327;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; lean_object* x_363; 
x_355 = lean_ctor_get(x_36, 1);
lean_inc(x_355);
lean_dec(x_36);
x_356 = lean_box(0);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_11);
x_358 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
x_360 = lean_array_get_size(x_27);
x_361 = lean_nat_dec_lt(x_11, x_360);
x_362 = lean_box(3);
if (x_361 == 0)
{
lean_object* x_394; 
x_394 = l___private_Init_Util_0__outOfBounds___rarg(x_359);
x_363 = x_394;
goto block_393;
}
else
{
lean_object* x_395; 
lean_dec(x_359);
x_395 = lean_array_fget(x_27, x_11);
x_363 = x_395;
goto block_393;
}
block_393:
{
lean_object* x_364; uint8_t x_365; uint8_t x_366; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_364, x_362);
lean_dec(x_364);
if (x_365 == 0)
{
x_366 = x_34;
goto block_391;
}
else
{
uint8_t x_392; 
x_392 = 1;
x_366 = x_392;
goto block_391;
}
block_391:
{
lean_object* x_367; lean_object* x_368; 
if (x_366 == 0)
{
lean_dec(x_363);
x_367 = x_5;
x_368 = x_311;
goto block_382;
}
else
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_363, 1);
lean_inc(x_383);
lean_dec(x_363);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_384 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_383, x_5, x_6, x_7, x_8, x_9, x_311);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_367 = x_385;
x_368 = x_386;
goto block_382;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_360);
lean_dec(x_355);
lean_dec(x_312);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_387 = lean_ctor_get(x_384, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_384, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_389 = x_384;
} else {
 lean_dec_ref(x_384);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_388);
return x_390;
}
}
block_382:
{
if (x_361 == 0)
{
lean_object* x_369; 
lean_dec(x_360);
lean_dec(x_355);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_312)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_312;
}
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_370 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_28;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_37);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_unsigned_to_nat(1u);
x_374 = lean_nat_sub(x_360, x_373);
lean_dec(x_360);
x_375 = lean_box(0);
x_376 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(x_1, x_375, x_27, x_372, x_11, x_374);
lean_dec(x_27);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; 
lean_dec(x_355);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_312)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_312;
}
lean_ctor_set(x_377, 0, x_367);
lean_ctor_set(x_377, 1, x_368);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_312);
x_378 = lean_ctor_get(x_376, 0);
lean_inc(x_378);
lean_dec(x_376);
x_379 = l_Array_append___rarg(x_33, x_355);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_2 = x_11;
x_3 = x_379;
x_4 = x_380;
x_5 = x_367;
x_10 = x_368;
goto _start;
}
}
}
}
}
}
}
case 5:
{
lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_396 = lean_ctor_get(x_35, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_397 = x_35;
} else {
 lean_dec_ref(x_35);
 x_397 = lean_box(0);
}
x_398 = !lean_is_exclusive(x_36);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; 
x_399 = lean_ctor_get(x_36, 1);
x_400 = lean_ctor_get(x_36, 0);
lean_dec(x_400);
x_401 = lean_box(0);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_11);
x_403 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
lean_ctor_set(x_36, 1, x_403);
lean_ctor_set(x_36, 0, x_402);
x_404 = lean_array_get_size(x_27);
x_405 = lean_nat_dec_lt(x_11, x_404);
x_406 = lean_box(3);
if (x_405 == 0)
{
lean_object* x_455; 
x_455 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_407 = x_455;
goto block_454;
}
else
{
lean_object* x_456; 
lean_dec(x_36);
x_456 = lean_array_fget(x_27, x_11);
x_407 = x_456;
goto block_454;
}
block_454:
{
lean_object* x_408; uint8_t x_409; uint8_t x_410; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_408, x_406);
lean_dec(x_408);
if (x_409 == 0)
{
x_410 = x_34;
goto block_452;
}
else
{
uint8_t x_453; 
x_453 = 1;
x_410 = x_453;
goto block_452;
}
block_452:
{
lean_object* x_411; lean_object* x_412; 
if (x_410 == 0)
{
lean_dec(x_407);
x_411 = x_5;
x_412 = x_396;
goto block_443;
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_407, 1);
lean_inc(x_444);
lean_dec(x_407);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_445 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_444, x_5, x_6, x_7, x_8, x_9, x_396);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
x_411 = x_446;
x_412 = x_447;
goto block_443;
}
else
{
uint8_t x_448; 
lean_dec(x_404);
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_448 = !lean_is_exclusive(x_445);
if (x_448 == 0)
{
return x_445;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_445, 0);
x_450 = lean_ctor_get(x_445, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_445);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
return x_451;
}
}
}
block_443:
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_413 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_414 = lean_alloc_ctor(0, 2, 0);
} else {
 x_414 = x_28;
}
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_413);
lean_inc(x_414);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_37);
lean_ctor_set(x_415, 1, x_414);
x_416 = lean_unsigned_to_nat(1u);
x_417 = lean_nat_sub(x_404, x_416);
lean_dec(x_404);
if (x_405 == 0)
{
lean_dec(x_415);
lean_dec(x_399);
x_418 = x_411;
x_419 = x_412;
goto block_430;
}
else
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_box(0);
lean_inc(x_417);
x_432 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(x_1, x_431, x_27, x_415, x_11, x_417);
if (lean_obj_tag(x_432) == 0)
{
lean_dec(x_399);
x_418 = x_411;
x_419 = x_412;
goto block_430;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
lean_dec(x_432);
lean_inc(x_33);
x_434 = l_Array_append___rarg(x_33, x_399);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_436 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_434, x_435, x_411, x_6, x_7, x_8, x_9, x_412);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_418 = x_437;
x_419 = x_438;
goto block_430;
}
else
{
uint8_t x_439; 
lean_dec(x_417);
lean_dec(x_414);
lean_dec(x_397);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_439 = !lean_is_exclusive(x_436);
if (x_439 == 0)
{
return x_436;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_436, 0);
x_441 = lean_ctor_get(x_436, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_436);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
}
block_430:
{
if (x_405 == 0)
{
lean_object* x_420; 
lean_dec(x_417);
lean_dec(x_414);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_397)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_397;
}
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_421 = lean_box(4);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_414);
x_423 = lean_box(0);
x_424 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_1, x_423, x_27, x_422, x_11, x_417);
lean_dec(x_27);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_397)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_397;
}
lean_ctor_set(x_425, 0, x_418);
lean_ctor_set(x_425, 1, x_419);
return x_425;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_397);
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
lean_dec(x_424);
x_427 = l_Array_append___rarg(x_33, x_413);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_2 = x_11;
x_3 = x_427;
x_4 = x_428;
x_5 = x_418;
x_10 = x_419;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; 
x_457 = lean_ctor_get(x_36, 1);
lean_inc(x_457);
lean_dec(x_36);
x_458 = lean_box(0);
x_459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_11);
x_460 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
x_462 = lean_array_get_size(x_27);
x_463 = lean_nat_dec_lt(x_11, x_462);
x_464 = lean_box(3);
if (x_463 == 0)
{
lean_object* x_513; 
x_513 = l___private_Init_Util_0__outOfBounds___rarg(x_461);
x_465 = x_513;
goto block_512;
}
else
{
lean_object* x_514; 
lean_dec(x_461);
x_514 = lean_array_fget(x_27, x_11);
x_465 = x_514;
goto block_512;
}
block_512:
{
lean_object* x_466; uint8_t x_467; uint8_t x_468; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_466, x_464);
lean_dec(x_466);
if (x_467 == 0)
{
x_468 = x_34;
goto block_510;
}
else
{
uint8_t x_511; 
x_511 = 1;
x_468 = x_511;
goto block_510;
}
block_510:
{
lean_object* x_469; lean_object* x_470; 
if (x_468 == 0)
{
lean_dec(x_465);
x_469 = x_5;
x_470 = x_396;
goto block_501;
}
else
{
lean_object* x_502; lean_object* x_503; 
x_502 = lean_ctor_get(x_465, 1);
lean_inc(x_502);
lean_dec(x_465);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_503 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_502, x_5, x_6, x_7, x_8, x_9, x_396);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_469 = x_504;
x_470 = x_505;
goto block_501;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_462);
lean_dec(x_457);
lean_dec(x_397);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_506 = lean_ctor_get(x_503, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_503, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_508 = x_503;
} else {
 lean_dec_ref(x_503);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(1, 2, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
}
block_501:
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_471 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_28;
}
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_471);
lean_inc(x_472);
x_473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_473, 0, x_37);
lean_ctor_set(x_473, 1, x_472);
x_474 = lean_unsigned_to_nat(1u);
x_475 = lean_nat_sub(x_462, x_474);
lean_dec(x_462);
if (x_463 == 0)
{
lean_dec(x_473);
lean_dec(x_457);
x_476 = x_469;
x_477 = x_470;
goto block_488;
}
else
{
lean_object* x_489; lean_object* x_490; 
x_489 = lean_box(0);
lean_inc(x_475);
x_490 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(x_1, x_489, x_27, x_473, x_11, x_475);
if (lean_obj_tag(x_490) == 0)
{
lean_dec(x_457);
x_476 = x_469;
x_477 = x_470;
goto block_488;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
lean_dec(x_490);
lean_inc(x_33);
x_492 = l_Array_append___rarg(x_33, x_457);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec(x_491);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_494 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_492, x_493, x_469, x_6, x_7, x_8, x_9, x_470);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_476 = x_495;
x_477 = x_496;
goto block_488;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_475);
lean_dec(x_472);
lean_dec(x_397);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_497 = lean_ctor_get(x_494, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_494, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_499 = x_494;
} else {
 lean_dec_ref(x_494);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
}
block_488:
{
if (x_463 == 0)
{
lean_object* x_478; 
lean_dec(x_475);
lean_dec(x_472);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_397)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_397;
}
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_479 = lean_box(4);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_472);
x_481 = lean_box(0);
x_482 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_1, x_481, x_27, x_480, x_11, x_475);
lean_dec(x_27);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_397)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_397;
}
lean_ctor_set(x_483, 0, x_476);
lean_ctor_set(x_483, 1, x_477);
return x_483;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_397);
x_484 = lean_ctor_get(x_482, 0);
lean_inc(x_484);
lean_dec(x_482);
x_485 = l_Array_append___rarg(x_33, x_471);
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec(x_484);
x_2 = x_11;
x_3 = x_485;
x_4 = x_486;
x_5 = x_476;
x_10 = x_477;
goto _start;
}
}
}
}
}
}
}
}
default: 
{
lean_object* x_515; lean_object* x_516; uint8_t x_517; 
x_515 = lean_ctor_get(x_35, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_516 = x_35;
} else {
 lean_dec_ref(x_35);
 x_516 = lean_box(0);
}
x_517 = !lean_is_exclusive(x_36);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; uint8_t x_524; lean_object* x_525; lean_object* x_526; 
x_518 = lean_ctor_get(x_36, 1);
x_519 = lean_ctor_get(x_36, 0);
lean_dec(x_519);
x_520 = lean_box(0);
x_521 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_521, 0, x_520);
lean_ctor_set(x_521, 1, x_11);
x_522 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
lean_ctor_set(x_36, 1, x_522);
lean_ctor_set(x_36, 0, x_521);
x_523 = lean_array_get_size(x_27);
x_524 = lean_nat_dec_lt(x_11, x_523);
x_525 = lean_box(3);
if (x_524 == 0)
{
lean_object* x_557; 
x_557 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_526 = x_557;
goto block_556;
}
else
{
lean_object* x_558; 
lean_dec(x_36);
x_558 = lean_array_fget(x_27, x_11);
x_526 = x_558;
goto block_556;
}
block_556:
{
lean_object* x_527; uint8_t x_528; uint8_t x_529; 
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_527, x_525);
lean_dec(x_527);
if (x_528 == 0)
{
x_529 = x_34;
goto block_554;
}
else
{
uint8_t x_555; 
x_555 = 1;
x_529 = x_555;
goto block_554;
}
block_554:
{
lean_object* x_530; lean_object* x_531; 
if (x_529 == 0)
{
lean_dec(x_526);
x_530 = x_5;
x_531 = x_515;
goto block_545;
}
else
{
lean_object* x_546; lean_object* x_547; 
x_546 = lean_ctor_get(x_526, 1);
lean_inc(x_546);
lean_dec(x_526);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_547 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_546, x_5, x_6, x_7, x_8, x_9, x_515);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; 
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
lean_dec(x_547);
x_530 = x_548;
x_531 = x_549;
goto block_545;
}
else
{
uint8_t x_550; 
lean_dec(x_523);
lean_dec(x_518);
lean_dec(x_516);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_550 = !lean_is_exclusive(x_547);
if (x_550 == 0)
{
return x_547;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_551 = lean_ctor_get(x_547, 0);
x_552 = lean_ctor_get(x_547, 1);
lean_inc(x_552);
lean_inc(x_551);
lean_dec(x_547);
x_553 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_552);
return x_553;
}
}
}
block_545:
{
if (x_524 == 0)
{
lean_object* x_532; 
lean_dec(x_523);
lean_dec(x_518);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_516)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_516;
}
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
return x_532;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_533 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_534 = x_28;
}
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_533);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_37);
lean_ctor_set(x_535, 1, x_534);
x_536 = lean_unsigned_to_nat(1u);
x_537 = lean_nat_sub(x_523, x_536);
lean_dec(x_523);
x_538 = lean_box(0);
x_539 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(x_1, x_538, x_27, x_535, x_11, x_537);
lean_dec(x_27);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; 
lean_dec(x_518);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_516)) {
 x_540 = lean_alloc_ctor(0, 2, 0);
} else {
 x_540 = x_516;
}
lean_ctor_set(x_540, 0, x_530);
lean_ctor_set(x_540, 1, x_531);
return x_540;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_516);
x_541 = lean_ctor_get(x_539, 0);
lean_inc(x_541);
lean_dec(x_539);
x_542 = l_Array_append___rarg(x_33, x_518);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
lean_dec(x_541);
x_2 = x_11;
x_3 = x_542;
x_4 = x_543;
x_5 = x_530;
x_10 = x_531;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; uint8_t x_565; lean_object* x_566; lean_object* x_567; 
x_559 = lean_ctor_get(x_36, 1);
lean_inc(x_559);
lean_dec(x_36);
x_560 = lean_box(0);
x_561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_561, 1, x_11);
x_562 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg(x_1);
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
x_564 = lean_array_get_size(x_27);
x_565 = lean_nat_dec_lt(x_11, x_564);
x_566 = lean_box(3);
if (x_565 == 0)
{
lean_object* x_598; 
x_598 = l___private_Init_Util_0__outOfBounds___rarg(x_563);
x_567 = x_598;
goto block_597;
}
else
{
lean_object* x_599; 
lean_dec(x_563);
x_599 = lean_array_fget(x_27, x_11);
x_567 = x_599;
goto block_597;
}
block_597:
{
lean_object* x_568; uint8_t x_569; uint8_t x_570; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_115____rarg(x_568, x_566);
lean_dec(x_568);
if (x_569 == 0)
{
x_570 = x_34;
goto block_595;
}
else
{
uint8_t x_596; 
x_596 = 1;
x_570 = x_596;
goto block_595;
}
block_595:
{
lean_object* x_571; lean_object* x_572; 
if (x_570 == 0)
{
lean_dec(x_567);
x_571 = x_5;
x_572 = x_515;
goto block_586;
}
else
{
lean_object* x_587; lean_object* x_588; 
x_587 = lean_ctor_get(x_567, 1);
lean_inc(x_587);
lean_dec(x_567);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_588 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_1, x_11, x_33, x_587, x_5, x_6, x_7, x_8, x_9, x_515);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
lean_dec(x_588);
x_571 = x_589;
x_572 = x_590;
goto block_586;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec(x_564);
lean_dec(x_559);
lean_dec(x_516);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_591 = lean_ctor_get(x_588, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_588, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_593 = x_588;
} else {
 lean_dec_ref(x_588);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(1, 2, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_592);
return x_594;
}
}
block_586:
{
if (x_565 == 0)
{
lean_object* x_573; 
lean_dec(x_564);
lean_dec(x_559);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_516)) {
 x_573 = lean_alloc_ctor(0, 2, 0);
} else {
 x_573 = x_516;
}
lean_ctor_set(x_573, 0, x_571);
lean_ctor_set(x_573, 1, x_572);
return x_573;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_574 = l_Lean_Meta_DiscrTree_instInhabitedTrie___rarg___closed__1;
if (lean_is_scalar(x_28)) {
 x_575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_575 = x_28;
}
lean_ctor_set(x_575, 0, x_574);
lean_ctor_set(x_575, 1, x_574);
x_576 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_576, 0, x_37);
lean_ctor_set(x_576, 1, x_575);
x_577 = lean_unsigned_to_nat(1u);
x_578 = lean_nat_sub(x_564, x_577);
lean_dec(x_564);
x_579 = lean_box(0);
x_580 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(x_1, x_579, x_27, x_576, x_11, x_578);
lean_dec(x_27);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; 
lean_dec(x_559);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_516)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_516;
}
lean_ctor_set(x_581, 0, x_571);
lean_ctor_set(x_581, 1, x_572);
return x_581;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_dec(x_516);
x_582 = lean_ctor_get(x_580, 0);
lean_inc(x_582);
lean_dec(x_580);
x_583 = l_Array_append___rarg(x_33, x_559);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec(x_582);
x_2 = x_11;
x_3 = x_583;
x_4 = x_584;
x_5 = x_571;
x_10 = x_572;
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
else
{
uint8_t x_600; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_600 = !lean_is_exclusive(x_35);
if (x_600 == 0)
{
return x_35;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_35, 0);
x_602 = lean_ctor_get(x_35, 1);
lean_inc(x_602);
lean_inc(x_601);
lean_dec(x_35);
x_603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set(x_603, 1, x_602);
return x_603;
}
}
}
else
{
lean_object* x_604; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_604, 0, x_5);
lean_ctor_set(x_604, 1, x_10);
return x_604;
}
}
else
{
lean_object* x_605; lean_object* x_606; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_605 = l_Array_append___rarg(x_5, x_26);
x_606 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_606, 0, x_605);
lean_ctor_set(x_606, 1, x_10);
return x_606;
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
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
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
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__1);
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
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___lambda__1___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__2 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__2();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_elimLooseBVarsByBeta___closed__2);
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
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__2___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__3___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
