// Lean compiler output
// Module: Lean.Meta.DiscrTree
// Imports: Init Lean.Meta.Basic Lean.Meta.FunInfo Lean.Meta.InferType Lean.Meta.WHNF Lean.Meta.Match.MatcherInfo
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_join(lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__10;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__6;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__4;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__8;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__4___rarg(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_whnfDT(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_MetavarContext_getExprAssignmentDomain___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_format(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfUntilBadKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_whnfDT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__1;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__4;
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__6;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3(lean_object*);
uint8_t l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_process___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__4(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__9;
lean_object* l_Subarray_popFront___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lt___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__6;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__2___rarg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__1___rarg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify_process___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__5;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6(lean_object*);
lean_object* l_List_format___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId;
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__5;
LEAN_EXPORT lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfEta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity(lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10(lean_object*);
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1(lean_object*);
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__1;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4;
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__2;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify_process(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__9;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__1;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__7;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_instToFormatKey___closed__1;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1;
static lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2;
static lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
static lean_object* l_Lean_Meta_DiscrTree_mkPath___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__4;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object*);
uint8_t l_Array_contains___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_process(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg(lean_object*, size_t, lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7;
static lean_object* l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_String_quote(lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12(lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatKey;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__2;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1(lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_format___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_hasNoindexAnnotation___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2(lean_object*);
lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__7;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object*);
static lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfUntilBadKey_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instLTKey;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__7;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5(lean_object*);
uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1___rarg(size_t, size_t, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19(lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey(lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isStrictImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object* x_1, lean_object* x_2) {
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
x_12 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_1);
x_13 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_2);
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
x_24 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_1);
x_25 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_2);
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
x_30 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_1);
x_31 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_2);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
x_37 = l_Lean_Name_quickLt(x_33, x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = lean_name_eq(x_33, x_35);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = 0;
return x_39;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_lt(x_34, x_36);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = 1;
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_1);
x_43 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_2);
x_44 = lean_nat_dec_lt(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
return x_44;
}
}
default: 
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_1);
x_46 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_2);
x_47 = lean_nat_dec_lt(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_DiscrTree_Key_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instLTKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Meta_DiscrTree_Key_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_DiscrTree_instDecidableLtKeyInstLTKey(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("*");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Key_format___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("◾");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Key_format___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("→");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Key_format___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Key_format___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_format(lean_object* x_1) {
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
x_5 = lean_alloc_ctor(2, 1, 0);
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
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 3:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_DiscrTree_Key_format___closed__2;
return x_9;
}
case 4:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_DiscrTree_Key_format___closed__4;
return x_10;
}
case 5:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_DiscrTree_Key_format___closed__6;
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
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_DiscrTree_Key_format___closed__8;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Nat_repr(x_13);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(4, 2, 0);
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
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToFormatKey___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_format), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToFormatKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instToFormatKey___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity(lean_object* x_1) {
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
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(1u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_Key_arity(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_empty___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_DiscrTree_empty___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_empty___closed__3;
return x_2;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" => ");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_Meta_DiscrTree_Key_format(x_8);
x_11 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_1);
x_13 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_9);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_20 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = 0;
x_22 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_24);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Meta_DiscrTree_Key_format(x_28);
x_31 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_1);
x_33 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_29);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_40 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = 0;
x_42 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_box(1);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
x_2 = x_27;
x_3 = x_45;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("node");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
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
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Array_isEmpty___rarg(x_3);
x_6 = lean_array_to_list(lean_box(0), x_4);
x_7 = lean_box(0);
lean_inc(x_1);
x_8 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(x_1, x_6, x_7);
x_9 = l_Std_Format_join(x_8);
if (x_5 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_10 = lean_array_to_list(lean_box(0), x_3);
x_11 = l_List_format___rarg(x_1, x_10);
x_12 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__6;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__4;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
x_19 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_24 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = 0;
x_26 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
lean_dec(x_1);
x_28 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__7;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
x_30 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_35 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = 0;
x_37 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_36);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_instToFormatTrie___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = l_Lean_Meta_DiscrTree_Key_format(x_10);
x_15 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_1);
x_17 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_11);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_24 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = 0;
x_26 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_unbox(x_13);
lean_dec(x_13);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_3 = x_9;
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_3 = x_9;
x_5 = x_40;
goto _start;
}
}
case 1:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_42);
lean_dec(x_7);
lean_inc(x_1);
x_43 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg(x_1, x_42, x_5);
x_3 = x_9;
x_5 = x_43;
goto _start;
}
default: 
{
x_3 = x_9;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_Meta_DiscrTree_Key_format(x_3);
x_8 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_4);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_17 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = 0;
x_19 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_unbox(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_box(1);
lean_inc(x_5);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_box(0);
lean_inc(x_5);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg(x_1, x_4, x_9, x_10, x_3);
lean_dec(x_4);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_MetavarContext_getExprAssignmentDomain___spec__4___rarg(x_14, x_12, x_13, lean_box(0), x_15, x_3);
lean_dec(x_13);
lean_dec(x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg), 3, 0);
return x_2;
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = l_Lean_Meta_DiscrTree_format___rarg___closed__1;
x_4 = l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_instToFormatDiscrTree___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_discr_tree_tmp");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
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
x_2 = l_Lean_mkMVar(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_empty___closed__3;
return x_2;
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
x_1 = lean_mk_string("Nat");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("OfNat");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofNat");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("zero");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
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
x_30 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__10;
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
x_34 = l_Lean_Expr_getAppNumArgsAux(x_1, x_33);
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
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6;
x_9 = lean_name_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
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
x_14 = l_Lean_Expr_getAppNumArgsAux(x_1, x_13);
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
x_17 = l_Lean_Expr_getAppNumArgsAux(x_1, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_1);
x_20 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
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
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2;
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
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2;
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
x_1 = lean_mk_string("HAdd");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hAdd");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__2;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Add");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("add");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__6;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_65; lean_object* x_104; uint8_t x_105; 
x_104 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__9;
x_105 = lean_name_eq(x_1, x_104);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_box(0);
x_65 = x_106;
goto block_103;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_unsigned_to_nat(0u);
x_108 = l_Lean_Expr_getAppNumArgsAux(x_2, x_107);
x_109 = lean_unsigned_to_nat(2u);
x_110 = lean_nat_dec_eq(x_108, x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_box(0);
x_65 = x_111;
goto block_103;
}
else
{
lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_113 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_112);
x_114 = lean_box(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_7);
return x_115;
}
}
block_64:
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_8);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__4;
x_10 = lean_name_eq(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__10;
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
x_17 = l_Lean_Expr_getAppNumArgsAux(x_2, x_16);
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
x_23 = l_Lean_Expr_getAppNumArgsAux(x_2, x_22);
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
x_26 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__10;
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
block_103:
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_65);
x_66 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__8;
x_67 = lean_name_eq(x_1, x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_box(0);
x_8 = x_68;
goto block_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Lean_Expr_getAppNumArgsAux(x_2, x_69);
x_71 = lean_unsigned_to_nat(4u);
x_72 = lean_nat_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_70);
x_73 = lean_box(0);
x_8 = x_73;
goto block_64;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_nat_sub(x_70, x_69);
lean_dec(x_70);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_74, x_75);
lean_dec(x_74);
lean_inc(x_2);
x_77 = l_Lean_Expr_getRevArg_x21(x_2, x_76);
x_78 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType(x_77, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
uint8_t x_81; 
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_78);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 0);
lean_dec(x_82);
x_83 = 0;
x_84 = lean_box(x_83);
lean_ctor_set(x_78, 0, x_84);
return x_78;
}
else
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = 0;
x_87 = lean_box(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_78);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_78, 0);
lean_dec(x_90);
x_91 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_92 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_91);
x_93 = lean_box(x_92);
lean_ctor_set(x_78, 0, x_93);
return x_78;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_78, 1);
lean_inc(x_94);
lean_dec(x_78);
x_95 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_96 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_95);
x_97 = lean_box(x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_78);
if (x_99 == 0)
{
return x_78;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_78, 0);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_78);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
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
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
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
x_1 = lean_mk_string("noindex");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfEta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_11 = l_Lean_Expr_etaExpandedStrict_x3f(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_12; 
lean_free_object(x_7);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_1 = x_12;
x_6 = x_10;
goto _start;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
lean_inc(x_14);
x_16 = l_Lean_Expr_etaExpandedStrict_x3f(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_1 = x_18;
x_6 = x_15;
goto _start;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfUntilBadKey_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_10 = l_Lean_Meta_unfoldDefinition_x3f(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l_Lean_Expr_getAppFn(x_19);
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_free_object(x_10);
lean_dec(x_8);
x_1 = x_19;
x_6 = x_17;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = l_Lean_Expr_getAppFn(x_24);
x_26 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_8);
x_1 = x_24;
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
return x_7;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfUntilBadKey(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfUntilBadKey_step(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_11 = l_Lean_Expr_etaExpandedStrict_x3f(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_12; 
lean_free_object(x_7);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_1 = x_12;
x_6 = x_10;
goto _start;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
lean_inc(x_14);
x_16 = l_Lean_Expr_etaExpandedStrict_x3f(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_1 = x_18;
x_6 = x_15;
goto _start;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_whnfDT(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_2 == 0)
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfEta(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfUntilBadKey(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_whnfDT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_DiscrTree_whnfDT(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_14 = l_Lean_Meta_getFunInfoNArgs(x_3, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_12, x_18);
lean_dec(x_12);
x_20 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_17, x_19, x_1, x_4, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_13);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Meta_DiscrTree_whnfDT(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Expr_getAppNumArgsAux(x_12, x_16);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_19 = l_Lean_Meta_getFunInfoNArgs(x_14, x_17, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_17, x_23);
lean_dec(x_17);
x_25 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_22, x_24, x_12, x_2, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_18);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
case 2:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_12);
x_41 = lean_ctor_get(x_14, 0);
lean_inc(x_41);
lean_dec(x_14);
x_42 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId;
x_43 = lean_name_eq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_free_object(x_10);
x_44 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(x_41, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 0);
lean_dec(x_48);
x_49 = lean_box(3);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_2);
lean_ctor_set(x_44, 0, x_50);
return x_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec(x_44);
x_52 = lean_box(3);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_2);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_44, 0);
lean_dec(x_56);
x_57 = lean_box(4);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_2);
lean_ctor_set(x_44, 0, x_58);
return x_44;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_dec(x_44);
x_60 = lean_box(4);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_2);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_44);
if (x_63 == 0)
{
return x_44;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_44, 0);
x_65 = lean_ctor_get(x_44, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_44);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = lean_box(3);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_2);
lean_ctor_set(x_10, 0, x_68);
return x_10;
}
}
case 4:
{
lean_free_object(x_10);
if (x_1 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_14, 0);
lean_inc(x_69);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_12);
x_70 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar(x_69, x_12, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_box(0);
x_75 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_12, x_69, x_14, x_2, x_74, x_4, x_5, x_6, x_7, x_73);
return x_75;
}
else
{
uint8_t x_76; 
lean_dec(x_69);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_76 = !lean_is_exclusive(x_70);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_70, 0);
lean_dec(x_77);
x_78 = lean_box(3);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_2);
lean_ctor_set(x_70, 0, x_79);
return x_70;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
lean_dec(x_70);
x_81 = lean_box(3);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_2);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_69);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_70);
if (x_84 == 0)
{
return x_70;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_70, 0);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_70);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_14, 0);
lean_inc(x_88);
x_89 = lean_box(0);
x_90 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_12, x_88, x_14, x_2, x_89, x_4, x_5, x_6, x_7, x_13);
return x_90;
}
}
case 7:
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_91 = lean_ctor_get(x_14, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_14, 2);
lean_inc(x_92);
lean_dec(x_14);
x_93 = l_Lean_Expr_hasLooseBVars(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_array_push(x_2, x_91);
x_95 = lean_array_push(x_94, x_92);
x_96 = lean_box(5);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_10, 0, x_97);
return x_10;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_92);
lean_dec(x_91);
x_98 = lean_box(4);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_2);
lean_ctor_set(x_10, 0, x_99);
return x_10;
}
}
case 9:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_100 = lean_ctor_get(x_14, 0);
lean_inc(x_100);
lean_dec(x_14);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_2);
lean_ctor_set(x_10, 0, x_102);
return x_10;
}
case 11:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_103 = lean_ctor_get(x_14, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_14, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_14, 2);
lean_inc(x_105);
lean_dec(x_14);
x_106 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_array_push(x_2, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_10, 0, x_108);
return x_10;
}
default: 
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_109 = lean_box(4);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_2);
lean_ctor_set(x_10, 0, x_110);
return x_10;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_10, 0);
x_112 = lean_ctor_get(x_10, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_10);
x_113 = l_Lean_Expr_getAppFn(x_111);
switch (lean_obj_tag(x_113)) {
case 1:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unsigned_to_nat(0u);
x_116 = l_Lean_Expr_getAppNumArgsAux(x_111, x_115);
lean_inc(x_116);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_116);
x_118 = l_Lean_Meta_getFunInfoNArgs(x_113, x_116, x_4, x_5, x_6, x_7, x_112);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_sub(x_116, x_122);
lean_dec(x_116);
x_124 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(x_121, x_123, x_111, x_2, x_4, x_5, x_6, x_7, x_120);
lean_dec(x_121);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_117);
lean_ctor_set(x_128, 1, x_125);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_117);
x_130 = lean_ctor_get(x_124, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_132 = x_124;
} else {
 lean_dec_ref(x_124);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_134 = lean_ctor_get(x_118, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_118, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_136 = x_118;
} else {
 lean_dec_ref(x_118);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
case 2:
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_dec(x_111);
x_138 = lean_ctor_get(x_113, 0);
lean_inc(x_138);
lean_dec(x_113);
x_139 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId;
x_140 = lean_name_eq(x_138, x_139);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(x_138, x_4, x_5, x_6, x_7, x_112);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_145 = x_141;
} else {
 lean_dec_ref(x_141);
 x_145 = lean_box(0);
}
x_146 = lean_box(3);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_2);
if (lean_is_scalar(x_145)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_145;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_144);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_ctor_get(x_141, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_150 = x_141;
} else {
 lean_dec_ref(x_141);
 x_150 = lean_box(0);
}
x_151 = lean_box(4);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_2);
if (lean_is_scalar(x_150)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_150;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_149);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_2);
x_154 = lean_ctor_get(x_141, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_141, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_156 = x_141;
} else {
 lean_dec_ref(x_141);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_138);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_158 = lean_box(3);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_2);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_112);
return x_160;
}
}
case 4:
{
if (x_1 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_113, 0);
lean_inc(x_161);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_111);
x_162 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar(x_161, x_111, x_4, x_5, x_6, x_7, x_112);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_box(0);
x_167 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_111, x_161, x_113, x_2, x_166, x_4, x_5, x_6, x_7, x_165);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_161);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_168 = lean_ctor_get(x_162, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_169 = x_162;
} else {
 lean_dec_ref(x_162);
 x_169 = lean_box(0);
}
x_170 = lean_box(3);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_2);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_168);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_161);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_173 = lean_ctor_get(x_162, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_162, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_175 = x_162;
} else {
 lean_dec_ref(x_162);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_113, 0);
lean_inc(x_177);
x_178 = lean_box(0);
x_179 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_111, x_177, x_113, x_2, x_178, x_4, x_5, x_6, x_7, x_112);
return x_179;
}
}
case 7:
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_180 = lean_ctor_get(x_113, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_113, 2);
lean_inc(x_181);
lean_dec(x_113);
x_182 = l_Lean_Expr_hasLooseBVars(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_array_push(x_2, x_180);
x_184 = lean_array_push(x_183, x_181);
x_185 = lean_box(5);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_112);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_181);
lean_dec(x_180);
x_188 = lean_box(4);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_2);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_112);
return x_190;
}
}
case 9:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_191 = lean_ctor_get(x_113, 0);
lean_inc(x_191);
lean_dec(x_113);
x_192 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_2);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_112);
return x_194;
}
case 11:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_195 = lean_ctor_get(x_113, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_113, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_113, 2);
lean_inc(x_197);
lean_dec(x_113);
x_198 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
x_199 = lean_array_push(x_2, x_197);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_112);
return x_201;
}
default: 
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_202 = lean_box(4);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_2);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_112);
return x_204;
}
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_205 = !lean_is_exclusive(x_10);
if (x_205 == 0)
{
return x_10;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_10, 0);
x_207 = lean_ctor_get(x_10, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_10);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_209 = lean_box(3);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_2);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_8);
return x_211;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Array_isEmpty___rarg(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_instInhabitedExpr;
x_11 = l_Array_back___rarg(x_10, x_2);
x_12 = lean_array_pop(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(x_1, x_12, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_array_push(x_3, x_16);
x_19 = 0;
x_1 = x_19;
x_2 = x_17;
x_3 = x_18;
x_8 = x_15;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_DiscrTree_mkPathAux(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_DiscrTree_mkPath___closed__1;
x_8 = lean_array_push(x_7, x_1);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = 2;
lean_ctor_set_uint8(x_10, 5, x_12);
x_13 = 1;
x_14 = l_Lean_Meta_DiscrTree_mkPathAux(x_13, x_8, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_23 = lean_ctor_get_uint8(x_10, 0);
x_24 = lean_ctor_get_uint8(x_10, 1);
x_25 = lean_ctor_get_uint8(x_10, 2);
x_26 = lean_ctor_get_uint8(x_10, 3);
x_27 = lean_ctor_get_uint8(x_10, 4);
x_28 = lean_ctor_get_uint8(x_10, 6);
x_29 = lean_ctor_get_uint8(x_10, 7);
x_30 = lean_ctor_get_uint8(x_10, 8);
x_31 = lean_ctor_get_uint8(x_10, 9);
x_32 = lean_ctor_get_uint8(x_10, 10);
x_33 = lean_ctor_get_uint8(x_10, 11);
x_34 = lean_ctor_get_uint8(x_10, 12);
x_35 = lean_ctor_get_uint8(x_10, 13);
lean_dec(x_10);
x_36 = 2;
x_37 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_37, 0, x_23);
lean_ctor_set_uint8(x_37, 1, x_24);
lean_ctor_set_uint8(x_37, 2, x_25);
lean_ctor_set_uint8(x_37, 3, x_26);
lean_ctor_set_uint8(x_37, 4, x_27);
lean_ctor_set_uint8(x_37, 5, x_36);
lean_ctor_set_uint8(x_37, 6, x_28);
lean_ctor_set_uint8(x_37, 7, x_29);
lean_ctor_set_uint8(x_37, 8, x_30);
lean_ctor_set_uint8(x_37, 9, x_31);
lean_ctor_set_uint8(x_37, 10, x_32);
lean_ctor_set_uint8(x_37, 11, x_33);
lean_ctor_set_uint8(x_37, 12, x_34);
lean_ctor_set_uint8(x_37, 13, x_35);
lean_ctor_set(x_2, 0, x_37);
x_38 = 1;
x_39 = l_Lean_Meta_DiscrTree_mkPathAux(x_38, x_8, x_7, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_ctor_get(x_2, 1);
x_50 = lean_ctor_get(x_2, 2);
x_51 = lean_ctor_get(x_2, 3);
x_52 = lean_ctor_get(x_2, 4);
x_53 = lean_ctor_get(x_2, 5);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_2);
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
x_66 = lean_ctor_get_uint8(x_48, 13);
if (lean_is_exclusive(x_48)) {
 x_67 = x_48;
} else {
 lean_dec_ref(x_48);
 x_67 = lean_box(0);
}
x_68 = 2;
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 0, 14);
} else {
 x_69 = x_67;
}
lean_ctor_set_uint8(x_69, 0, x_54);
lean_ctor_set_uint8(x_69, 1, x_55);
lean_ctor_set_uint8(x_69, 2, x_56);
lean_ctor_set_uint8(x_69, 3, x_57);
lean_ctor_set_uint8(x_69, 4, x_58);
lean_ctor_set_uint8(x_69, 5, x_68);
lean_ctor_set_uint8(x_69, 6, x_59);
lean_ctor_set_uint8(x_69, 7, x_60);
lean_ctor_set_uint8(x_69, 8, x_61);
lean_ctor_set_uint8(x_69, 9, x_62);
lean_ctor_set_uint8(x_69, 10, x_63);
lean_ctor_set_uint8(x_69, 11, x_64);
lean_ctor_set_uint8(x_69, 12, x_65);
lean_ctor_set_uint8(x_69, 13, x_66);
x_70 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_49);
lean_ctor_set(x_70, 2, x_50);
lean_ctor_set(x_70, 3, x_51);
lean_ctor_set(x_70, 4, x_52);
lean_ctor_set(x_70, 5, x_53);
x_71 = 1;
x_72 = l_Lean_Meta_DiscrTree_mkPathAux(x_71, x_8, x_7, x_70, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1;
x_7 = lean_array_push(x_6, x_2);
x_8 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_array_fget(x_1, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1;
x_16 = lean_array_push(x_15, x_14);
x_17 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_nat_add(x_9, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
lean_inc(x_6);
x_14 = lean_array_get(x_6, x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_8, 0);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_10);
x_18 = l_Lean_Meta_DiscrTree_Key_lt(x_16, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_6);
x_19 = lean_array_get_size(x_7);
x_20 = lean_nat_dec_lt(x_13, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
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
x_28 = lean_nat_add(x_4, x_27);
x_29 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_28, x_25);
lean_dec(x_28);
lean_ctor_set(x_21, 1, x_29);
lean_ctor_set(x_21, 0, x_5);
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
x_33 = lean_nat_add(x_4, x_32);
x_34 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_33, x_31);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
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
lean_dec(x_6);
lean_dec(x_1);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_4, x_40);
x_42 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_nat_add(x_9, x_40);
lean_dec(x_9);
x_45 = l_Array_insertAt___rarg(x_7, x_44, x_43);
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Array_isEmpty___rarg(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_11 = lean_array_get(x_6, x_7, x_10);
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_6);
x_16 = lean_array_get_size(x_7);
x_17 = lean_nat_dec_lt(x_10, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
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
x_25 = lean_nat_add(x_4, x_24);
x_26 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_25, x_22);
lean_dec(x_25);
lean_ctor_set(x_18, 1, x_26);
lean_ctor_set(x_18, 0, x_5);
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
x_30 = lean_nat_add(x_4, x_29);
x_31 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_30, x_28);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_fset(x_20, x_10, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_inc(x_6);
x_34 = l_Array_back___rarg(x_6, x_7);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Meta_DiscrTree_Key_lt(x_35, x_12);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_35);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_6);
x_38 = lean_array_get_size(x_7);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_38, x_39);
x_41 = lean_nat_dec_lt(x_40, x_38);
lean_dec(x_38);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
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
x_48 = lean_nat_add(x_4, x_39);
x_49 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_48, x_46);
lean_dec(x_48);
lean_ctor_set(x_42, 1, x_49);
lean_ctor_set(x_42, 0, x_5);
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
x_52 = lean_nat_add(x_4, x_39);
x_53 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_52, x_51);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_5);
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
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_4, x_60);
x_62 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_61);
lean_dec(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_5);
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
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_4, x_65);
x_67 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_5);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Array_insertAt___rarg(x_7, x_10, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_6);
lean_dec(x_1);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_4, x_70);
x_72 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
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
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg(x_1, x_7, x_3);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_fget(x_2, x_4);
x_13 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2;
x_16 = l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(x_1, x_2, x_3, x_4, x_12, x_15, x_8, x_14);
lean_dec(x_14);
lean_ctor_set(x_5, 1, x_16);
return x_5;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_array_get_size(x_2);
x_20 = lean_nat_dec_lt(x_4, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg(x_1, x_17, x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_array_fget(x_2, x_4);
x_24 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2;
x_27 = l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(x_1, x_2, x_3, x_4, x_23, x_26, x_18, x_25);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Meta_DiscrTree_Key_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Meta_DiscrTree_Key_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.DiscrTree");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.DiscrTree.insertCore");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid key sequence");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1;
x_2 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2;
x_3 = lean_unsigned_to_nat(353u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_3, x_7);
lean_inc(x_8);
lean_inc(x_2);
x_9 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_3, x_4, x_10);
lean_dec(x_3);
x_12 = l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg(x_2, x_8, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_3, x_4, x_14, x_13);
lean_dec(x_3);
x_16 = l_Std_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg(x_2, x_8, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4;
x_18 = l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_insertCore___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_DiscrTree_mkPath(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Meta_DiscrTree_insertCore___rarg(x_1, x_2, x_12, x_4);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l_Lean_Meta_DiscrTree_insertCore___rarg(x_1, x_2, x_14, x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_insert___rarg), 9, 0);
return x_2;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Expr_getAppNumArgsAux(x_1, x_9);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_empty_array_with_capacity(x_10);
lean_dec(x_10);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(4);
x_2 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_DiscrTree_whnfDT(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Expr_getAppFn(x_11);
switch (lean_obj_tag(x_13)) {
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_getAppNumArgsAux(x_11, x_15);
lean_inc(x_16);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_empty_array_with_capacity(x_16);
lean_dec(x_16);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_11, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
case 2:
{
lean_dec(x_11);
if (x_2 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_21, 4);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_9);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(x_23, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
lean_ctor_set(x_24, 0, x_35);
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec(x_24);
x_37 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
lean_ctor_set(x_9, 0, x_43);
return x_9;
}
}
else
{
lean_object* x_44; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
lean_ctor_set(x_9, 0, x_44);
return x_9;
}
}
case 4:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_9);
x_45 = lean_ctor_get(x_13, 0);
lean_inc(x_45);
lean_dec(x_13);
x_46 = l_Lean_Meta_getConfig(x_4, x_5, x_6, x_7, x_12);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_47, 4);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_box(0);
x_51 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_11, x_45, x_50, x_4, x_5, x_6, x_7, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = l_Lean_Expr_hasExprMVar(x_11);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_box(0);
x_55 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_11, x_45, x_54, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc(x_45);
x_56 = l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(x_45, x_4, x_5, x_6, x_7, x_52);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_st_ref_get(x_7, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Meta_isMatcherAppCore_x3f(x_63, x_11);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_inc(x_45);
x_65 = l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(x_45, x_4, x_5, x_6, x_7, x_62);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_box(0);
x_70 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_11, x_45, x_69, x_4, x_5, x_6, x_7, x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_45);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_71);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
return x_72;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; lean_object* x_91; size_t x_92; lean_object* x_93; lean_object* x_94; 
x_77 = lean_ctor_get(x_64, 0);
lean_inc(x_77);
lean_dec(x_64);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Expr_getAppNumArgsAux(x_11, x_78);
x_80 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3;
lean_inc(x_79);
x_81 = lean_mk_array(x_79, x_80);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_sub(x_79, x_82);
lean_dec(x_79);
lean_inc(x_11);
x_84 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_11, x_81, x_83);
x_85 = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(x_77);
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
lean_dec(x_77);
x_87 = lean_nat_add(x_85, x_86);
lean_dec(x_86);
x_88 = l_Array_toSubarray___rarg(x_84, x_85, x_87);
x_89 = lean_ctor_get(x_88, 2);
lean_inc(x_89);
x_90 = lean_usize_of_nat(x_89);
lean_dec(x_89);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
x_92 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_93 = lean_box(0);
x_94 = l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2(x_88, x_90, x_92, x_93, x_4, x_5, x_6, x_7, x_62);
lean_dec(x_88);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_11, x_45, x_93, x_4, x_5, x_6, x_7, x_95);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_96;
}
else
{
uint8_t x_97; 
lean_dec(x_45);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_97 = !lean_is_exclusive(x_94);
if (x_97 == 0)
{
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_94, 0);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_94);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_45);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_101 = lean_ctor_get(x_56, 1);
lean_inc(x_101);
lean_dec(x_56);
x_102 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_101);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
}
case 7:
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_107 = lean_ctor_get(x_13, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_13, 2);
lean_inc(x_108);
lean_dec(x_13);
x_109 = l_Lean_Expr_hasLooseBVars(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__4;
x_111 = lean_array_push(x_110, x_107);
x_112 = lean_array_push(x_111, x_108);
x_113 = lean_box(5);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_9, 0, x_114);
return x_9;
}
else
{
lean_object* x_115; 
lean_dec(x_108);
lean_dec(x_107);
x_115 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
lean_ctor_set(x_9, 0, x_115);
return x_9;
}
}
case 9:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = lean_ctor_get(x_13, 0);
lean_inc(x_116);
lean_dec(x_13);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_9, 0, x_119);
return x_9;
}
case 11:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_120 = lean_ctor_get(x_13, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_13, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_13, 2);
lean_inc(x_122);
lean_dec(x_13);
x_123 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
x_124 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1;
x_125 = lean_array_push(x_124, x_122);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_9, 0, x_126);
return x_9;
}
default: 
{
lean_object* x_127; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_127 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
lean_ctor_set(x_9, 0, x_127);
return x_9;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_9, 0);
x_129 = lean_ctor_get(x_9, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_9);
x_130 = l_Lean_Expr_getAppFn(x_128);
switch (lean_obj_tag(x_130)) {
case 1:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_unsigned_to_nat(0u);
x_133 = l_Lean_Expr_getAppNumArgsAux(x_128, x_132);
lean_inc(x_133);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_mk_empty_array_with_capacity(x_133);
lean_dec(x_133);
x_136 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_128, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_129);
return x_138;
}
case 2:
{
lean_dec(x_128);
if (x_2 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_4, 0);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_139, 4);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_130, 0);
lean_inc(x_141);
lean_dec(x_130);
x_142 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(x_141, x_4, x_5, x_6, x_7, x_129);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_146 = x_142;
} else {
 lean_dec_ref(x_142);
 x_146 = lean_box(0);
}
x_147 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_142, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_150 = x_142;
} else {
 lean_dec_ref(x_142);
 x_150 = lean_box(0);
}
x_151 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_142, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_142, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_155 = x_142;
} else {
 lean_dec_ref(x_142);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_130);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_157 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_129);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_130);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_159 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_129);
return x_160;
}
}
case 4:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_161 = lean_ctor_get(x_130, 0);
lean_inc(x_161);
lean_dec(x_130);
x_162 = l_Lean_Meta_getConfig(x_4, x_5, x_6, x_7, x_129);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get_uint8(x_163, 4);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_box(0);
x_167 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_128, x_161, x_166, x_4, x_5, x_6, x_7, x_165);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_167;
}
else
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_162, 1);
lean_inc(x_168);
lean_dec(x_162);
x_169 = l_Lean_Expr_hasExprMVar(x_128);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_box(0);
x_171 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_128, x_161, x_170, x_4, x_5, x_6, x_7, x_168);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_inc(x_161);
x_172 = l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(x_161, x_4, x_5, x_6, x_7, x_168);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = lean_st_ref_get(x_7, x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_Lean_Meta_isMatcherAppCore_x3f(x_179, x_128);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
lean_inc(x_161);
x_181 = l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(x_161, x_4, x_5, x_6, x_7, x_178);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_unbox(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec(x_181);
x_185 = lean_box(0);
x_186 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_128, x_161, x_185, x_4, x_5, x_6, x_7, x_184);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_161);
lean_dec(x_128);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_187 = lean_ctor_get(x_181, 1);
lean_inc(x_187);
lean_dec(x_181);
x_188 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
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
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; size_t x_206; lean_object* x_207; size_t x_208; lean_object* x_209; lean_object* x_210; 
x_193 = lean_ctor_get(x_180, 0);
lean_inc(x_193);
lean_dec(x_180);
x_194 = lean_unsigned_to_nat(0u);
x_195 = l_Lean_Expr_getAppNumArgsAux(x_128, x_194);
x_196 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3;
lean_inc(x_195);
x_197 = lean_mk_array(x_195, x_196);
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_nat_sub(x_195, x_198);
lean_dec(x_195);
lean_inc(x_128);
x_200 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_128, x_197, x_199);
x_201 = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(x_193);
x_202 = lean_ctor_get(x_193, 1);
lean_inc(x_202);
lean_dec(x_193);
x_203 = lean_nat_add(x_201, x_202);
lean_dec(x_202);
x_204 = l_Array_toSubarray___rarg(x_200, x_201, x_203);
x_205 = lean_ctor_get(x_204, 2);
lean_inc(x_205);
x_206 = lean_usize_of_nat(x_205);
lean_dec(x_205);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
x_208 = lean_usize_of_nat(x_207);
lean_dec(x_207);
x_209 = lean_box(0);
x_210 = l_Subarray_forInUnsafe_loop___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__2(x_204, x_206, x_208, x_209, x_4, x_5, x_6, x_7, x_178);
lean_dec(x_204);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_128, x_161, x_209, x_4, x_5, x_6, x_7, x_211);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_161);
lean_dec(x_128);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_213 = lean_ctor_get(x_210, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_215 = x_210;
} else {
 lean_dec_ref(x_210);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_161);
lean_dec(x_128);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_217 = lean_ctor_get(x_172, 1);
lean_inc(x_217);
lean_dec(x_172);
x_218 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_217);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
}
}
case 7:
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
lean_dec(x_128);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_223 = lean_ctor_get(x_130, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_130, 2);
lean_inc(x_224);
lean_dec(x_130);
x_225 = l_Lean_Expr_hasLooseBVars(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__4;
x_227 = lean_array_push(x_226, x_223);
x_228 = lean_array_push(x_227, x_224);
x_229 = lean_box(5);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_129);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_224);
lean_dec(x_223);
x_232 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_129);
return x_233;
}
}
case 9:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_128);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_234 = lean_ctor_get(x_130, 0);
lean_inc(x_234);
lean_dec(x_130);
x_235 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_236 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_129);
return x_238;
}
case 11:
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_128);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_239 = lean_ctor_get(x_130, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_130, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_130, 2);
lean_inc(x_241);
lean_dec(x_130);
x_242 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
x_243 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1;
x_244 = lean_array_push(x_243, x_241);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_129);
return x_246;
}
default: 
{
lean_object* x_247; lean_object* x_248; 
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_247 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_129);
return x_248;
}
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_249 = !lean_is_exclusive(x_9);
if (x_249 == 0)
{
return x_9;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_9, 0);
x_251 = lean_ctor_get(x_9, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_9);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(3);
x_3 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__1___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_mkPath___closed__1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_DiscrTree_mkPath___closed__1;
x_8 = l_Array_append___rarg(x_7, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___spec__2___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_5);
lean_dec(x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2;
x_13 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg(x_12, x_11, x_1, x_4, x_8, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(4);
x_2 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Array_isEmpty___rarg(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_9);
x_12 = l_Array_isEmpty___rarg(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_13 = l_Lean_instInhabitedExpr;
x_14 = l_Array_back___rarg(x_13, x_1);
x_15 = lean_array_pop(x_1);
x_16 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get(x_16, x_10, x_17);
x_19 = 1;
x_20 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_14, x_19, x_20, x_4, x_5, x_6, x_7, x_8);
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
x_30 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
x_31 = x_20;
goto block_152;
}
else
{
x_31 = x_19;
goto block_152;
}
block_152:
{
lean_object* x_32; lean_object* x_33; 
if (x_31 == 0)
{
lean_dec(x_18);
x_32 = x_3;
x_33 = x_23;
goto block_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_18, 1);
lean_inc(x_144);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_145 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(x_15, x_144, x_3, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_32 = x_146;
x_33 = x_147;
goto block_143;
}
else
{
uint8_t x_148; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_148 = !lean_is_exclusive(x_145);
if (x_148 == 0)
{
return x_145;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_145, 0);
x_150 = lean_ctor_get(x_145, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_145);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
block_143:
{
lean_object* x_34; 
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_24);
x_63 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_27)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_27;
}
lean_ctor_set(x_64, 0, x_25);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_array_get_size(x_10);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_sub(x_65, x_66);
x_68 = lean_nat_dec_lt(x_17, x_65);
lean_dec(x_65);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_32);
lean_ctor_set(x_69, 1, x_33);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
x_71 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg(x_16, x_70, x_10, x_64, x_17, x_67);
lean_dec(x_64);
lean_dec(x_10);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_32);
lean_ctor_set(x_72, 1, x_33);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Array_append___rarg(x_15, x_26);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_1 = x_74;
x_2 = x_75;
x_3 = x_32;
x_8 = x_33;
goto _start;
}
}
}
case 1:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_24);
x_77 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_27)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_27;
}
lean_ctor_set(x_78, 0, x_25);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_array_get_size(x_10);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_sub(x_79, x_80);
x_82 = lean_nat_dec_lt(x_17, x_79);
lean_dec(x_79);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_32);
lean_ctor_set(x_83, 1, x_33);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_box(0);
x_85 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg(x_16, x_84, x_10, x_78, x_17, x_81);
lean_dec(x_78);
lean_dec(x_10);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_32);
lean_ctor_set(x_86, 1, x_33);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Array_append___rarg(x_15, x_26);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_1 = x_88;
x_2 = x_89;
x_3 = x_32;
x_8 = x_33;
goto _start;
}
}
}
case 2:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec(x_24);
x_91 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_27)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_27;
}
lean_ctor_set(x_92, 0, x_25);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_array_get_size(x_10);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_sub(x_93, x_94);
x_96 = lean_nat_dec_lt(x_17, x_93);
lean_dec(x_93);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_32);
lean_ctor_set(x_97, 1, x_33);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_box(0);
x_99 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg(x_16, x_98, x_10, x_92, x_17, x_95);
lean_dec(x_92);
lean_dec(x_10);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_32);
lean_ctor_set(x_100, 1, x_33);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Array_append___rarg(x_15, x_26);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_1 = x_102;
x_2 = x_103;
x_3 = x_32;
x_8 = x_33;
goto _start;
}
}
}
case 3:
{
lean_object* x_105; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_32);
lean_ctor_set(x_105, 1, x_33);
return x_105;
}
case 4:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_24);
x_106 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_27)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_27;
}
lean_ctor_set(x_107, 0, x_25);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_array_get_size(x_10);
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_nat_sub(x_108, x_109);
x_111 = lean_nat_dec_lt(x_17, x_108);
lean_dec(x_108);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_32);
lean_ctor_set(x_112, 1, x_33);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_box(0);
x_114 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg(x_16, x_113, x_10, x_107, x_17, x_110);
lean_dec(x_107);
lean_dec(x_10);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_32);
lean_ctor_set(x_115, 1, x_33);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Array_append___rarg(x_15, x_26);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_1 = x_117;
x_2 = x_118;
x_3 = x_32;
x_8 = x_33;
goto _start;
}
}
}
case 5:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_120 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_27)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_27;
}
lean_ctor_set(x_121, 0, x_25);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_array_get_size(x_10);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_sub(x_122, x_123);
x_125 = lean_nat_dec_lt(x_17, x_122);
lean_dec(x_122);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec(x_124);
lean_dec(x_121);
x_126 = lean_box(0);
x_34 = x_126;
goto block_62;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_box(0);
x_128 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg(x_16, x_127, x_10, x_121, x_17, x_124);
lean_dec(x_121);
x_34 = x_128;
goto block_62;
}
}
default: 
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec(x_24);
x_129 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_27)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_27;
}
lean_ctor_set(x_130, 0, x_25);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_array_get_size(x_10);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_nat_sub(x_131, x_132);
x_134 = lean_nat_dec_lt(x_17, x_131);
lean_dec(x_131);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_32);
lean_ctor_set(x_135, 1, x_33);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_box(0);
x_137 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg(x_16, x_136, x_10, x_130, x_17, x_133);
lean_dec(x_130);
lean_dec(x_10);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_32);
lean_ctor_set(x_138, 1, x_33);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Array_append___rarg(x_15, x_26);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_1 = x_140;
x_2 = x_141;
x_3 = x_32;
x_8 = x_33;
goto _start;
}
}
}
}
block_62:
{
lean_object* x_35; lean_object* x_36; 
if (lean_obj_tag(x_34) == 0)
{
lean_dec(x_26);
x_35 = x_32;
x_36 = x_33;
goto block_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_34, 0);
lean_inc(x_52);
lean_dec(x_34);
lean_inc(x_15);
x_53 = l_Array_append___rarg(x_15, x_26);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_55 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(x_53, x_54, x_32, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_35 = x_56;
x_36 = x_57;
goto block_51;
}
else
{
uint8_t x_58; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_55);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
block_51:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_array_get_size(x_10);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_37, x_38);
x_40 = lean_nat_dec_lt(x_17, x_37);
lean_dec(x_37);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_39);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_24)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_24;
}
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_box(0);
x_43 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg___closed__1;
x_44 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg(x_16, x_42, x_10, x_43, x_17, x_39);
lean_dec(x_10);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_24)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_24;
}
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_24);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_48 = l_Array_append___rarg(x_15, x_47);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_1 = x_48;
x_2 = x_49;
x_3 = x_35;
x_8 = x_36;
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
uint8_t x_153; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_153 = !lean_is_exclusive(x_21);
if (x_153 == 0)
{
return x_21;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_21, 0);
x_155 = lean_ctor_get(x_21, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_21);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
lean_object* x_157; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_3);
lean_ctor_set(x_157, 1, x_8);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_158 = l_Array_append___rarg(x_3, x_9);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_8);
return x_159;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___spec__7___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__1___rarg(x_1, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg(x_3, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___spec__2___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = 2;
lean_ctor_set_uint8(x_10, 5, x_12);
x_13 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_13, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 3)
{
uint8_t x_17; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_8);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_16, x_22, x_8, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_36 = lean_ctor_get_uint8(x_10, 0);
x_37 = lean_ctor_get_uint8(x_10, 1);
x_38 = lean_ctor_get_uint8(x_10, 2);
x_39 = lean_ctor_get_uint8(x_10, 3);
x_40 = lean_ctor_get_uint8(x_10, 4);
x_41 = lean_ctor_get_uint8(x_10, 6);
x_42 = lean_ctor_get_uint8(x_10, 7);
x_43 = lean_ctor_get_uint8(x_10, 8);
x_44 = lean_ctor_get_uint8(x_10, 9);
x_45 = lean_ctor_get_uint8(x_10, 10);
x_46 = lean_ctor_get_uint8(x_10, 11);
x_47 = lean_ctor_get_uint8(x_10, 12);
x_48 = lean_ctor_get_uint8(x_10, 13);
lean_dec(x_10);
x_49 = 2;
x_50 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_50, 0, x_36);
lean_ctor_set_uint8(x_50, 1, x_37);
lean_ctor_set_uint8(x_50, 2, x_38);
lean_ctor_set_uint8(x_50, 3, x_39);
lean_ctor_set_uint8(x_50, 4, x_40);
lean_ctor_set_uint8(x_50, 5, x_49);
lean_ctor_set_uint8(x_50, 6, x_41);
lean_ctor_set_uint8(x_50, 7, x_42);
lean_ctor_set_uint8(x_50, 8, x_43);
lean_ctor_set_uint8(x_50, 9, x_44);
lean_ctor_set_uint8(x_50, 10, x_45);
lean_ctor_set_uint8(x_50, 11, x_46);
lean_ctor_set_uint8(x_50, 12, x_47);
lean_ctor_set_uint8(x_50, 13, x_48);
lean_ctor_set(x_3, 0, x_50);
x_51 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_52 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_51, x_51, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 3)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_8);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_dec(x_53);
x_60 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_54, x_59, x_8, x_3, x_4, x_5, x_6, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = lean_ctor_get(x_52, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_52, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_71 = x_52;
} else {
 lean_dec_ref(x_52);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_73 = lean_ctor_get(x_3, 0);
x_74 = lean_ctor_get(x_3, 1);
x_75 = lean_ctor_get(x_3, 2);
x_76 = lean_ctor_get(x_3, 3);
x_77 = lean_ctor_get(x_3, 4);
x_78 = lean_ctor_get(x_3, 5);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_3);
x_79 = lean_ctor_get_uint8(x_73, 0);
x_80 = lean_ctor_get_uint8(x_73, 1);
x_81 = lean_ctor_get_uint8(x_73, 2);
x_82 = lean_ctor_get_uint8(x_73, 3);
x_83 = lean_ctor_get_uint8(x_73, 4);
x_84 = lean_ctor_get_uint8(x_73, 6);
x_85 = lean_ctor_get_uint8(x_73, 7);
x_86 = lean_ctor_get_uint8(x_73, 8);
x_87 = lean_ctor_get_uint8(x_73, 9);
x_88 = lean_ctor_get_uint8(x_73, 10);
x_89 = lean_ctor_get_uint8(x_73, 11);
x_90 = lean_ctor_get_uint8(x_73, 12);
x_91 = lean_ctor_get_uint8(x_73, 13);
if (lean_is_exclusive(x_73)) {
 x_92 = x_73;
} else {
 lean_dec_ref(x_73);
 x_92 = lean_box(0);
}
x_93 = 2;
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 0, 14);
} else {
 x_94 = x_92;
}
lean_ctor_set_uint8(x_94, 0, x_79);
lean_ctor_set_uint8(x_94, 1, x_80);
lean_ctor_set_uint8(x_94, 2, x_81);
lean_ctor_set_uint8(x_94, 3, x_82);
lean_ctor_set_uint8(x_94, 4, x_83);
lean_ctor_set_uint8(x_94, 5, x_93);
lean_ctor_set_uint8(x_94, 6, x_84);
lean_ctor_set_uint8(x_94, 7, x_85);
lean_ctor_set_uint8(x_94, 8, x_86);
lean_ctor_set_uint8(x_94, 9, x_87);
lean_ctor_set_uint8(x_94, 10, x_88);
lean_ctor_set_uint8(x_94, 11, x_89);
lean_ctor_set_uint8(x_94, 12, x_90);
lean_ctor_set_uint8(x_94, 13, x_91);
x_95 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_74);
lean_ctor_set(x_95, 2, x_75);
lean_ctor_set(x_95, 3, x_76);
lean_ctor_set(x_95, 4, x_77);
lean_ctor_set(x_95, 5, x_78);
x_96 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_95);
x_97 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_96, x_96, x_95, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 3)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_8);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_97, 1);
lean_inc(x_103);
lean_dec(x_97);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_dec(x_98);
x_105 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_99, x_104, x_8, x_95, x_4, x_5, x_6, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_112 = x_105;
} else {
 lean_dec_ref(x_105);
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
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_95);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_114 = lean_ctor_get(x_97, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_97, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_116 = x_97;
} else {
 lean_dec_ref(x_97);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatch___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__2___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__3___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__2___rarg(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__4___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_process___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_3);
x_11 = l_Array_ofSubarray___rarg(x_3);
x_12 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchRoot___rarg(x_1, x_2, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__1___rarg(x_1, x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_15);
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_13);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_20, x_23);
lean_dec(x_20);
lean_ctor_set(x_2, 1, x_24);
x_25 = l_Subarray_popFront___rarg(x_3);
x_26 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_3 = x_25;
x_4 = x_26;
x_10 = x_16;
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_13);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_29, x_32);
lean_dec(x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Subarray_popFront___rarg(x_3);
x_36 = lean_nat_add(x_4, x_32);
lean_dec(x_4);
x_2 = x_34;
x_3 = x_35;
x_4 = x_36;
x_10 = x_16;
goto _start;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_13);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_40, x_43);
lean_dec(x_40);
lean_ctor_set(x_2, 1, x_44);
x_45 = l_Subarray_popFront___rarg(x_3);
x_46 = lean_nat_add(x_4, x_43);
lean_dec(x_4);
x_3 = x_45;
x_4 = x_46;
x_10 = x_16;
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_2);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_13);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_49, x_52);
lean_dec(x_49);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Subarray_popFront___rarg(x_3);
x_56 = lean_nat_add(x_4, x_52);
lean_dec(x_4);
x_2 = x_54;
x_3 = x_55;
x_4 = x_56;
x_10 = x_16;
goto _start;
}
else
{
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
}
default: 
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
}
else
{
lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_17);
x_58 = lean_array_get_size(x_15);
x_59 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_60 = 0;
lean_inc(x_4);
x_61 = l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__4___rarg(x_4, x_59, x_60, x_15);
x_62 = l_Array_append___rarg(x_5, x_61);
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_2);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_2, 0);
x_65 = lean_ctor_get(x_2, 1);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_13);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_sub(x_65, x_68);
lean_dec(x_65);
lean_ctor_set(x_2, 1, x_69);
x_70 = l_Subarray_popFront___rarg(x_3);
x_71 = lean_nat_add(x_4, x_68);
lean_dec(x_4);
x_3 = x_70;
x_4 = x_71;
x_5 = x_62;
x_10 = x_16;
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_62);
return x_13;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_2);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_eq(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_13);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_sub(x_74, x_77);
lean_dec(x_74);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Subarray_popFront___rarg(x_3);
x_81 = lean_nat_add(x_4, x_77);
lean_dec(x_4);
x_2 = x_79;
x_3 = x_80;
x_4 = x_81;
x_5 = x_62;
x_10 = x_16;
goto _start;
}
else
{
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_62);
return x_13;
}
}
}
case 1:
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_2);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_2, 0);
x_85 = lean_ctor_get(x_2, 1);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_nat_dec_eq(x_85, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_13);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_sub(x_85, x_88);
lean_dec(x_85);
lean_ctor_set(x_2, 1, x_89);
x_90 = l_Subarray_popFront___rarg(x_3);
x_91 = lean_nat_add(x_4, x_88);
lean_dec(x_4);
x_3 = x_90;
x_4 = x_91;
x_5 = x_62;
x_10 = x_16;
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_62);
return x_13;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_2, 0);
x_94 = lean_ctor_get(x_2, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_2);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_nat_dec_eq(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_free_object(x_13);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_sub(x_94, x_97);
lean_dec(x_94);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Subarray_popFront___rarg(x_3);
x_101 = lean_nat_add(x_4, x_97);
lean_dec(x_4);
x_2 = x_99;
x_3 = x_100;
x_4 = x_101;
x_5 = x_62;
x_10 = x_16;
goto _start;
}
else
{
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_62);
return x_13;
}
}
}
default: 
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_62);
return x_13;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_13, 0);
x_104 = lean_ctor_get(x_13, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_105 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__1___rarg(x_1, x_2);
if (lean_obj_tag(x_105) == 0)
{
lean_dec(x_103);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_2, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_2, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_108 = x_2;
} else {
 lean_dec_ref(x_2);
 x_108 = lean_box(0);
}
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_dec_eq(x_107, x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_sub(x_107, x_111);
lean_dec(x_107);
if (lean_is_scalar(x_108)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_108;
}
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Subarray_popFront___rarg(x_3);
x_115 = lean_nat_add(x_4, x_111);
lean_dec(x_4);
x_2 = x_113;
x_3 = x_114;
x_4 = x_115;
x_10 = x_104;
goto _start;
}
else
{
lean_object* x_117; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_5);
lean_ctor_set(x_117, 1, x_104);
return x_117;
}
}
case 1:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_118 = lean_ctor_get(x_2, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_2, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_120 = x_2;
} else {
 lean_dec_ref(x_2);
 x_120 = lean_box(0);
}
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_nat_dec_eq(x_119, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_sub(x_119, x_123);
lean_dec(x_119);
if (lean_is_scalar(x_120)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_120;
}
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Subarray_popFront___rarg(x_3);
x_127 = lean_nat_add(x_4, x_123);
lean_dec(x_4);
x_2 = x_125;
x_3 = x_126;
x_4 = x_127;
x_10 = x_104;
goto _start;
}
else
{
lean_object* x_129; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_5);
lean_ctor_set(x_129, 1, x_104);
return x_129;
}
}
default: 
{
lean_object* x_130; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_5);
lean_ctor_set(x_130, 1, x_104);
return x_130;
}
}
}
else
{
lean_object* x_131; size_t x_132; size_t x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_105);
x_131 = lean_array_get_size(x_103);
x_132 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_133 = 0;
lean_inc(x_4);
x_134 = l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__4___rarg(x_4, x_132, x_133, x_103);
x_135 = l_Array_append___rarg(x_5, x_134);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_2, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_2, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_138 = x_2;
} else {
 lean_dec_ref(x_2);
 x_138 = lean_box(0);
}
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_nat_dec_eq(x_137, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_sub(x_137, x_141);
lean_dec(x_137);
if (lean_is_scalar(x_138)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_138;
}
lean_ctor_set(x_143, 0, x_136);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Subarray_popFront___rarg(x_3);
x_145 = lean_nat_add(x_4, x_141);
lean_dec(x_4);
x_2 = x_143;
x_3 = x_144;
x_4 = x_145;
x_5 = x_135;
x_10 = x_104;
goto _start;
}
else
{
lean_object* x_147; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_135);
lean_ctor_set(x_147, 1, x_104);
return x_147;
}
}
case 1:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_2, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_2, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_150 = x_2;
} else {
 lean_dec_ref(x_2);
 x_150 = lean_box(0);
}
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_nat_dec_eq(x_149, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_nat_sub(x_149, x_153);
lean_dec(x_149);
if (lean_is_scalar(x_150)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_150;
}
lean_ctor_set(x_155, 0, x_148);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Subarray_popFront___rarg(x_3);
x_157 = lean_nat_add(x_4, x_153);
lean_dec(x_4);
x_2 = x_155;
x_3 = x_156;
x_4 = x_157;
x_5 = x_135;
x_10 = x_104;
goto _start;
}
else
{
lean_object* x_159; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_135);
lean_ctor_set(x_159, 1, x_104);
return x_159;
}
}
default: 
{
lean_object* x_160; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_135);
lean_ctor_set(x_160, 1, x_104);
return x_160;
}
}
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_13);
if (x_161 == 0)
{
return x_13;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_13, 0);
x_163 = lean_ctor_get(x_13, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_13);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra_process(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatchWithExtra_process___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__2___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra_process___spec__4___rarg(x_1, x_5, x_6, x_4);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_Meta_DiscrTree_getMatchWithExtra___spec__1___rarg(x_10, x_11, x_8);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = 2;
lean_ctor_set_uint8(x_14, 5, x_16);
x_17 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_17, x_17, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 3)
{
uint8_t x_21; 
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_array_get_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Array_toSubarray___rarg(x_26, x_28, x_27);
x_30 = l_Lean_Meta_DiscrTree_getMatchWithExtra_process___rarg(x_1, x_20, x_29, x_28, x_12, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_43 = lean_ctor_get_uint8(x_14, 0);
x_44 = lean_ctor_get_uint8(x_14, 1);
x_45 = lean_ctor_get_uint8(x_14, 2);
x_46 = lean_ctor_get_uint8(x_14, 3);
x_47 = lean_ctor_get_uint8(x_14, 4);
x_48 = lean_ctor_get_uint8(x_14, 6);
x_49 = lean_ctor_get_uint8(x_14, 7);
x_50 = lean_ctor_get_uint8(x_14, 8);
x_51 = lean_ctor_get_uint8(x_14, 9);
x_52 = lean_ctor_get_uint8(x_14, 10);
x_53 = lean_ctor_get_uint8(x_14, 11);
x_54 = lean_ctor_get_uint8(x_14, 12);
x_55 = lean_ctor_get_uint8(x_14, 13);
lean_dec(x_14);
x_56 = 2;
x_57 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_57, 0, x_43);
lean_ctor_set_uint8(x_57, 1, x_44);
lean_ctor_set_uint8(x_57, 2, x_45);
lean_ctor_set_uint8(x_57, 3, x_46);
lean_ctor_set_uint8(x_57, 4, x_47);
lean_ctor_set_uint8(x_57, 5, x_56);
lean_ctor_set_uint8(x_57, 6, x_48);
lean_ctor_set_uint8(x_57, 7, x_49);
lean_ctor_set_uint8(x_57, 8, x_50);
lean_ctor_set_uint8(x_57, 9, x_51);
lean_ctor_set_uint8(x_57, 10, x_52);
lean_ctor_set_uint8(x_57, 11, x_53);
lean_ctor_set_uint8(x_57, 12, x_54);
lean_ctor_set_uint8(x_57, 13, x_55);
lean_ctor_set(x_3, 0, x_57);
x_58 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_59 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_58, x_58, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 3)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_12);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_dec(x_60);
x_67 = lean_array_get_size(x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Array_toSubarray___rarg(x_66, x_68, x_67);
x_70 = l_Lean_Meta_DiscrTree_getMatchWithExtra_process___rarg(x_1, x_61, x_69, x_68, x_12, x_3, x_4, x_5, x_6, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_79 = lean_ctor_get(x_59, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_59, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_81 = x_59;
} else {
 lean_dec_ref(x_59);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_83 = lean_ctor_get(x_3, 0);
x_84 = lean_ctor_get(x_3, 1);
x_85 = lean_ctor_get(x_3, 2);
x_86 = lean_ctor_get(x_3, 3);
x_87 = lean_ctor_get(x_3, 4);
x_88 = lean_ctor_get(x_3, 5);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_3);
x_89 = lean_ctor_get_uint8(x_83, 0);
x_90 = lean_ctor_get_uint8(x_83, 1);
x_91 = lean_ctor_get_uint8(x_83, 2);
x_92 = lean_ctor_get_uint8(x_83, 3);
x_93 = lean_ctor_get_uint8(x_83, 4);
x_94 = lean_ctor_get_uint8(x_83, 6);
x_95 = lean_ctor_get_uint8(x_83, 7);
x_96 = lean_ctor_get_uint8(x_83, 8);
x_97 = lean_ctor_get_uint8(x_83, 9);
x_98 = lean_ctor_get_uint8(x_83, 10);
x_99 = lean_ctor_get_uint8(x_83, 11);
x_100 = lean_ctor_get_uint8(x_83, 12);
x_101 = lean_ctor_get_uint8(x_83, 13);
if (lean_is_exclusive(x_83)) {
 x_102 = x_83;
} else {
 lean_dec_ref(x_83);
 x_102 = lean_box(0);
}
x_103 = 2;
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 0, 14);
} else {
 x_104 = x_102;
}
lean_ctor_set_uint8(x_104, 0, x_89);
lean_ctor_set_uint8(x_104, 1, x_90);
lean_ctor_set_uint8(x_104, 2, x_91);
lean_ctor_set_uint8(x_104, 3, x_92);
lean_ctor_set_uint8(x_104, 4, x_93);
lean_ctor_set_uint8(x_104, 5, x_103);
lean_ctor_set_uint8(x_104, 6, x_94);
lean_ctor_set_uint8(x_104, 7, x_95);
lean_ctor_set_uint8(x_104, 8, x_96);
lean_ctor_set_uint8(x_104, 9, x_97);
lean_ctor_set_uint8(x_104, 10, x_98);
lean_ctor_set_uint8(x_104, 11, x_99);
lean_ctor_set_uint8(x_104, 12, x_100);
lean_ctor_set_uint8(x_104, 13, x_101);
x_105 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_84);
lean_ctor_set(x_105, 2, x_85);
lean_ctor_set(x_105, 3, x_86);
lean_ctor_set(x_105, 4, x_87);
lean_ctor_set(x_105, 5, x_88);
x_106 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_105);
x_107 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_106, x_106, x_105, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 3)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_108);
lean_dec(x_105);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_111 = x_107;
} else {
 lean_dec_ref(x_107);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_12);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_dec(x_107);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_dec(x_108);
x_115 = lean_array_get_size(x_114);
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Array_toSubarray___rarg(x_114, x_116, x_115);
x_118 = l_Lean_Meta_DiscrTree_getMatchWithExtra_process___rarg(x_1, x_109, x_117, x_116, x_12, x_105, x_4, x_5, x_6, x_113);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_118, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_118, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_125 = x_118;
} else {
 lean_dec_ref(x_118);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_105);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_127 = lean_ctor_get(x_107, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_107, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_129 = x_107;
} else {
 lean_dec_ref(x_107);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg), 7, 0);
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_DiscrTree_Key_arity(x_13);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_15, x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_array_uget(x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_DiscrTree_Key_arity(x_14);
lean_dec(x_14);
x_17 = lean_nat_add(x_2, x_16);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_18 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_17, x_1, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_4 = x_22;
x_6 = x_19;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_11);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify_process___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Array_isEmpty___rarg(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_10, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_16, x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_23 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(x_2, x_13, x_14, x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_14);
lean_dec(x_13);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_dec(x_3);
x_27 = l_Array_isEmpty___rarg(x_2);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_25);
x_28 = l_Array_isEmpty___rarg(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = l_Lean_instInhabitedExpr;
x_30 = l_Array_back___rarg(x_29, x_2);
x_31 = lean_array_pop(x_2);
x_32 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_30, x_32, x_32, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_37 = x_33;
} else {
 lean_dec_ref(x_33);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_39 = x_34;
} else {
 lean_dec_ref(x_34);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2;
x_41 = lean_array_get(x_40, x_26, x_10);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_box(3);
x_44 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
x_45 = x_32;
goto block_71;
}
else
{
uint8_t x_72; 
x_72 = 1;
x_45 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_46; lean_object* x_47; 
if (x_45 == 0)
{
lean_dec(x_41);
x_46 = x_4;
x_47 = x_36;
goto block_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
lean_dec(x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_31);
x_64 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_31, x_63, x_4, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_46 = x_65;
x_47 = x_66;
goto block_62;
}
else
{
uint8_t x_67; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 0);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_64);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
block_62:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_39)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_39;
}
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_get_size(x_26);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_50, x_51);
x_53 = lean_nat_dec_lt(x_10, x_50);
lean_dec(x_50);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_38);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_37)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_37;
}
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_box(0);
x_56 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(x_40, x_55, x_26, x_49, x_10, x_52);
lean_dec(x_49);
lean_dec(x_26);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec(x_38);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_37)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_37;
}
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_47);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_37);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Array_append___rarg(x_31, x_38);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_1 = x_10;
x_2 = x_59;
x_3 = x_60;
x_4 = x_46;
x_9 = x_47;
goto _start;
}
}
}
}
}
case 1:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; 
x_73 = lean_ctor_get(x_33, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_74 = x_33;
} else {
 lean_dec_ref(x_33);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_76 = x_34;
} else {
 lean_dec_ref(x_34);
 x_76 = lean_box(0);
}
x_77 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2;
x_78 = lean_array_get(x_77, x_26, x_10);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_box(3);
x_81 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_79, x_80);
lean_dec(x_79);
if (x_81 == 0)
{
x_82 = x_32;
goto block_108;
}
else
{
uint8_t x_109; 
x_109 = 1;
x_82 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_83; lean_object* x_84; 
if (x_82 == 0)
{
lean_dec(x_78);
x_83 = x_4;
x_84 = x_73;
goto block_99;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_78, 1);
lean_inc(x_100);
lean_dec(x_78);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_31);
x_101 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_31, x_100, x_4, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_83 = x_102;
x_84 = x_103;
goto block_99;
}
else
{
uint8_t x_104; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_104 = !lean_is_exclusive(x_101);
if (x_104 == 0)
{
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
block_99:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_85 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_76)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_76;
}
lean_ctor_set(x_86, 0, x_35);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_array_get_size(x_26);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_sub(x_87, x_88);
x_90 = lean_nat_dec_lt(x_10, x_87);
lean_dec(x_87);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_75);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_74)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_74;
}
lean_ctor_set(x_91, 0, x_83);
lean_ctor_set(x_91, 1, x_84);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_box(0);
x_93 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_77, x_92, x_26, x_86, x_10, x_89);
lean_dec(x_86);
lean_dec(x_26);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
lean_dec(x_75);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_74)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_74;
}
lean_ctor_set(x_94, 0, x_83);
lean_ctor_set(x_94, 1, x_84);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_74);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Array_append___rarg(x_31, x_75);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_1 = x_10;
x_2 = x_96;
x_3 = x_97;
x_4 = x_83;
x_9 = x_84;
goto _start;
}
}
}
}
}
case 2:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; 
x_110 = lean_ctor_get(x_33, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_111 = x_33;
} else {
 lean_dec_ref(x_33);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_34, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_113 = x_34;
} else {
 lean_dec_ref(x_34);
 x_113 = lean_box(0);
}
x_114 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2;
x_115 = lean_array_get(x_114, x_26, x_10);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_box(3);
x_118 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_116, x_117);
lean_dec(x_116);
if (x_118 == 0)
{
x_119 = x_32;
goto block_145;
}
else
{
uint8_t x_146; 
x_146 = 1;
x_119 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_120; lean_object* x_121; 
if (x_119 == 0)
{
lean_dec(x_115);
x_120 = x_4;
x_121 = x_110;
goto block_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_115, 1);
lean_inc(x_137);
lean_dec(x_115);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_31);
x_138 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_31, x_137, x_4, x_5, x_6, x_7, x_8, x_110);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_120 = x_139;
x_121 = x_140;
goto block_136;
}
else
{
uint8_t x_141; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_141 = !lean_is_exclusive(x_138);
if (x_141 == 0)
{
return x_138;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_138, 0);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_138);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
block_136:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_113)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_113;
}
lean_ctor_set(x_123, 0, x_35);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_get_size(x_26);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_sub(x_124, x_125);
x_127 = lean_nat_dec_lt(x_10, x_124);
lean_dec(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_126);
lean_dec(x_123);
lean_dec(x_112);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_111)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_111;
}
lean_ctor_set(x_128, 0, x_120);
lean_ctor_set(x_128, 1, x_121);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_box(0);
x_130 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(x_114, x_129, x_26, x_123, x_10, x_126);
lean_dec(x_123);
lean_dec(x_26);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
lean_dec(x_112);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_111)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_111;
}
lean_ctor_set(x_131, 0, x_120);
lean_ctor_set(x_131, 1, x_121);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_111);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Array_append___rarg(x_31, x_112);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_1 = x_10;
x_2 = x_133;
x_3 = x_134;
x_4 = x_120;
x_9 = x_121;
goto _start;
}
}
}
}
}
case 3:
{
uint8_t x_147; 
lean_dec(x_34);
x_147 = !lean_is_exclusive(x_33);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = lean_ctor_get(x_33, 1);
x_149 = lean_ctor_get(x_33, 0);
lean_dec(x_149);
x_150 = lean_array_get_size(x_26);
x_151 = lean_nat_dec_lt(x_10, x_150);
if (x_151 == 0)
{
lean_dec(x_150);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_33, 0, x_4);
return x_33;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_150, x_150);
if (x_152 == 0)
{
lean_dec(x_150);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_33, 0, x_4);
return x_33;
}
else
{
size_t x_153; size_t x_154; lean_object* x_155; 
lean_free_object(x_33);
x_153 = 0;
x_154 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_155 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_31, x_26, x_153, x_154, x_4, x_5, x_6, x_7, x_8, x_148);
lean_dec(x_26);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = lean_ctor_get(x_33, 1);
lean_inc(x_156);
lean_dec(x_33);
x_157 = lean_array_get_size(x_26);
x_158 = lean_nat_dec_lt(x_10, x_157);
if (x_158 == 0)
{
lean_object* x_159; 
lean_dec(x_157);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_4);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
else
{
uint8_t x_160; 
x_160 = lean_nat_dec_le(x_157, x_157);
if (x_160 == 0)
{
lean_object* x_161; 
lean_dec(x_157);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_4);
lean_ctor_set(x_161, 1, x_156);
return x_161;
}
else
{
size_t x_162; size_t x_163; lean_object* x_164; 
x_162 = 0;
x_163 = lean_usize_of_nat(x_157);
lean_dec(x_157);
x_164 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_31, x_26, x_162, x_163, x_4, x_5, x_6, x_7, x_8, x_156);
lean_dec(x_26);
return x_164;
}
}
}
}
case 4:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_174; 
x_165 = lean_ctor_get(x_33, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_166 = x_33;
} else {
 lean_dec_ref(x_33);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_34, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_168 = x_34;
} else {
 lean_dec_ref(x_34);
 x_168 = lean_box(0);
}
x_169 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2;
x_170 = lean_array_get(x_169, x_26, x_10);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_box(3);
x_173 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_171, x_172);
lean_dec(x_171);
if (x_173 == 0)
{
x_174 = x_32;
goto block_200;
}
else
{
uint8_t x_201; 
x_201 = 1;
x_174 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_175; lean_object* x_176; 
if (x_174 == 0)
{
lean_dec(x_170);
x_175 = x_4;
x_176 = x_165;
goto block_191;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_170, 1);
lean_inc(x_192);
lean_dec(x_170);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_31);
x_193 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_31, x_192, x_4, x_5, x_6, x_7, x_8, x_165);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_175 = x_194;
x_176 = x_195;
goto block_191;
}
else
{
uint8_t x_196; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_196 = !lean_is_exclusive(x_193);
if (x_196 == 0)
{
return x_193;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_193, 0);
x_198 = lean_ctor_get(x_193, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_193);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
block_191:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_177 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_168)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_168;
}
lean_ctor_set(x_178, 0, x_35);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_array_get_size(x_26);
x_180 = lean_unsigned_to_nat(1u);
x_181 = lean_nat_sub(x_179, x_180);
x_182 = lean_nat_dec_lt(x_10, x_179);
lean_dec(x_179);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_181);
lean_dec(x_178);
lean_dec(x_167);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_166)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_166;
}
lean_ctor_set(x_183, 0, x_175);
lean_ctor_set(x_183, 1, x_176);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_box(0);
x_185 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(x_169, x_184, x_26, x_178, x_10, x_181);
lean_dec(x_178);
lean_dec(x_26);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; 
lean_dec(x_167);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_166)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_166;
}
lean_ctor_set(x_186, 0, x_175);
lean_ctor_set(x_186, 1, x_176);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_166);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Array_append___rarg(x_31, x_167);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_1 = x_10;
x_2 = x_188;
x_3 = x_189;
x_4 = x_175;
x_9 = x_176;
goto _start;
}
}
}
}
}
case 5:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_202 = lean_ctor_get(x_33, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_203 = x_33;
} else {
 lean_dec_ref(x_33);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_34, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_205 = x_34;
} else {
 lean_dec_ref(x_34);
 x_205 = lean_box(0);
}
x_206 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2;
x_207 = lean_array_get(x_206, x_26, x_10);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_box(3);
x_210 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_208, x_209);
lean_dec(x_208);
if (x_210 == 0)
{
x_211 = x_32;
goto block_254;
}
else
{
uint8_t x_255; 
x_255 = 1;
x_211 = x_255;
goto block_254;
}
block_254:
{
lean_object* x_212; lean_object* x_213; 
if (x_211 == 0)
{
lean_dec(x_207);
x_212 = x_4;
x_213 = x_202;
goto block_245;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_207, 1);
lean_inc(x_246);
lean_dec(x_207);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_31);
x_247 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_31, x_246, x_4, x_5, x_6, x_7, x_8, x_202);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_212 = x_248;
x_213 = x_249;
goto block_245;
}
else
{
uint8_t x_250; 
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_250 = !lean_is_exclusive(x_247);
if (x_250 == 0)
{
return x_247;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_247, 0);
x_252 = lean_ctor_get(x_247, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_247);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
block_245:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; 
x_214 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_205)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_205;
}
lean_ctor_set(x_215, 0, x_35);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_array_get_size(x_26);
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_nat_sub(x_216, x_217);
x_219 = lean_nat_dec_lt(x_10, x_216);
lean_dec(x_216);
if (x_219 == 0)
{
lean_dec(x_215);
lean_dec(x_204);
x_220 = x_212;
x_221 = x_213;
goto block_232;
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_box(0);
lean_inc(x_218);
x_234 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(x_206, x_233, x_26, x_215, x_10, x_218);
lean_dec(x_215);
if (lean_obj_tag(x_234) == 0)
{
lean_dec(x_204);
x_220 = x_212;
x_221 = x_213;
goto block_232;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec(x_234);
lean_inc(x_31);
x_236 = l_Array_append___rarg(x_31, x_204);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_238 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_236, x_237, x_212, x_5, x_6, x_7, x_8, x_213);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_220 = x_239;
x_221 = x_240;
goto block_232;
}
else
{
uint8_t x_241; 
lean_dec(x_218);
lean_dec(x_203);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_241 = !lean_is_exclusive(x_238);
if (x_241 == 0)
{
return x_238;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_238, 0);
x_243 = lean_ctor_get(x_238, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_238);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
}
block_232:
{
if (x_219 == 0)
{
lean_object* x_222; 
lean_dec(x_218);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_203)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_203;
}
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_box(0);
x_224 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg___closed__1;
x_225 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_206, x_223, x_26, x_224, x_10, x_218);
lean_dec(x_26);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_203)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_203;
}
lean_ctor_set(x_226, 0, x_220);
lean_ctor_set(x_226, 1, x_221);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_203);
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_227);
lean_dec(x_225);
x_228 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_229 = l_Array_append___rarg(x_31, x_228);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
x_1 = x_10;
x_2 = x_229;
x_3 = x_230;
x_4 = x_220;
x_9 = x_221;
goto _start;
}
}
}
}
}
}
default: 
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_265; 
x_256 = lean_ctor_get(x_33, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_257 = x_33;
} else {
 lean_dec_ref(x_33);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_34, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_259 = x_34;
} else {
 lean_dec_ref(x_34);
 x_259 = lean_box(0);
}
x_260 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2;
x_261 = lean_array_get(x_260, x_26, x_10);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_box(3);
x_264 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_262, x_263);
lean_dec(x_262);
if (x_264 == 0)
{
x_265 = x_32;
goto block_291;
}
else
{
uint8_t x_292; 
x_292 = 1;
x_265 = x_292;
goto block_291;
}
block_291:
{
lean_object* x_266; lean_object* x_267; 
if (x_265 == 0)
{
lean_dec(x_261);
x_266 = x_4;
x_267 = x_256;
goto block_282;
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_261, 1);
lean_inc(x_283);
lean_dec(x_261);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_31);
x_284 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_31, x_283, x_4, x_5, x_6, x_7, x_8, x_256);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_266 = x_285;
x_267 = x_286;
goto block_282;
}
else
{
uint8_t x_287; 
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_287 = !lean_is_exclusive(x_284);
if (x_287 == 0)
{
return x_284;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_284, 0);
x_289 = lean_ctor_get(x_284, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_284);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
block_282:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_268 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_259)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_259;
}
lean_ctor_set(x_269, 0, x_35);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_array_get_size(x_26);
x_271 = lean_unsigned_to_nat(1u);
x_272 = lean_nat_sub(x_270, x_271);
x_273 = lean_nat_dec_lt(x_10, x_270);
lean_dec(x_270);
if (x_273 == 0)
{
lean_object* x_274; 
lean_dec(x_272);
lean_dec(x_269);
lean_dec(x_258);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_257)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_257;
}
lean_ctor_set(x_274, 0, x_266);
lean_ctor_set(x_274, 1, x_267);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_box(0);
x_276 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(x_260, x_275, x_26, x_269, x_10, x_272);
lean_dec(x_269);
lean_dec(x_26);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; 
lean_dec(x_258);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_257)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_257;
}
lean_ctor_set(x_277, 0, x_266);
lean_ctor_set(x_277, 1, x_267);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_257);
x_278 = lean_ctor_get(x_276, 0);
lean_inc(x_278);
lean_dec(x_276);
x_279 = l_Array_append___rarg(x_31, x_258);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_1 = x_10;
x_2 = x_279;
x_3 = x_280;
x_4 = x_266;
x_9 = x_267;
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
uint8_t x_293; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_293 = !lean_is_exclusive(x_33);
if (x_293 == 0)
{
return x_33;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_33, 0);
x_295 = lean_ctor_get(x_33, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_33);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
lean_object* x_297; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_4);
lean_ctor_set(x_297, 1, x_9);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_298 = l_Array_append___rarg(x_4, x_25);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_9);
return x_299;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify_process(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getUnify_process___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_array_uget(x_1, x_2);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_DiscrTree_Key_arity(x_12);
lean_dec(x_12);
x_15 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_14, x_15, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_17;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
case 1:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg(x_26, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = lean_usize_add(x_2, x_30);
x_2 = x_31;
x_4 = x_28;
x_9 = x_29;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
default: 
{
size_t x_37; size_t x_38; 
x_37 = 1;
x_38 = lean_usize_add(x_2, x_37);
x_2 = x_38;
goto _start;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_9);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg___boxed), 11, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Meta_DiscrTree_Key_arity(x_2);
x_10 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_11 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_9, x_10, x_3, x_1, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_9, x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg(x_8, x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___closed__1;
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg(x_20, x_18, x_19, lean_box(0), x_21, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_19);
lean_dec(x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_21 = 2;
lean_ctor_set_uint8(x_19, 5, x_21);
x_22 = 0;
x_23 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_22, x_23, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
switch (lean_obj_tag(x_26)) {
case 0:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_24, 1);
x_29 = lean_ctor_get(x_24, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
lean_inc(x_1);
x_31 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_32 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_26);
if (lean_obj_tag(x_32) == 0)
{
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_24, 0, x_31);
x_8 = x_24;
goto block_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_24);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_34, x_30, x_33, x_31, x_3, x_4, x_5, x_6, x_28);
x_8 = x_35;
goto block_17;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
lean_inc(x_1);
x_38 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_39 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_26);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_36);
x_8 = x_40;
goto block_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_42, x_37, x_41, x_38, x_3, x_4, x_5, x_6, x_36);
x_8 = x_43;
goto block_17;
}
}
}
case 1:
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_24);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_24, 1);
x_46 = lean_ctor_get(x_24, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
lean_inc(x_1);
x_48 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_49 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_26);
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_47);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_24, 0, x_48);
x_8 = x_24;
goto block_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_24);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_51, x_47, x_50, x_48, x_3, x_4, x_5, x_6, x_45);
x_8 = x_52;
goto block_17;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
lean_dec(x_24);
x_54 = lean_ctor_get(x_25, 1);
lean_inc(x_54);
lean_dec(x_25);
lean_inc(x_1);
x_55 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_56 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_26);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_53);
x_8 = x_57;
goto block_17;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_59, x_54, x_58, x_55, x_3, x_4, x_5, x_6, x_53);
x_8 = x_60;
goto block_17;
}
}
}
case 2:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_24, 1);
x_63 = lean_ctor_get(x_24, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_25, 1);
lean_inc(x_64);
lean_dec(x_25);
lean_inc(x_1);
x_65 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_66 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(x_1, x_26);
if (lean_obj_tag(x_66) == 0)
{
lean_dec(x_64);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_24, 0, x_65);
x_8 = x_24;
goto block_17;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_24);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_68, x_64, x_67, x_65, x_3, x_4, x_5, x_6, x_62);
x_8 = x_69;
goto block_17;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_24, 1);
lean_inc(x_70);
lean_dec(x_24);
x_71 = lean_ctor_get(x_25, 1);
lean_inc(x_71);
lean_dec(x_25);
lean_inc(x_1);
x_72 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_73 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(x_1, x_26);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_70);
x_8 = x_74;
goto block_17;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_76, x_71, x_75, x_72, x_3, x_4, x_5, x_6, x_70);
x_8 = x_77;
goto block_17;
}
}
}
case 3:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_25);
x_78 = lean_ctor_get(x_24, 1);
lean_inc(x_78);
lean_dec(x_24);
x_79 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_80 = l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg(x_1, x_79, x_3, x_4, x_5, x_6, x_78);
x_8 = x_80;
goto block_17;
}
case 4:
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_24);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_24, 1);
x_83 = lean_ctor_get(x_24, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_25, 1);
lean_inc(x_84);
lean_dec(x_25);
lean_inc(x_1);
x_85 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_86 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(x_1, x_26);
if (lean_obj_tag(x_86) == 0)
{
lean_dec(x_84);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_24, 0, x_85);
x_8 = x_24;
goto block_17;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_24);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_88, x_84, x_87, x_85, x_3, x_4, x_5, x_6, x_82);
x_8 = x_89;
goto block_17;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_24, 1);
lean_inc(x_90);
lean_dec(x_24);
x_91 = lean_ctor_get(x_25, 1);
lean_inc(x_91);
lean_dec(x_25);
lean_inc(x_1);
x_92 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_93 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(x_1, x_26);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
lean_dec(x_91);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_90);
x_8 = x_94;
goto block_17;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_96, x_91, x_95, x_92, x_3, x_4, x_5, x_6, x_90);
x_8 = x_97;
goto block_17;
}
}
}
case 5:
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_24);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_24, 1);
x_100 = lean_ctor_get(x_24, 0);
lean_dec(x_100);
x_101 = lean_ctor_get(x_25, 1);
lean_inc(x_101);
lean_dec(x_25);
lean_inc(x_1);
x_102 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_103 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(x_1, x_26);
if (lean_obj_tag(x_103) == 0)
{
lean_dec(x_101);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_24, 0, x_102);
x_8 = x_24;
goto block_17;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_free_object(x_24);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_unsigned_to_nat(0u);
x_106 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_105, x_101, x_104, x_102, x_3, x_4, x_5, x_6, x_99);
x_8 = x_106;
goto block_17;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_24, 1);
lean_inc(x_107);
lean_dec(x_24);
x_108 = lean_ctor_get(x_25, 1);
lean_inc(x_108);
lean_dec(x_25);
lean_inc(x_1);
x_109 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_110 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(x_1, x_26);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
lean_dec(x_108);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_107);
x_8 = x_111;
goto block_17;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_unsigned_to_nat(0u);
x_114 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_113, x_108, x_112, x_109, x_3, x_4, x_5, x_6, x_107);
x_8 = x_114;
goto block_17;
}
}
}
default: 
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_24);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_24, 1);
x_117 = lean_ctor_get(x_24, 0);
lean_dec(x_117);
x_118 = lean_ctor_get(x_25, 1);
lean_inc(x_118);
lean_dec(x_25);
lean_inc(x_1);
x_119 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_120 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(x_1, x_26);
if (lean_obj_tag(x_120) == 0)
{
lean_dec(x_118);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_24, 0, x_119);
x_8 = x_24;
goto block_17;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_free_object(x_24);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_122, x_118, x_121, x_119, x_3, x_4, x_5, x_6, x_116);
x_8 = x_123;
goto block_17;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_24, 1);
lean_inc(x_124);
lean_dec(x_24);
x_125 = lean_ctor_get(x_25, 1);
lean_inc(x_125);
lean_dec(x_25);
lean_inc(x_1);
x_126 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_127 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(x_1, x_26);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
lean_dec(x_125);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_124);
x_8 = x_128;
goto block_17;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_unsigned_to_nat(0u);
x_131 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_130, x_125, x_129, x_126, x_3, x_4, x_5, x_6, x_124);
x_8 = x_131;
goto block_17;
}
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_24);
if (x_132 == 0)
{
x_8 = x_24;
goto block_17;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_24, 0);
x_134 = lean_ctor_get(x_24, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_24);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_8 = x_135;
goto block_17;
}
}
}
else
{
uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; lean_object* x_153; 
x_136 = lean_ctor_get_uint8(x_19, 0);
x_137 = lean_ctor_get_uint8(x_19, 1);
x_138 = lean_ctor_get_uint8(x_19, 2);
x_139 = lean_ctor_get_uint8(x_19, 3);
x_140 = lean_ctor_get_uint8(x_19, 4);
x_141 = lean_ctor_get_uint8(x_19, 6);
x_142 = lean_ctor_get_uint8(x_19, 7);
x_143 = lean_ctor_get_uint8(x_19, 8);
x_144 = lean_ctor_get_uint8(x_19, 9);
x_145 = lean_ctor_get_uint8(x_19, 10);
x_146 = lean_ctor_get_uint8(x_19, 11);
x_147 = lean_ctor_get_uint8(x_19, 12);
x_148 = lean_ctor_get_uint8(x_19, 13);
lean_dec(x_19);
x_149 = 2;
x_150 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_150, 0, x_136);
lean_ctor_set_uint8(x_150, 1, x_137);
lean_ctor_set_uint8(x_150, 2, x_138);
lean_ctor_set_uint8(x_150, 3, x_139);
lean_ctor_set_uint8(x_150, 4, x_140);
lean_ctor_set_uint8(x_150, 5, x_149);
lean_ctor_set_uint8(x_150, 6, x_141);
lean_ctor_set_uint8(x_150, 7, x_142);
lean_ctor_set_uint8(x_150, 8, x_143);
lean_ctor_set_uint8(x_150, 9, x_144);
lean_ctor_set_uint8(x_150, 10, x_145);
lean_ctor_set_uint8(x_150, 11, x_146);
lean_ctor_set_uint8(x_150, 12, x_147);
lean_ctor_set_uint8(x_150, 13, x_148);
lean_ctor_set(x_3, 0, x_150);
x_151 = 0;
x_152 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_153 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_151, x_152, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
switch (lean_obj_tag(x_155)) {
case 0:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_157 = x_153;
} else {
 lean_dec_ref(x_153);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 1);
lean_inc(x_158);
lean_dec(x_154);
lean_inc(x_1);
x_159 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_160 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_155);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
lean_dec(x_158);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_157)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_157;
}
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_156);
x_8 = x_161;
goto block_17;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_157);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_unsigned_to_nat(0u);
x_164 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_163, x_158, x_162, x_159, x_3, x_4, x_5, x_6, x_156);
x_8 = x_164;
goto block_17;
}
}
case 1:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_165 = lean_ctor_get(x_153, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_166 = x_153;
} else {
 lean_dec_ref(x_153);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_154, 1);
lean_inc(x_167);
lean_dec(x_154);
lean_inc(x_1);
x_168 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_169 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_155);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
lean_dec(x_167);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_166)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_166;
}
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_165);
x_8 = x_170;
goto block_17;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_166);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_unsigned_to_nat(0u);
x_173 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_172, x_167, x_171, x_168, x_3, x_4, x_5, x_6, x_165);
x_8 = x_173;
goto block_17;
}
}
case 2:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_153, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_175 = x_153;
} else {
 lean_dec_ref(x_153);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_154, 1);
lean_inc(x_176);
lean_dec(x_154);
lean_inc(x_1);
x_177 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_178 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(x_1, x_155);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
lean_dec(x_176);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_175)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_175;
}
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_174);
x_8 = x_179;
goto block_17;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_175);
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_unsigned_to_nat(0u);
x_182 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_181, x_176, x_180, x_177, x_3, x_4, x_5, x_6, x_174);
x_8 = x_182;
goto block_17;
}
}
case 3:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_154);
x_183 = lean_ctor_get(x_153, 1);
lean_inc(x_183);
lean_dec(x_153);
x_184 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_185 = l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg(x_1, x_184, x_3, x_4, x_5, x_6, x_183);
x_8 = x_185;
goto block_17;
}
case 4:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_153, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_187 = x_153;
} else {
 lean_dec_ref(x_153);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_154, 1);
lean_inc(x_188);
lean_dec(x_154);
lean_inc(x_1);
x_189 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_190 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(x_1, x_155);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; 
lean_dec(x_188);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_187)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_187;
}
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_186);
x_8 = x_191;
goto block_17;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_187);
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_unsigned_to_nat(0u);
x_194 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_193, x_188, x_192, x_189, x_3, x_4, x_5, x_6, x_186);
x_8 = x_194;
goto block_17;
}
}
case 5:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_153, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_196 = x_153;
} else {
 lean_dec_ref(x_153);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_154, 1);
lean_inc(x_197);
lean_dec(x_154);
lean_inc(x_1);
x_198 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_199 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(x_1, x_155);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; 
lean_dec(x_197);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_196)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_196;
}
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_195);
x_8 = x_200;
goto block_17;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_196);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_unsigned_to_nat(0u);
x_203 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_202, x_197, x_201, x_198, x_3, x_4, x_5, x_6, x_195);
x_8 = x_203;
goto block_17;
}
}
default: 
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_153, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_205 = x_153;
} else {
 lean_dec_ref(x_153);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_154, 1);
lean_inc(x_206);
lean_dec(x_154);
lean_inc(x_1);
x_207 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_208 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(x_1, x_155);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; 
lean_dec(x_206);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_205)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_205;
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_204);
x_8 = x_209;
goto block_17;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_205);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_unsigned_to_nat(0u);
x_212 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_211, x_206, x_210, x_207, x_3, x_4, x_5, x_6, x_204);
x_8 = x_212;
goto block_17;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_213 = lean_ctor_get(x_153, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_153, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_215 = x_153;
} else {
 lean_dec_ref(x_153);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
x_8 = x_216;
goto block_17;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; uint8_t x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_241; lean_object* x_242; 
x_217 = lean_ctor_get(x_3, 0);
x_218 = lean_ctor_get(x_3, 1);
x_219 = lean_ctor_get(x_3, 2);
x_220 = lean_ctor_get(x_3, 3);
x_221 = lean_ctor_get(x_3, 4);
x_222 = lean_ctor_get(x_3, 5);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_3);
x_223 = lean_ctor_get_uint8(x_217, 0);
x_224 = lean_ctor_get_uint8(x_217, 1);
x_225 = lean_ctor_get_uint8(x_217, 2);
x_226 = lean_ctor_get_uint8(x_217, 3);
x_227 = lean_ctor_get_uint8(x_217, 4);
x_228 = lean_ctor_get_uint8(x_217, 6);
x_229 = lean_ctor_get_uint8(x_217, 7);
x_230 = lean_ctor_get_uint8(x_217, 8);
x_231 = lean_ctor_get_uint8(x_217, 9);
x_232 = lean_ctor_get_uint8(x_217, 10);
x_233 = lean_ctor_get_uint8(x_217, 11);
x_234 = lean_ctor_get_uint8(x_217, 12);
x_235 = lean_ctor_get_uint8(x_217, 13);
if (lean_is_exclusive(x_217)) {
 x_236 = x_217;
} else {
 lean_dec_ref(x_217);
 x_236 = lean_box(0);
}
x_237 = 2;
if (lean_is_scalar(x_236)) {
 x_238 = lean_alloc_ctor(0, 0, 14);
} else {
 x_238 = x_236;
}
lean_ctor_set_uint8(x_238, 0, x_223);
lean_ctor_set_uint8(x_238, 1, x_224);
lean_ctor_set_uint8(x_238, 2, x_225);
lean_ctor_set_uint8(x_238, 3, x_226);
lean_ctor_set_uint8(x_238, 4, x_227);
lean_ctor_set_uint8(x_238, 5, x_237);
lean_ctor_set_uint8(x_238, 6, x_228);
lean_ctor_set_uint8(x_238, 7, x_229);
lean_ctor_set_uint8(x_238, 8, x_230);
lean_ctor_set_uint8(x_238, 9, x_231);
lean_ctor_set_uint8(x_238, 10, x_232);
lean_ctor_set_uint8(x_238, 11, x_233);
lean_ctor_set_uint8(x_238, 12, x_234);
lean_ctor_set_uint8(x_238, 13, x_235);
x_239 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_218);
lean_ctor_set(x_239, 2, x_219);
lean_ctor_set(x_239, 3, x_220);
lean_ctor_set(x_239, 4, x_221);
lean_ctor_set(x_239, 5, x_222);
x_240 = 0;
x_241 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_239);
x_242 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_240, x_241, x_239, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
switch (lean_obj_tag(x_244)) {
case 0:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_246 = x_242;
} else {
 lean_dec_ref(x_242);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_243, 1);
lean_inc(x_247);
lean_dec(x_243);
lean_inc(x_1);
x_248 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_249 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_244);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; 
lean_dec(x_247);
lean_dec(x_239);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_246)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_246;
}
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_245);
x_8 = x_250;
goto block_17;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_246);
x_251 = lean_ctor_get(x_249, 0);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_unsigned_to_nat(0u);
x_253 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_252, x_247, x_251, x_248, x_239, x_4, x_5, x_6, x_245);
x_8 = x_253;
goto block_17;
}
}
case 1:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_242, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_255 = x_242;
} else {
 lean_dec_ref(x_242);
 x_255 = lean_box(0);
}
x_256 = lean_ctor_get(x_243, 1);
lean_inc(x_256);
lean_dec(x_243);
lean_inc(x_1);
x_257 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_258 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_244);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
lean_dec(x_256);
lean_dec(x_239);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_255)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_255;
}
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_254);
x_8 = x_259;
goto block_17;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_255);
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_unsigned_to_nat(0u);
x_262 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_261, x_256, x_260, x_257, x_239, x_4, x_5, x_6, x_254);
x_8 = x_262;
goto block_17;
}
}
case 2:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_242, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_264 = x_242;
} else {
 lean_dec_ref(x_242);
 x_264 = lean_box(0);
}
x_265 = lean_ctor_get(x_243, 1);
lean_inc(x_265);
lean_dec(x_243);
lean_inc(x_1);
x_266 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_267 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(x_1, x_244);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; 
lean_dec(x_265);
lean_dec(x_239);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_264)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_264;
}
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_263);
x_8 = x_268;
goto block_17;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_264);
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
lean_dec(x_267);
x_270 = lean_unsigned_to_nat(0u);
x_271 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_270, x_265, x_269, x_266, x_239, x_4, x_5, x_6, x_263);
x_8 = x_271;
goto block_17;
}
}
case 3:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_243);
x_272 = lean_ctor_get(x_242, 1);
lean_inc(x_272);
lean_dec(x_242);
x_273 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_274 = l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__10___rarg(x_1, x_273, x_239, x_4, x_5, x_6, x_272);
x_8 = x_274;
goto block_17;
}
case 4:
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_275 = lean_ctor_get(x_242, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_276 = x_242;
} else {
 lean_dec_ref(x_242);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_243, 1);
lean_inc(x_277);
lean_dec(x_243);
lean_inc(x_1);
x_278 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_279 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__14___rarg(x_1, x_244);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; 
lean_dec(x_277);
lean_dec(x_239);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_276)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_276;
}
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_275);
x_8 = x_280;
goto block_17;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_276);
x_281 = lean_ctor_get(x_279, 0);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_unsigned_to_nat(0u);
x_283 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_282, x_277, x_281, x_278, x_239, x_4, x_5, x_6, x_275);
x_8 = x_283;
goto block_17;
}
}
case 5:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_284 = lean_ctor_get(x_242, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_285 = x_242;
} else {
 lean_dec_ref(x_242);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_243, 1);
lean_inc(x_286);
lean_dec(x_243);
lean_inc(x_1);
x_287 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_288 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__17___rarg(x_1, x_244);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; 
lean_dec(x_286);
lean_dec(x_239);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_285)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_285;
}
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_284);
x_8 = x_289;
goto block_17;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_285);
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
lean_dec(x_288);
x_291 = lean_unsigned_to_nat(0u);
x_292 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_291, x_286, x_290, x_287, x_239, x_4, x_5, x_6, x_284);
x_8 = x_292;
goto block_17;
}
}
default: 
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_242, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_294 = x_242;
} else {
 lean_dec_ref(x_242);
 x_294 = lean_box(0);
}
x_295 = lean_ctor_get(x_243, 1);
lean_inc(x_295);
lean_dec(x_243);
lean_inc(x_1);
x_296 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_297 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__20___rarg(x_1, x_244);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; 
lean_dec(x_295);
lean_dec(x_239);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_294)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_294;
}
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_293);
x_8 = x_298;
goto block_17;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_294);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_unsigned_to_nat(0u);
x_301 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_300, x_295, x_299, x_296, x_239, x_4, x_5, x_6, x_293);
x_8 = x_301;
goto block_17;
}
}
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_239);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_302 = lean_ctor_get(x_242, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_242, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_304 = x_242;
} else {
 lean_dec_ref(x_242);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
x_8 = x_305;
goto block_17;
}
}
block_17:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getUnify___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__9___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__8___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__12___rarg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__16___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__15___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__19___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__18___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_DiscrTree_getUnify___spec__22___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_getUnify___spec__21___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_DiscrTree_instLTKey = _init_l_Lean_Meta_DiscrTree_instLTKey();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instLTKey);
l_Lean_Meta_DiscrTree_Key_format___closed__1 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__1);
l_Lean_Meta_DiscrTree_Key_format___closed__2 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__2);
l_Lean_Meta_DiscrTree_Key_format___closed__3 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__3);
l_Lean_Meta_DiscrTree_Key_format___closed__4 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__4);
l_Lean_Meta_DiscrTree_Key_format___closed__5 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__5();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__5);
l_Lean_Meta_DiscrTree_Key_format___closed__6 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__6();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__6);
l_Lean_Meta_DiscrTree_Key_format___closed__7 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__7();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__7);
l_Lean_Meta_DiscrTree_Key_format___closed__8 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__8();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__8);
l_Lean_Meta_DiscrTree_instToFormatKey___closed__1 = _init_l_Lean_Meta_DiscrTree_instToFormatKey___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instToFormatKey___closed__1);
l_Lean_Meta_DiscrTree_instToFormatKey = _init_l_Lean_Meta_DiscrTree_instToFormatKey();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instToFormatKey);
l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1 = _init_l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1);
l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2 = _init_l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2);
l_Lean_Meta_DiscrTree_empty___closed__1 = _init_l_Lean_Meta_DiscrTree_empty___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_empty___closed__1);
l_Lean_Meta_DiscrTree_empty___closed__2 = _init_l_Lean_Meta_DiscrTree_empty___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_empty___closed__2);
l_Lean_Meta_DiscrTree_empty___closed__3 = _init_l_Lean_Meta_DiscrTree_empty___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_empty___closed__3);
l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1 = _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1);
l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2 = _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2);
l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3 = _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3);
l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4 = _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4);
l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5 = _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5);
l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6 = _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6);
l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7 = _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7);
l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8 = _init_l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8);
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
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__9 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__9();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__9);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__10 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__10();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__10);
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
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__8 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__8();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__8);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__9 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__9();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__9);
l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1 = _init_l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1);
l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2 = _init_l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity);
l_Lean_Meta_DiscrTree_mkPath___closed__1 = _init_l_Lean_Meta_DiscrTree_mkPath___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_mkPath___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___closed__2);
l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__1 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__1();
l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___closed__2();
l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___closed__1);
l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg___closed__1 = _init_l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_DiscrTree_insertCore___spec__12___rarg___closed__1);
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
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__4 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__4();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__4);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchLoop___rarg___closed__1);
l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___closed__1 = _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__11___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
