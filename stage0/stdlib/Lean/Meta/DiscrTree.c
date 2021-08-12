// Lean compiler output
// Module: Lean.Meta.DiscrTree
// Imports: Init Lean.Meta.Basic Lean.Meta.FunInfo Lean.Meta.InferType Lean.Meta.WHNF
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
lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__11(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_initCapacity;
lean_object* l_Lean_Meta_DiscrTree_getMatch_process_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_join(lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey_match__1(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__10;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__14(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___boxed(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__3;
static lean_object* l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__1;
static lean_object* l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__6;
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__4;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__8;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__13(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_arity_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__5(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__1;
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx_match__1(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_MetavarContext_getExprAssignmentDomain___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instDecidableLt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__2;
extern lean_object* l_Lean_Meta_DiscrTree_instHashableKey;
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_format_match__1(lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch_process_match__2(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__2(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__1(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___boxed(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify_process_match__1(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfDT(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__5;
lean_object* l_Lean_Meta_DiscrTree_Key_format(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPathAux_match__1(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__3;
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfEta_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfUntilBadKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_format(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree___rarg(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__8(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__6(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object*);
static lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1;
static lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__4;
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__6;
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3;
uint8_t l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(lean_object*, lean_object*);
lean_object* l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__9;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__3;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__12(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_lt___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__8;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insert(lean_object*);
static lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__6;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch_process_match__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__1;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore_match__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__5;
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3(lean_object*);
lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_format_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify_process___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__2;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__5;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_List_format___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId;
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__5;
lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfEta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_arity(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify_process_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie(lean_object*);
lean_object* l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___spec__1(lean_object*);
uint8_t l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format_match__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__4;
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__2;
extern lean_object* l_Lean_Meta_DiscrTree_instBEqKey;
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify_process(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__9;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__16___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__1;
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__3(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux_match__1(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch_process_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instDecidableLt___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___boxed(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__1;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch_match__1(lean_object*);
lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__8;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__16(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__7;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__2;
static lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_instToFormatKey___closed__1;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar___closed__1;
lean_object* l_Lean_Meta_DiscrTree_format___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___closed__7;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1;
static lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2;
static lean_object* l_Lean_Meta_DiscrTree_mkPath___closed__1;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__4;
static lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1;
lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object*);
uint8_t l_Array_contains___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfEta_match__1(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13(lean_object*);
lean_object* l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_tmpStar;
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_format_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch_process___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2;
lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfDT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__7(lean_object*);
lean_object* l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult_match__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___rarg(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__1;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__10(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__6;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__3(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instToFormatKey;
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__2;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_format___rarg___closed__1;
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_arity___boxed(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_format_match__1(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_hasNoindexAnnotation___boxed(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify_process_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_lt_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__2;
lean_object* l_Lean_Meta_DiscrTree_getMatch_process(lean_object*);
lean_object* lean_array_pop(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__7;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__5;
lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_arity_match__1(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__3;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format_match__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__16___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__4(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__14___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___rarg(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs_match__1(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfUntilBadKey_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPathAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instLTKey;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___closed__7;
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs_match__1(lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___closed__1;
lean_object* l_Lean_Meta_DiscrTree_Trie_format_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_lt_match__1(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey(lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isStrictImplicit(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_6, x_9, x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_2(x_5, x_12, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_apply_1(x_2, x_17);
return x_18;
}
case 4:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_apply_1(x_3, x_19);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_apply_1(x_7, x_21);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_apply_2(x_8, x_23, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_ctorIdx_match__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx(lean_object* x_1) {
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
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_lt_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_4(x_5, x_8, x_9, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_5);
x_13 = lean_apply_2(x_7, x_1, x_2);
return x_13;
}
}
case 1:
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_4(x_4, x_14, x_15, x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_apply_2(x_7, x_1, x_2);
return x_19;
}
}
case 2:
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_2(x_3, x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_3);
x_23 = lean_apply_2(x_7, x_1, x_2);
return x_23;
}
}
case 6:
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_apply_4(x_6, x_24, x_25, x_26, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_6);
x_29 = lean_apply_2(x_7, x_1, x_2);
return x_29;
}
}
default: 
{
lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_apply_2(x_7, x_1, x_2);
return x_30;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_lt_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_lt_match__1___rarg), 7, 0);
return x_2;
}
}
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_DiscrTree_Key_lt___boxed(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_Lean_Meta_DiscrTree_instDecidableLt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Meta_DiscrTree_Key_lt(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_DiscrTree_instDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_DiscrTree_instDecidableLt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_format_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_6, x_10, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_8, x_13, x_14);
return x_15;
}
case 2:
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_apply_1(x_4, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_apply_1(x_5, x_19);
return x_20;
}
}
case 3:
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = lean_apply_1(x_2, x_21);
return x_22;
}
case 4:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_apply_1(x_3, x_23);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_apply_1(x_9, x_25);
return x_26;
}
default: 
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_apply_2(x_7, x_27, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_format_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_format_match__1___rarg), 9, 0);
return x_2;
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
lean_object* l_Lean_Meta_DiscrTree_Key_format(lean_object* x_1) {
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
lean_object* l_Lean_Meta_DiscrTree_Key_arity_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_3, x_10, x_11);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_4, x_13);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_2(x_5, x_15, x_16);
return x_17;
}
default: 
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_apply_1(x_6, x_1);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_arity_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_arity_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_arity(lean_object* x_1) {
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
lean_object* l_Lean_Meta_DiscrTree_Key_arity___boxed(lean_object* x_1) {
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
lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object* x_1) {
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
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_empty___closed__3;
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_format_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_format_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format_match__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_format_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_format_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format_match__2___rarg), 2, 0);
return x_3;
}
}
static lean_object* _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" => ");
return x_1;
}
}
static lean_object* _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(x_1, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_Meta_DiscrTree_Key_format(x_8);
x_11 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_9);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
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
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_24);
return x_2;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
x_27 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(x_1, x_26);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Meta_DiscrTree_Key_format(x_28);
x_31 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_29);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
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
lean_ctor_set(x_45, 1, x_27);
return x_45;
}
}
}
}
lean_object* l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg), 2, 0);
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
x_1 = lean_mk_string("#");
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
x_1 = lean_mk_string(" ");
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
lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Array_isEmpty___rarg(x_3);
x_6 = lean_array_to_list(lean_box(0), x_4);
lean_inc(x_1);
x_7 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg(x_1, x_6);
x_8 = l_Std_Format_join(x_7);
if (x_5 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_9 = lean_array_to_list(lean_box(0), x_3);
x_10 = l_List_format___rarg(x_1, x_9);
x_11 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__4;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__6;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__2;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
x_18 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_23 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = 0;
x_25 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__7;
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
x_34 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = 0;
x_36 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_35);
return x_37;
}
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_instToFormatTrie___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_format_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_DiscrTree_format_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = x_3 + x_8;
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
x_15 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_1);
x_17 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_11);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_Meta_DiscrTree_Key_format(x_3);
x_8 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_4);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5;
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
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg(x_1, x_6, x_5);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg), 5, 0);
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
lean_object* l_Lean_Meta_DiscrTree_format___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_3 = l_Lean_Meta_DiscrTree_instBEqKey;
x_4 = l_Lean_Meta_DiscrTree_instHashableKey;
x_5 = l_Lean_Meta_DiscrTree_format___rarg___closed__1;
x_6 = l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__1___rarg(x_1, x_3, x_4, x_2, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_DiscrTree_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_format___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_format___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_instToFormatDiscrTree(lean_object* x_1) {
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
lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_empty___closed__3;
return x_2;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_ignoreArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_5(x_4, x_1, x_6, x_7, x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_3(x_5, x_1, x_2, x_3);
return x_11;
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
uint8_t l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(lean_object* x_1) {
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
lean_dec(x_1);
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNumeral(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isNatType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_shouldAddAsStar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
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
lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object* x_1) {
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
lean_object* l_Lean_Meta_DiscrTree_hasNoindexAnnotation___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfEta_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfEta_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfEta_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfEta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_10 = lean_box_uint64(x_9);
x_11 = lean_apply_2(x_4, x_8, x_10);
return x_11;
}
case 4:
{
lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_3(x_3, x_12, x_13, x_15);
return x_16;
}
case 7:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_21 = lean_box_uint64(x_20);
x_22 = lean_apply_4(x_6, x_17, x_18, x_19, x_21);
return x_22;
}
case 9:
{
lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_25 = lean_box_uint64(x_24);
x_26 = lean_apply_2(x_2, x_23, x_25);
return x_26;
}
case 11:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_4(x_5, x_27, x_28, x_29, x_31);
return x_32;
}
default: 
{
lean_object* x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_apply_1(x_7, x_1);
return x_33;
}
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey_match__1___rarg), 7, 0);
return x_2;
}
}
uint8_t l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(lean_object* x_1) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfUntilBadKey_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(x_19);
if (x_20 == 0)
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
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_isBadKey(x_23);
if (x_24 == 0)
{
lean_dec(x_8);
x_1 = x_23;
x_6 = x_22;
goto _start;
}
else
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfUntilBadKey(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfDT(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfDT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfDT(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_11 = lean_box_uint64(x_10);
x_12 = lean_apply_2(x_5, x_9, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_2(x_6, x_13, x_15);
return x_16;
}
case 4:
{
lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_3(x_3, x_17, x_18, x_20);
return x_21;
}
case 7:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_26 = lean_box_uint64(x_25);
x_27 = lean_apply_4(x_7, x_22, x_23, x_24, x_26);
return x_27;
}
case 9:
{
lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_30 = lean_box_uint64(x_29);
x_31 = lean_apply_2(x_2, x_28, x_30);
return x_31;
}
case 11:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_4(x_4, x_32, x_33, x_34, x_36);
return x_37;
}
default: 
{
lean_object* x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_apply_1(x_8, x_1);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs_match__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfDT(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_DiscrTree_mkPathAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_DiscrTree_mkPathAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mkPathAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_instInhabitedExpr;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Array_isEmpty___rarg(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___spec__1(x_2);
x_11 = lean_array_pop(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_pushArgs(x_1, x_11, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_array_push(x_3, x_15);
x_18 = 0;
x_1 = x_18;
x_2 = x_16;
x_3 = x_17;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
}
}
lean_object* l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
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
lean_dec(x_10);
x_33 = 2;
x_34 = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(x_34, 0, x_23);
lean_ctor_set_uint8(x_34, 1, x_24);
lean_ctor_set_uint8(x_34, 2, x_25);
lean_ctor_set_uint8(x_34, 3, x_26);
lean_ctor_set_uint8(x_34, 4, x_27);
lean_ctor_set_uint8(x_34, 5, x_33);
lean_ctor_set_uint8(x_34, 6, x_28);
lean_ctor_set_uint8(x_34, 7, x_29);
lean_ctor_set_uint8(x_34, 8, x_30);
lean_ctor_set_uint8(x_34, 9, x_31);
lean_ctor_set_uint8(x_34, 10, x_32);
lean_ctor_set(x_2, 0, x_34);
x_35 = 1;
x_36 = l_Lean_Meta_DiscrTree_mkPathAux(x_35, x_8, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_2, 2);
x_48 = lean_ctor_get(x_2, 3);
x_49 = lean_ctor_get(x_2, 4);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
x_50 = lean_ctor_get_uint8(x_45, 0);
x_51 = lean_ctor_get_uint8(x_45, 1);
x_52 = lean_ctor_get_uint8(x_45, 2);
x_53 = lean_ctor_get_uint8(x_45, 3);
x_54 = lean_ctor_get_uint8(x_45, 4);
x_55 = lean_ctor_get_uint8(x_45, 6);
x_56 = lean_ctor_get_uint8(x_45, 7);
x_57 = lean_ctor_get_uint8(x_45, 8);
x_58 = lean_ctor_get_uint8(x_45, 9);
x_59 = lean_ctor_get_uint8(x_45, 10);
if (lean_is_exclusive(x_45)) {
 x_60 = x_45;
} else {
 lean_dec_ref(x_45);
 x_60 = lean_box(0);
}
x_61 = 2;
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 0, 11);
} else {
 x_62 = x_60;
}
lean_ctor_set_uint8(x_62, 0, x_50);
lean_ctor_set_uint8(x_62, 1, x_51);
lean_ctor_set_uint8(x_62, 2, x_52);
lean_ctor_set_uint8(x_62, 3, x_53);
lean_ctor_set_uint8(x_62, 4, x_54);
lean_ctor_set_uint8(x_62, 5, x_61);
lean_ctor_set_uint8(x_62, 6, x_55);
lean_ctor_set_uint8(x_62, 7, x_56);
lean_ctor_set_uint8(x_62, 8, x_57);
lean_ctor_set_uint8(x_62, 9, x_58);
lean_ctor_set_uint8(x_62, 10, x_59);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_46);
lean_ctor_set(x_63, 2, x_47);
lean_ctor_set(x_63, 3, x_48);
lean_ctor_set(x_63, 4, x_49);
x_64 = 1;
x_65 = l_Lean_Meta_DiscrTree_mkPathAux(x_64, x_8, x_7, x_63, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_3(x_3, x_1, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_2 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___boxed), 1, 0);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__1;
x_2 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_nat_add(x_8, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
x_13 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_14 = lean_array_get(x_13, x_6, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_7, 0);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = l_Lean_Meta_DiscrTree_Key_lt(x_16, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_8);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_12, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_array_fget(x_6, x_12);
x_22 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__2;
x_23 = lean_array_fset(x_6, x_12, x_22);
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
x_30 = lean_array_fset(x_23, x_12, x_21);
lean_dec(x_12);
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
x_36 = lean_array_fset(x_23, x_12, x_35);
lean_dec(x_12);
return x_36;
}
}
}
else
{
x_9 = x_12;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_15);
x_38 = lean_nat_dec_eq(x_12, x_8);
if (x_38 == 0)
{
lean_dec(x_8);
x_8 = x_12;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_1);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_4, x_40);
x_42 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_nat_add(x_8, x_40);
lean_dec(x_8);
x_45 = l_Array_insertAt___rarg(x_6, x_44, x_43);
lean_dec(x_44);
return x_45;
}
}
}
}
lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_6, x_10);
x_12 = lean_ctor_get(x_7, 0);
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
x_16 = lean_array_get_size(x_6);
x_17 = lean_nat_dec_lt(x_10, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_array_fget(x_6, x_10);
x_19 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__2;
x_20 = lean_array_fset(x_6, x_10, x_19);
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
x_34 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(x_6);
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
x_38 = lean_array_get_size(x_6);
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
return x_6;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_array_fget(x_6, x_40);
x_43 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__2;
x_44 = lean_array_fset(x_6, x_40, x_43);
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
x_56 = lean_array_get_size(x_6);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_56, x_57);
lean_dec(x_56);
x_59 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_35);
lean_dec(x_1);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_4, x_60);
x_62 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_61);
lean_dec(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_array_push(x_6, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_13);
lean_dec(x_1);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_4, x_65);
x_67 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_5);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Array_insertAt___rarg(x_6, x_10, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_4, x_70);
x_72 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_push(x_6, x_73);
return x_74;
}
}
}
lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_fget(x_2, x_4);
x_13 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(x_1, x_2, x_3, x_4, x_12, x_8, x_14);
lean_dec(x_14);
lean_ctor_set(x_5, 1, x_15);
return x_5;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_array_get_size(x_2);
x_19 = lean_nat_dec_lt(x_4, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___rarg(x_1, x_16, x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_array_fget(x_2, x_4);
x_23 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_inc(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(x_1, x_2, x_3, x_4, x_22, x_17, x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_binInsertM___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_DiscrTree_insertCore_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_DiscrTree_insertCore_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_insertCore_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.DiscrTree");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.DiscrTree.insertCore");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid key sequence");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2;
x_2 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3;
x_3 = lean_unsigned_to_nat(352u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_3, x_7);
x_9 = l_Lean_Meta_DiscrTree_instBEqKey;
x_10 = l_Lean_Meta_DiscrTree_instHashableKey;
lean_inc(x_8);
lean_inc(x_2);
x_11 = l_Std_PersistentHashMap_find_x3f___rarg(x_9, x_10, x_2, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_3, x_4, x_12);
x_14 = l_Std_PersistentHashMap_insert___rarg(x_9, x_10, x_2, x_8, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___rarg(x_1, x_3, x_4, x_16, x_15);
x_18 = l_Std_PersistentHashMap_insert___rarg(x_9, x_10, x_2, x_8, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1;
x_20 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__5;
x_21 = lean_panic_fn(x_19, x_20);
return x_21;
}
}
}
lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_insertCore___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_DiscrTree_insertCore___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_DiscrTree_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_12);
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
lean_dec(x_14);
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
lean_object* l_Lean_Meta_DiscrTree_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_insert___rarg), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_11 = lean_box_uint64(x_10);
x_12 = lean_apply_2(x_4, x_9, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_2(x_5, x_13, x_15);
return x_16;
}
case 4:
{
lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_3(x_3, x_17, x_18, x_20);
return x_21;
}
case 7:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_26 = lean_box_uint64(x_25);
x_27 = lean_apply_4(x_7, x_22, x_23, x_24, x_26);
return x_27;
}
case 9:
{
lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_30 = lean_box_uint64(x_29);
x_31 = lean_apply_2(x_2, x_28, x_30);
return x_31;
}
case 11:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_4(x_6, x_32, x_33, x_34, x_36);
return x_37;
}
default: 
{
lean_object* x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_apply_1(x_8, x_1);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs_match__1___rarg), 8, 0);
return x_2;
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
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_whnfDT(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = lean_ctor_get(x_13, 0);
lean_inc(x_45);
lean_dec(x_13);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_Expr_getAppNumArgsAux(x_11, x_46);
lean_inc(x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_empty_array_with_capacity(x_47);
lean_dec(x_47);
x_50 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_11, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_9, 0, x_51);
return x_9;
}
case 7:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_13, 2);
lean_inc(x_53);
lean_dec(x_13);
x_54 = l_Lean_Expr_hasLooseBVars(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3;
x_56 = lean_array_push(x_55, x_52);
x_57 = lean_array_push(x_56, x_53);
x_58 = lean_box(5);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_9, 0, x_59);
return x_9;
}
else
{
lean_object* x_60; 
lean_dec(x_53);
lean_dec(x_52);
x_60 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
lean_ctor_set(x_9, 0, x_60);
return x_9;
}
}
case 9:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = lean_ctor_get(x_13, 0);
lean_inc(x_61);
lean_dec(x_13);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_9, 0, x_64);
return x_9;
}
case 11:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_65 = lean_ctor_get(x_13, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_13, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_13, 2);
lean_inc(x_67);
lean_dec(x_13);
x_68 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
x_69 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1;
x_70 = lean_array_push(x_69, x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_9, 0, x_71);
return x_9;
}
default: 
{
lean_object* x_72; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_72 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
lean_ctor_set(x_9, 0, x_72);
return x_9;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_9, 0);
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_9);
x_75 = l_Lean_Expr_getAppFn(x_73);
switch (lean_obj_tag(x_75)) {
case 1:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Lean_Expr_getAppNumArgsAux(x_73, x_77);
lean_inc(x_78);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_empty_array_with_capacity(x_78);
lean_dec(x_78);
x_81 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_73, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
return x_83;
}
case 2:
{
lean_dec(x_73);
if (x_2 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_4, 0);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_84, 4);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
lean_dec(x_75);
x_87 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(x_86, x_4, x_5, x_6, x_7, x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
x_92 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
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
x_96 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_100 = x_87;
} else {
 lean_dec_ref(x_87);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_75);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_74);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_75);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_104 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_74);
return x_105;
}
}
case 4:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_106 = lean_ctor_get(x_75, 0);
lean_inc(x_106);
lean_dec(x_75);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l_Lean_Expr_getAppNumArgsAux(x_73, x_107);
lean_inc(x_108);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_mk_empty_array_with_capacity(x_108);
lean_dec(x_108);
x_111 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_73, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_74);
return x_113;
}
case 7:
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_114 = lean_ctor_get(x_75, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_75, 2);
lean_inc(x_115);
lean_dec(x_75);
x_116 = l_Lean_Expr_hasLooseBVars(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3;
x_118 = lean_array_push(x_117, x_114);
x_119 = lean_array_push(x_118, x_115);
x_120 = lean_box(5);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_74);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_115);
lean_dec(x_114);
x_123 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_74);
return x_124;
}
}
case 9:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_125 = lean_ctor_get(x_75, 0);
lean_inc(x_125);
lean_dec(x_75);
x_126 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_74);
return x_129;
}
case 11:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_130 = lean_ctor_get(x_75, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_75, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_75, 2);
lean_inc(x_132);
lean_dec(x_75);
x_133 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
x_134 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg___closed__1;
x_135 = lean_array_push(x_134, x_132);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_74);
return x_137;
}
default: 
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_138 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_74);
return x_139;
}
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_140 = !lean_is_exclusive(x_9);
if (x_140 == 0)
{
return x_9;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_9, 0);
x_142 = lean_ctor_get(x_9, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_9);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getMatchKeyArgs(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_DiscrTree_instBEqKey;
x_3 = l_Lean_Meta_DiscrTree_instHashableKey;
x_4 = lean_box(3);
x_5 = l_Std_PersistentHashMap_find_x3f___rarg(x_2, x_3, x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Meta_DiscrTree_mkPath___closed__1;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_DiscrTree_mkPath___closed__1;
x_10 = l_Array_append___rarg(x_9, x_8);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___rarg(lean_object* x_1, lean_object* x_2) {
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
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg(x_1, x_4, x_8, x_7);
lean_dec(x_4);
return x_11;
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_findKey___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch_process_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch_process_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatch_process_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch_process_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 5:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_1(x_4, x_1);
return x_9;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch_process_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatch_process_match__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatch_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__6___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__8___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16___rarg___boxed), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1() {
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
lean_object* l_Lean_Meta_DiscrTree_getMatch_process___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_13 = l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___spec__1(x_1);
x_14 = lean_array_pop(x_1);
x_15 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_15, x_10, x_16);
x_18 = 1;
x_19 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_13, x_18, x_19, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
x_28 = lean_box(3);
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_dec(x_17);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_30);
x_31 = lean_array_get_size(x_10);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_31, x_32);
x_34 = lean_nat_dec_lt(x_16, x_31);
lean_dec(x_31);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_35; 
x_35 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__1___rarg(x_10, x_22, x_16, x_33);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_20);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Array_append___rarg(x_14, x_26);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_1 = x_37;
x_2 = x_38;
x_8 = x_24;
goto _start;
}
}
}
case 1:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_40);
x_41 = lean_array_get_size(x_10);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_41, x_42);
x_44 = lean_nat_dec_lt(x_16, x_41);
lean_dec(x_41);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_45; 
x_45 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__2___rarg(x_10, x_22, x_16, x_43);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_45) == 0)
{
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_20);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Array_append___rarg(x_14, x_26);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_1 = x_47;
x_2 = x_48;
x_8 = x_24;
goto _start;
}
}
}
case 2:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_50);
x_51 = lean_array_get_size(x_10);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_51, x_52);
x_54 = lean_nat_dec_lt(x_16, x_51);
lean_dec(x_51);
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_55; 
x_55 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__3___rarg(x_10, x_22, x_16, x_53);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_20);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Array_append___rarg(x_14, x_26);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_1 = x_57;
x_2 = x_58;
x_8 = x_24;
goto _start;
}
}
}
case 3:
{
lean_free_object(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
case 4:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_60);
x_61 = lean_array_get_size(x_10);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_sub(x_61, x_62);
x_64 = lean_nat_dec_lt(x_16, x_61);
lean_dec(x_61);
if (x_64 == 0)
{
lean_dec(x_63);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_65; 
x_65 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__4___rarg(x_10, x_22, x_16, x_63);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_20);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Array_append___rarg(x_14, x_26);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_1 = x_67;
x_2 = x_68;
x_8 = x_24;
goto _start;
}
}
}
case 5:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_70);
x_71 = lean_array_get_size(x_10);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_sub(x_71, x_72);
x_74 = lean_nat_dec_lt(x_16, x_71);
lean_dec(x_71);
if (x_74 == 0)
{
lean_dec(x_73);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_75; 
lean_inc(x_73);
x_75 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__5___rarg(x_10, x_22, x_16, x_73);
lean_dec(x_22);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_26);
x_76 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_77 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__6___rarg(x_10, x_76, x_16, x_73);
lean_dec(x_10);
if (lean_obj_tag(x_77) == 0)
{
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_20);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_80 = l_Array_append___rarg(x_14, x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_1 = x_80;
x_2 = x_81;
x_8 = x_24;
goto _start;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_20);
x_83 = lean_ctor_get(x_75, 0);
lean_inc(x_83);
lean_dec(x_75);
lean_inc(x_14);
x_84 = l_Array_append___rarg(x_14, x_26);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_86 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_84, x_85, x_3, x_4, x_5, x_6, x_7, x_24);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
x_90 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_91 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7___rarg(x_10, x_90, x_16, x_73);
lean_dec(x_10);
if (lean_obj_tag(x_91) == 0)
{
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_86;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_free_object(x_86);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec(x_91);
x_93 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_94 = l_Array_append___rarg(x_14, x_93);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_1 = x_94;
x_2 = x_95;
x_3 = x_88;
x_8 = x_89;
goto _start;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_86, 0);
x_98 = lean_ctor_get(x_86, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_86);
x_99 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_100 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7___rarg(x_10, x_99, x_16, x_73);
lean_dec(x_10);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_104 = l_Array_append___rarg(x_14, x_103);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_1 = x_104;
x_2 = x_105;
x_3 = x_97;
x_8 = x_98;
goto _start;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_73);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_107 = !lean_is_exclusive(x_86);
if (x_107 == 0)
{
return x_86;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_86, 0);
x_109 = lean_ctor_get(x_86, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_86);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_111);
x_112 = lean_array_get_size(x_10);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_nat_sub(x_112, x_113);
x_115 = lean_nat_dec_lt(x_16, x_112);
lean_dec(x_112);
if (x_115 == 0)
{
lean_dec(x_114);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_116; 
x_116 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__8___rarg(x_10, x_22, x_16, x_114);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_116) == 0)
{
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_free_object(x_20);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Array_append___rarg(x_14, x_26);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_1 = x_118;
x_2 = x_119;
x_8 = x_24;
goto _start;
}
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_free_object(x_20);
x_121 = lean_ctor_get(x_17, 1);
lean_inc(x_121);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_122 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_14, x_121, x_3, x_4, x_5, x_6, x_7, x_24);
if (lean_obj_tag(x_122) == 0)
{
switch (lean_obj_tag(x_25)) {
case 0:
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_ctor_get(x_122, 1);
x_126 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_126);
x_127 = lean_array_get_size(x_10);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_sub(x_127, x_128);
x_130 = lean_nat_dec_lt(x_16, x_127);
lean_dec(x_127);
if (x_130 == 0)
{
lean_dec(x_129);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_131; 
x_131 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9___rarg(x_10, x_22, x_16, x_129);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_131) == 0)
{
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_free_object(x_122);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Array_append___rarg(x_14, x_26);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_1 = x_133;
x_2 = x_134;
x_3 = x_124;
x_8 = x_125;
goto _start;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_136 = lean_ctor_get(x_122, 0);
x_137 = lean_ctor_get(x_122, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_122);
x_138 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_138);
x_139 = lean_array_get_size(x_10);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_sub(x_139, x_140);
x_142 = lean_nat_dec_lt(x_16, x_139);
lean_dec(x_139);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_141);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_136);
lean_ctor_set(x_143, 1, x_137);
return x_143;
}
else
{
lean_object* x_144; 
x_144 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9___rarg(x_10, x_22, x_16, x_141);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_136);
lean_ctor_set(x_145, 1, x_137);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Array_append___rarg(x_14, x_26);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_1 = x_147;
x_2 = x_148;
x_3 = x_136;
x_8 = x_137;
goto _start;
}
}
}
}
case 1:
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_122);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_151 = lean_ctor_get(x_122, 0);
x_152 = lean_ctor_get(x_122, 1);
x_153 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_153);
x_154 = lean_array_get_size(x_10);
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_nat_sub(x_154, x_155);
x_157 = lean_nat_dec_lt(x_16, x_154);
lean_dec(x_154);
if (x_157 == 0)
{
lean_dec(x_156);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_158; 
x_158 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10___rarg(x_10, x_22, x_16, x_156);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_158) == 0)
{
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_free_object(x_122);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec(x_158);
x_160 = l_Array_append___rarg(x_14, x_26);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_1 = x_160;
x_2 = x_161;
x_3 = x_151;
x_8 = x_152;
goto _start;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_163 = lean_ctor_get(x_122, 0);
x_164 = lean_ctor_get(x_122, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_122);
x_165 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_165);
x_166 = lean_array_get_size(x_10);
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_nat_sub(x_166, x_167);
x_169 = lean_nat_dec_lt(x_16, x_166);
lean_dec(x_166);
if (x_169 == 0)
{
lean_object* x_170; 
lean_dec(x_168);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_163);
lean_ctor_set(x_170, 1, x_164);
return x_170;
}
else
{
lean_object* x_171; 
x_171 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10___rarg(x_10, x_22, x_16, x_168);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_163);
lean_ctor_set(x_172, 1, x_164);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Array_append___rarg(x_14, x_26);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_1 = x_174;
x_2 = x_175;
x_3 = x_163;
x_8 = x_164;
goto _start;
}
}
}
}
case 2:
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_122);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_178 = lean_ctor_get(x_122, 0);
x_179 = lean_ctor_get(x_122, 1);
x_180 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_180);
x_181 = lean_array_get_size(x_10);
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_nat_sub(x_181, x_182);
x_184 = lean_nat_dec_lt(x_16, x_181);
lean_dec(x_181);
if (x_184 == 0)
{
lean_dec(x_183);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_185; 
x_185 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11___rarg(x_10, x_22, x_16, x_183);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_185) == 0)
{
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_free_object(x_122);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec(x_185);
x_187 = l_Array_append___rarg(x_14, x_26);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_1 = x_187;
x_2 = x_188;
x_3 = x_178;
x_8 = x_179;
goto _start;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_190 = lean_ctor_get(x_122, 0);
x_191 = lean_ctor_get(x_122, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_122);
x_192 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_192);
x_193 = lean_array_get_size(x_10);
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_nat_sub(x_193, x_194);
x_196 = lean_nat_dec_lt(x_16, x_193);
lean_dec(x_193);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_195);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_190);
lean_ctor_set(x_197, 1, x_191);
return x_197;
}
else
{
lean_object* x_198; 
x_198 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11___rarg(x_10, x_22, x_16, x_195);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; 
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_190);
lean_ctor_set(x_199, 1, x_191);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Array_append___rarg(x_14, x_26);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_1 = x_201;
x_2 = x_202;
x_3 = x_190;
x_8 = x_191;
goto _start;
}
}
}
}
case 3:
{
uint8_t x_204; 
lean_free_object(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_204 = !lean_is_exclusive(x_122);
if (x_204 == 0)
{
return x_122;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_122, 0);
x_206 = lean_ctor_get(x_122, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_122);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
case 4:
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_122);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_209 = lean_ctor_get(x_122, 0);
x_210 = lean_ctor_get(x_122, 1);
x_211 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_211);
x_212 = lean_array_get_size(x_10);
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_sub(x_212, x_213);
x_215 = lean_nat_dec_lt(x_16, x_212);
lean_dec(x_212);
if (x_215 == 0)
{
lean_dec(x_214);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_216; 
x_216 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12___rarg(x_10, x_22, x_16, x_214);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_216) == 0)
{
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_free_object(x_122);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec(x_216);
x_218 = l_Array_append___rarg(x_14, x_26);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_1 = x_218;
x_2 = x_219;
x_3 = x_209;
x_8 = x_210;
goto _start;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_221 = lean_ctor_get(x_122, 0);
x_222 = lean_ctor_get(x_122, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_122);
x_223 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_223);
x_224 = lean_array_get_size(x_10);
x_225 = lean_unsigned_to_nat(1u);
x_226 = lean_nat_sub(x_224, x_225);
x_227 = lean_nat_dec_lt(x_16, x_224);
lean_dec(x_224);
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_226);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set(x_228, 1, x_222);
return x_228;
}
else
{
lean_object* x_229; 
x_229 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12___rarg(x_10, x_22, x_16, x_226);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_221);
lean_ctor_set(x_230, 1, x_222);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
lean_dec(x_229);
x_232 = l_Array_append___rarg(x_14, x_26);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_1 = x_232;
x_2 = x_233;
x_3 = x_221;
x_8 = x_222;
goto _start;
}
}
}
}
case 5:
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_122);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_236 = lean_ctor_get(x_122, 0);
x_237 = lean_ctor_get(x_122, 1);
x_238 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_238);
x_239 = lean_array_get_size(x_10);
x_240 = lean_unsigned_to_nat(1u);
x_241 = lean_nat_sub(x_239, x_240);
x_242 = lean_nat_dec_lt(x_16, x_239);
lean_dec(x_239);
if (x_242 == 0)
{
lean_dec(x_241);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_243; 
lean_inc(x_241);
x_243 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13___rarg(x_10, x_22, x_16, x_241);
lean_dec(x_22);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_26);
x_244 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_245 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14___rarg(x_10, x_244, x_16, x_241);
lean_dec(x_10);
if (lean_obj_tag(x_245) == 0)
{
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_free_object(x_122);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec(x_245);
x_247 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_248 = l_Array_append___rarg(x_14, x_247);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_1 = x_248;
x_2 = x_249;
x_3 = x_236;
x_8 = x_237;
goto _start;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_free_object(x_122);
x_251 = lean_ctor_get(x_243, 0);
lean_inc(x_251);
lean_dec(x_243);
lean_inc(x_14);
x_252 = l_Array_append___rarg(x_14, x_26);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_254 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_252, x_253, x_236, x_4, x_5, x_6, x_7, x_237);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_254, 0);
x_257 = lean_ctor_get(x_254, 1);
x_258 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_259 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15___rarg(x_10, x_258, x_16, x_241);
lean_dec(x_10);
if (lean_obj_tag(x_259) == 0)
{
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_254;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_free_object(x_254);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
lean_dec(x_259);
x_261 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_262 = l_Array_append___rarg(x_14, x_261);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_dec(x_260);
x_1 = x_262;
x_2 = x_263;
x_3 = x_256;
x_8 = x_257;
goto _start;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_254, 0);
x_266 = lean_ctor_get(x_254, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_254);
x_267 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_268 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15___rarg(x_10, x_267, x_16, x_241);
lean_dec(x_10);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_266);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_270 = lean_ctor_get(x_268, 0);
lean_inc(x_270);
lean_dec(x_268);
x_271 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_272 = l_Array_append___rarg(x_14, x_271);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
x_1 = x_272;
x_2 = x_273;
x_3 = x_265;
x_8 = x_266;
goto _start;
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_241);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_275 = !lean_is_exclusive(x_254);
if (x_275 == 0)
{
return x_254;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_254, 0);
x_277 = lean_ctor_get(x_254, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_254);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_279 = lean_ctor_get(x_122, 0);
x_280 = lean_ctor_get(x_122, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_122);
x_281 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_281);
x_282 = lean_array_get_size(x_10);
x_283 = lean_unsigned_to_nat(1u);
x_284 = lean_nat_sub(x_282, x_283);
x_285 = lean_nat_dec_lt(x_16, x_282);
lean_dec(x_282);
if (x_285 == 0)
{
lean_object* x_286; 
lean_dec(x_284);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_279);
lean_ctor_set(x_286, 1, x_280);
return x_286;
}
else
{
lean_object* x_287; 
lean_inc(x_284);
x_287 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13___rarg(x_10, x_22, x_16, x_284);
lean_dec(x_22);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_26);
x_288 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_289 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14___rarg(x_10, x_288, x_16, x_284);
lean_dec(x_10);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_279);
lean_ctor_set(x_290, 1, x_280);
return x_290;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_291 = lean_ctor_get(x_289, 0);
lean_inc(x_291);
lean_dec(x_289);
x_292 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_293 = l_Array_append___rarg(x_14, x_292);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
lean_dec(x_291);
x_1 = x_293;
x_2 = x_294;
x_3 = x_279;
x_8 = x_280;
goto _start;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_296 = lean_ctor_get(x_287, 0);
lean_inc(x_296);
lean_dec(x_287);
lean_inc(x_14);
x_297 = l_Array_append___rarg(x_14, x_26);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_299 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_297, x_298, x_279, x_4, x_5, x_6, x_7, x_280);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
x_303 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_304 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15___rarg(x_10, x_303, x_16, x_284);
lean_dec(x_10);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_302)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_302;
}
lean_ctor_set(x_305, 0, x_300);
lean_ctor_set(x_305, 1, x_301);
return x_305;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_302);
x_306 = lean_ctor_get(x_304, 0);
lean_inc(x_306);
lean_dec(x_304);
x_307 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_308 = l_Array_append___rarg(x_14, x_307);
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_dec(x_306);
x_1 = x_308;
x_2 = x_309;
x_3 = x_300;
x_8 = x_301;
goto _start;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_284);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_311 = lean_ctor_get(x_299, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_299, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_313 = x_299;
} else {
 lean_dec_ref(x_299);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
}
}
}
default: 
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_122);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_316 = lean_ctor_get(x_122, 0);
x_317 = lean_ctor_get(x_122, 1);
x_318 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_318);
x_319 = lean_array_get_size(x_10);
x_320 = lean_unsigned_to_nat(1u);
x_321 = lean_nat_sub(x_319, x_320);
x_322 = lean_nat_dec_lt(x_16, x_319);
lean_dec(x_319);
if (x_322 == 0)
{
lean_dec(x_321);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_323; 
x_323 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16___rarg(x_10, x_22, x_16, x_321);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_323) == 0)
{
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_free_object(x_122);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
lean_dec(x_323);
x_325 = l_Array_append___rarg(x_14, x_26);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_1 = x_325;
x_2 = x_326;
x_3 = x_316;
x_8 = x_317;
goto _start;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_328 = lean_ctor_get(x_122, 0);
x_329 = lean_ctor_get(x_122, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_122);
x_330 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_22, 1, x_330);
x_331 = lean_array_get_size(x_10);
x_332 = lean_unsigned_to_nat(1u);
x_333 = lean_nat_sub(x_331, x_332);
x_334 = lean_nat_dec_lt(x_16, x_331);
lean_dec(x_331);
if (x_334 == 0)
{
lean_object* x_335; 
lean_dec(x_333);
lean_dec(x_22);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_328);
lean_ctor_set(x_335, 1, x_329);
return x_335;
}
else
{
lean_object* x_336; 
x_336 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16___rarg(x_10, x_22, x_16, x_333);
lean_dec(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; 
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_328);
lean_ctor_set(x_337, 1, x_329);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_336, 0);
lean_inc(x_338);
lean_dec(x_336);
x_339 = l_Array_append___rarg(x_14, x_26);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_1 = x_339;
x_2 = x_340;
x_3 = x_328;
x_8 = x_329;
goto _start;
}
}
}
}
}
}
else
{
uint8_t x_342; 
lean_free_object(x_22);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_342 = !lean_is_exclusive(x_122);
if (x_342 == 0)
{
return x_122;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_122, 0);
x_344 = lean_ctor_get(x_122, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_122);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_346 = lean_ctor_get(x_20, 1);
x_347 = lean_ctor_get(x_22, 0);
x_348 = lean_ctor_get(x_22, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_22);
x_349 = lean_ctor_get(x_17, 0);
lean_inc(x_349);
x_350 = lean_box(3);
x_351 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_349, x_350);
lean_dec(x_349);
if (x_351 == 0)
{
lean_dec(x_17);
switch (lean_obj_tag(x_347)) {
case 0:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_352 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_347);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_array_get_size(x_10);
x_355 = lean_unsigned_to_nat(1u);
x_356 = lean_nat_sub(x_354, x_355);
x_357 = lean_nat_dec_lt(x_16, x_354);
lean_dec(x_354);
if (x_357 == 0)
{
lean_dec(x_356);
lean_dec(x_353);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_358; 
x_358 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__1___rarg(x_10, x_353, x_16, x_356);
lean_dec(x_353);
lean_dec(x_10);
if (lean_obj_tag(x_358) == 0)
{
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_free_object(x_20);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
lean_dec(x_358);
x_360 = l_Array_append___rarg(x_14, x_348);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_1 = x_360;
x_2 = x_361;
x_8 = x_346;
goto _start;
}
}
}
case 1:
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_363 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_347);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_array_get_size(x_10);
x_366 = lean_unsigned_to_nat(1u);
x_367 = lean_nat_sub(x_365, x_366);
x_368 = lean_nat_dec_lt(x_16, x_365);
lean_dec(x_365);
if (x_368 == 0)
{
lean_dec(x_367);
lean_dec(x_364);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_369; 
x_369 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__2___rarg(x_10, x_364, x_16, x_367);
lean_dec(x_364);
lean_dec(x_10);
if (lean_obj_tag(x_369) == 0)
{
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_free_object(x_20);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
lean_dec(x_369);
x_371 = l_Array_append___rarg(x_14, x_348);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_1 = x_371;
x_2 = x_372;
x_8 = x_346;
goto _start;
}
}
}
case 2:
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; 
x_374 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_347);
lean_ctor_set(x_375, 1, x_374);
x_376 = lean_array_get_size(x_10);
x_377 = lean_unsigned_to_nat(1u);
x_378 = lean_nat_sub(x_376, x_377);
x_379 = lean_nat_dec_lt(x_16, x_376);
lean_dec(x_376);
if (x_379 == 0)
{
lean_dec(x_378);
lean_dec(x_375);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_380; 
x_380 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__3___rarg(x_10, x_375, x_16, x_378);
lean_dec(x_375);
lean_dec(x_10);
if (lean_obj_tag(x_380) == 0)
{
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_free_object(x_20);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
lean_dec(x_380);
x_382 = l_Array_append___rarg(x_14, x_348);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_1 = x_382;
x_2 = x_383;
x_8 = x_346;
goto _start;
}
}
}
case 3:
{
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
case 4:
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; 
x_385 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_347);
lean_ctor_set(x_386, 1, x_385);
x_387 = lean_array_get_size(x_10);
x_388 = lean_unsigned_to_nat(1u);
x_389 = lean_nat_sub(x_387, x_388);
x_390 = lean_nat_dec_lt(x_16, x_387);
lean_dec(x_387);
if (x_390 == 0)
{
lean_dec(x_389);
lean_dec(x_386);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_391; 
x_391 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__4___rarg(x_10, x_386, x_16, x_389);
lean_dec(x_386);
lean_dec(x_10);
if (lean_obj_tag(x_391) == 0)
{
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_free_object(x_20);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
lean_dec(x_391);
x_393 = l_Array_append___rarg(x_14, x_348);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_1 = x_393;
x_2 = x_394;
x_8 = x_346;
goto _start;
}
}
}
case 5:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_396 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_347);
lean_ctor_set(x_397, 1, x_396);
x_398 = lean_array_get_size(x_10);
x_399 = lean_unsigned_to_nat(1u);
x_400 = lean_nat_sub(x_398, x_399);
x_401 = lean_nat_dec_lt(x_16, x_398);
lean_dec(x_398);
if (x_401 == 0)
{
lean_dec(x_400);
lean_dec(x_397);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_402; 
lean_inc(x_400);
x_402 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__5___rarg(x_10, x_397, x_16, x_400);
lean_dec(x_397);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; 
lean_dec(x_348);
x_403 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_404 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__6___rarg(x_10, x_403, x_16, x_400);
lean_dec(x_10);
if (lean_obj_tag(x_404) == 0)
{
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_free_object(x_20);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
lean_dec(x_404);
x_406 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_407 = l_Array_append___rarg(x_14, x_406);
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
lean_dec(x_405);
x_1 = x_407;
x_2 = x_408;
x_8 = x_346;
goto _start;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_free_object(x_20);
x_410 = lean_ctor_get(x_402, 0);
lean_inc(x_410);
lean_dec(x_402);
lean_inc(x_14);
x_411 = l_Array_append___rarg(x_14, x_348);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_413 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_411, x_412, x_3, x_4, x_5, x_6, x_7, x_346);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_416 = x_413;
} else {
 lean_dec_ref(x_413);
 x_416 = lean_box(0);
}
x_417 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_418 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7___rarg(x_10, x_417, x_16, x_400);
lean_dec(x_10);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_416)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_416;
}
lean_ctor_set(x_419, 0, x_414);
lean_ctor_set(x_419, 1, x_415);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_416);
x_420 = lean_ctor_get(x_418, 0);
lean_inc(x_420);
lean_dec(x_418);
x_421 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_422 = l_Array_append___rarg(x_14, x_421);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
lean_dec(x_420);
x_1 = x_422;
x_2 = x_423;
x_3 = x_414;
x_8 = x_415;
goto _start;
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_400);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_425 = lean_ctor_get(x_413, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_413, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_427 = x_413;
} else {
 lean_dec_ref(x_413);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_425);
lean_ctor_set(x_428, 1, x_426);
return x_428;
}
}
}
}
default: 
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_429 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_347);
lean_ctor_set(x_430, 1, x_429);
x_431 = lean_array_get_size(x_10);
x_432 = lean_unsigned_to_nat(1u);
x_433 = lean_nat_sub(x_431, x_432);
x_434 = lean_nat_dec_lt(x_16, x_431);
lean_dec(x_431);
if (x_434 == 0)
{
lean_dec(x_433);
lean_dec(x_430);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_435; 
x_435 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__8___rarg(x_10, x_430, x_16, x_433);
lean_dec(x_430);
lean_dec(x_10);
if (lean_obj_tag(x_435) == 0)
{
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_free_object(x_20);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
lean_dec(x_435);
x_437 = l_Array_append___rarg(x_14, x_348);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_1 = x_437;
x_2 = x_438;
x_8 = x_346;
goto _start;
}
}
}
}
}
else
{
lean_object* x_440; lean_object* x_441; 
lean_free_object(x_20);
x_440 = lean_ctor_get(x_17, 1);
lean_inc(x_440);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_441 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_14, x_440, x_3, x_4, x_5, x_6, x_7, x_346);
if (lean_obj_tag(x_441) == 0)
{
switch (lean_obj_tag(x_347)) {
case 0:
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_441, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_444 = x_441;
} else {
 lean_dec_ref(x_441);
 x_444 = lean_box(0);
}
x_445 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_347);
lean_ctor_set(x_446, 1, x_445);
x_447 = lean_array_get_size(x_10);
x_448 = lean_unsigned_to_nat(1u);
x_449 = lean_nat_sub(x_447, x_448);
x_450 = lean_nat_dec_lt(x_16, x_447);
lean_dec(x_447);
if (x_450 == 0)
{
lean_object* x_451; 
lean_dec(x_449);
lean_dec(x_446);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_444)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_444;
}
lean_ctor_set(x_451, 0, x_442);
lean_ctor_set(x_451, 1, x_443);
return x_451;
}
else
{
lean_object* x_452; 
x_452 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9___rarg(x_10, x_446, x_16, x_449);
lean_dec(x_446);
lean_dec(x_10);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; 
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_444)) {
 x_453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_453 = x_444;
}
lean_ctor_set(x_453, 0, x_442);
lean_ctor_set(x_453, 1, x_443);
return x_453;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_444);
x_454 = lean_ctor_get(x_452, 0);
lean_inc(x_454);
lean_dec(x_452);
x_455 = l_Array_append___rarg(x_14, x_348);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
lean_dec(x_454);
x_1 = x_455;
x_2 = x_456;
x_3 = x_442;
x_8 = x_443;
goto _start;
}
}
}
case 1:
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_458 = lean_ctor_get(x_441, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_441, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_460 = x_441;
} else {
 lean_dec_ref(x_441);
 x_460 = lean_box(0);
}
x_461 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_347);
lean_ctor_set(x_462, 1, x_461);
x_463 = lean_array_get_size(x_10);
x_464 = lean_unsigned_to_nat(1u);
x_465 = lean_nat_sub(x_463, x_464);
x_466 = lean_nat_dec_lt(x_16, x_463);
lean_dec(x_463);
if (x_466 == 0)
{
lean_object* x_467; 
lean_dec(x_465);
lean_dec(x_462);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_460)) {
 x_467 = lean_alloc_ctor(0, 2, 0);
} else {
 x_467 = x_460;
}
lean_ctor_set(x_467, 0, x_458);
lean_ctor_set(x_467, 1, x_459);
return x_467;
}
else
{
lean_object* x_468; 
x_468 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10___rarg(x_10, x_462, x_16, x_465);
lean_dec(x_462);
lean_dec(x_10);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; 
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_460)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_460;
}
lean_ctor_set(x_469, 0, x_458);
lean_ctor_set(x_469, 1, x_459);
return x_469;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_460);
x_470 = lean_ctor_get(x_468, 0);
lean_inc(x_470);
lean_dec(x_468);
x_471 = l_Array_append___rarg(x_14, x_348);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_1 = x_471;
x_2 = x_472;
x_3 = x_458;
x_8 = x_459;
goto _start;
}
}
}
case 2:
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; 
x_474 = lean_ctor_get(x_441, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_441, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_476 = x_441;
} else {
 lean_dec_ref(x_441);
 x_476 = lean_box(0);
}
x_477 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_347);
lean_ctor_set(x_478, 1, x_477);
x_479 = lean_array_get_size(x_10);
x_480 = lean_unsigned_to_nat(1u);
x_481 = lean_nat_sub(x_479, x_480);
x_482 = lean_nat_dec_lt(x_16, x_479);
lean_dec(x_479);
if (x_482 == 0)
{
lean_object* x_483; 
lean_dec(x_481);
lean_dec(x_478);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_476)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_476;
}
lean_ctor_set(x_483, 0, x_474);
lean_ctor_set(x_483, 1, x_475);
return x_483;
}
else
{
lean_object* x_484; 
x_484 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11___rarg(x_10, x_478, x_16, x_481);
lean_dec(x_478);
lean_dec(x_10);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; 
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_476)) {
 x_485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_485 = x_476;
}
lean_ctor_set(x_485, 0, x_474);
lean_ctor_set(x_485, 1, x_475);
return x_485;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_476);
x_486 = lean_ctor_get(x_484, 0);
lean_inc(x_486);
lean_dec(x_484);
x_487 = l_Array_append___rarg(x_14, x_348);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_1 = x_487;
x_2 = x_488;
x_3 = x_474;
x_8 = x_475;
goto _start;
}
}
}
case 3:
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_490 = lean_ctor_get(x_441, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_441, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_492 = x_441;
} else {
 lean_dec_ref(x_441);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_490);
lean_ctor_set(x_493, 1, x_491);
return x_493;
}
case 4:
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; 
x_494 = lean_ctor_get(x_441, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_441, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_496 = x_441;
} else {
 lean_dec_ref(x_441);
 x_496 = lean_box(0);
}
x_497 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_347);
lean_ctor_set(x_498, 1, x_497);
x_499 = lean_array_get_size(x_10);
x_500 = lean_unsigned_to_nat(1u);
x_501 = lean_nat_sub(x_499, x_500);
x_502 = lean_nat_dec_lt(x_16, x_499);
lean_dec(x_499);
if (x_502 == 0)
{
lean_object* x_503; 
lean_dec(x_501);
lean_dec(x_498);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_496)) {
 x_503 = lean_alloc_ctor(0, 2, 0);
} else {
 x_503 = x_496;
}
lean_ctor_set(x_503, 0, x_494);
lean_ctor_set(x_503, 1, x_495);
return x_503;
}
else
{
lean_object* x_504; 
x_504 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12___rarg(x_10, x_498, x_16, x_501);
lean_dec(x_498);
lean_dec(x_10);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; 
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_496)) {
 x_505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_505 = x_496;
}
lean_ctor_set(x_505, 0, x_494);
lean_ctor_set(x_505, 1, x_495);
return x_505;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_496);
x_506 = lean_ctor_get(x_504, 0);
lean_inc(x_506);
lean_dec(x_504);
x_507 = l_Array_append___rarg(x_14, x_348);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_1 = x_507;
x_2 = x_508;
x_3 = x_494;
x_8 = x_495;
goto _start;
}
}
}
case 5:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_510 = lean_ctor_get(x_441, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_441, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_512 = x_441;
} else {
 lean_dec_ref(x_441);
 x_512 = lean_box(0);
}
x_513 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_514 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_514, 0, x_347);
lean_ctor_set(x_514, 1, x_513);
x_515 = lean_array_get_size(x_10);
x_516 = lean_unsigned_to_nat(1u);
x_517 = lean_nat_sub(x_515, x_516);
x_518 = lean_nat_dec_lt(x_16, x_515);
lean_dec(x_515);
if (x_518 == 0)
{
lean_object* x_519; 
lean_dec(x_517);
lean_dec(x_514);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_512)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_512;
}
lean_ctor_set(x_519, 0, x_510);
lean_ctor_set(x_519, 1, x_511);
return x_519;
}
else
{
lean_object* x_520; 
lean_inc(x_517);
x_520 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13___rarg(x_10, x_514, x_16, x_517);
lean_dec(x_514);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; 
lean_dec(x_348);
x_521 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_522 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14___rarg(x_10, x_521, x_16, x_517);
lean_dec(x_10);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_512)) {
 x_523 = lean_alloc_ctor(0, 2, 0);
} else {
 x_523 = x_512;
}
lean_ctor_set(x_523, 0, x_510);
lean_ctor_set(x_523, 1, x_511);
return x_523;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_512);
x_524 = lean_ctor_get(x_522, 0);
lean_inc(x_524);
lean_dec(x_522);
x_525 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_526 = l_Array_append___rarg(x_14, x_525);
x_527 = lean_ctor_get(x_524, 1);
lean_inc(x_527);
lean_dec(x_524);
x_1 = x_526;
x_2 = x_527;
x_3 = x_510;
x_8 = x_511;
goto _start;
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_512);
x_529 = lean_ctor_get(x_520, 0);
lean_inc(x_529);
lean_dec(x_520);
lean_inc(x_14);
x_530 = l_Array_append___rarg(x_14, x_348);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_532 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_530, x_531, x_510, x_4, x_5, x_6, x_7, x_511);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_535 = x_532;
} else {
 lean_dec_ref(x_532);
 x_535 = lean_box(0);
}
x_536 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_537 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15___rarg(x_10, x_536, x_16, x_517);
lean_dec(x_10);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_535)) {
 x_538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_538 = x_535;
}
lean_ctor_set(x_538, 0, x_533);
lean_ctor_set(x_538, 1, x_534);
return x_538;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_535);
x_539 = lean_ctor_get(x_537, 0);
lean_inc(x_539);
lean_dec(x_537);
x_540 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_541 = l_Array_append___rarg(x_14, x_540);
x_542 = lean_ctor_get(x_539, 1);
lean_inc(x_542);
lean_dec(x_539);
x_1 = x_541;
x_2 = x_542;
x_3 = x_533;
x_8 = x_534;
goto _start;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_517);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_544 = lean_ctor_get(x_532, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_532, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_546 = x_532;
} else {
 lean_dec_ref(x_532);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
}
}
}
default: 
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; uint8_t x_556; 
x_548 = lean_ctor_get(x_441, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_441, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_550 = x_441;
} else {
 lean_dec_ref(x_441);
 x_550 = lean_box(0);
}
x_551 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_347);
lean_ctor_set(x_552, 1, x_551);
x_553 = lean_array_get_size(x_10);
x_554 = lean_unsigned_to_nat(1u);
x_555 = lean_nat_sub(x_553, x_554);
x_556 = lean_nat_dec_lt(x_16, x_553);
lean_dec(x_553);
if (x_556 == 0)
{
lean_object* x_557; 
lean_dec(x_555);
lean_dec(x_552);
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_550)) {
 x_557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_557 = x_550;
}
lean_ctor_set(x_557, 0, x_548);
lean_ctor_set(x_557, 1, x_549);
return x_557;
}
else
{
lean_object* x_558; 
x_558 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16___rarg(x_10, x_552, x_16, x_555);
lean_dec(x_552);
lean_dec(x_10);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; 
lean_dec(x_348);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_550)) {
 x_559 = lean_alloc_ctor(0, 2, 0);
} else {
 x_559 = x_550;
}
lean_ctor_set(x_559, 0, x_548);
lean_ctor_set(x_559, 1, x_549);
return x_559;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_550);
x_560 = lean_ctor_get(x_558, 0);
lean_inc(x_560);
lean_dec(x_558);
x_561 = l_Array_append___rarg(x_14, x_348);
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
lean_dec(x_560);
x_1 = x_561;
x_2 = x_562;
x_3 = x_548;
x_8 = x_549;
goto _start;
}
}
}
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_564 = lean_ctor_get(x_441, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_441, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_566 = x_441;
} else {
 lean_dec_ref(x_441);
 x_566 = lean_box(0);
}
if (lean_is_scalar(x_566)) {
 x_567 = lean_alloc_ctor(1, 2, 0);
} else {
 x_567 = x_566;
}
lean_ctor_set(x_567, 0, x_564);
lean_ctor_set(x_567, 1, x_565);
return x_567;
}
}
}
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint8_t x_575; 
x_568 = lean_ctor_get(x_20, 0);
x_569 = lean_ctor_get(x_20, 1);
lean_inc(x_569);
lean_inc(x_568);
lean_dec(x_20);
x_570 = lean_ctor_get(x_568, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_568, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_572 = x_568;
} else {
 lean_dec_ref(x_568);
 x_572 = lean_box(0);
}
x_573 = lean_ctor_get(x_17, 0);
lean_inc(x_573);
x_574 = lean_box(3);
x_575 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_573, x_574);
lean_dec(x_573);
if (x_575 == 0)
{
lean_dec(x_17);
switch (lean_obj_tag(x_570)) {
case 0:
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; 
x_576 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_577 = x_572;
}
lean_ctor_set(x_577, 0, x_570);
lean_ctor_set(x_577, 1, x_576);
x_578 = lean_array_get_size(x_10);
x_579 = lean_unsigned_to_nat(1u);
x_580 = lean_nat_sub(x_578, x_579);
x_581 = lean_nat_dec_lt(x_16, x_578);
lean_dec(x_578);
if (x_581 == 0)
{
lean_object* x_582; 
lean_dec(x_580);
lean_dec(x_577);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_3);
lean_ctor_set(x_582, 1, x_569);
return x_582;
}
else
{
lean_object* x_583; 
x_583 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__1___rarg(x_10, x_577, x_16, x_580);
lean_dec(x_577);
lean_dec(x_10);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; 
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_584, 0, x_3);
lean_ctor_set(x_584, 1, x_569);
return x_584;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_583, 0);
lean_inc(x_585);
lean_dec(x_583);
x_586 = l_Array_append___rarg(x_14, x_571);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
lean_dec(x_585);
x_1 = x_586;
x_2 = x_587;
x_8 = x_569;
goto _start;
}
}
}
case 1:
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; 
x_589 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_572;
}
lean_ctor_set(x_590, 0, x_570);
lean_ctor_set(x_590, 1, x_589);
x_591 = lean_array_get_size(x_10);
x_592 = lean_unsigned_to_nat(1u);
x_593 = lean_nat_sub(x_591, x_592);
x_594 = lean_nat_dec_lt(x_16, x_591);
lean_dec(x_591);
if (x_594 == 0)
{
lean_object* x_595; 
lean_dec(x_593);
lean_dec(x_590);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_595, 0, x_3);
lean_ctor_set(x_595, 1, x_569);
return x_595;
}
else
{
lean_object* x_596; 
x_596 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__2___rarg(x_10, x_590, x_16, x_593);
lean_dec(x_590);
lean_dec(x_10);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; 
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_597 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_597, 0, x_3);
lean_ctor_set(x_597, 1, x_569);
return x_597;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_596, 0);
lean_inc(x_598);
lean_dec(x_596);
x_599 = l_Array_append___rarg(x_14, x_571);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec(x_598);
x_1 = x_599;
x_2 = x_600;
x_8 = x_569;
goto _start;
}
}
}
case 2:
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; 
x_602 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_603 = x_572;
}
lean_ctor_set(x_603, 0, x_570);
lean_ctor_set(x_603, 1, x_602);
x_604 = lean_array_get_size(x_10);
x_605 = lean_unsigned_to_nat(1u);
x_606 = lean_nat_sub(x_604, x_605);
x_607 = lean_nat_dec_lt(x_16, x_604);
lean_dec(x_604);
if (x_607 == 0)
{
lean_object* x_608; 
lean_dec(x_606);
lean_dec(x_603);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_608 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_608, 0, x_3);
lean_ctor_set(x_608, 1, x_569);
return x_608;
}
else
{
lean_object* x_609; 
x_609 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__3___rarg(x_10, x_603, x_16, x_606);
lean_dec(x_603);
lean_dec(x_10);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; 
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_3);
lean_ctor_set(x_610, 1, x_569);
return x_610;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_611 = lean_ctor_get(x_609, 0);
lean_inc(x_611);
lean_dec(x_609);
x_612 = l_Array_append___rarg(x_14, x_571);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_1 = x_612;
x_2 = x_613;
x_8 = x_569;
goto _start;
}
}
}
case 3:
{
lean_object* x_615; 
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_3);
lean_ctor_set(x_615, 1, x_569);
return x_615;
}
case 4:
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; uint8_t x_621; 
x_616 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_617 = lean_alloc_ctor(0, 2, 0);
} else {
 x_617 = x_572;
}
lean_ctor_set(x_617, 0, x_570);
lean_ctor_set(x_617, 1, x_616);
x_618 = lean_array_get_size(x_10);
x_619 = lean_unsigned_to_nat(1u);
x_620 = lean_nat_sub(x_618, x_619);
x_621 = lean_nat_dec_lt(x_16, x_618);
lean_dec(x_618);
if (x_621 == 0)
{
lean_object* x_622; 
lean_dec(x_620);
lean_dec(x_617);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_622 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_622, 0, x_3);
lean_ctor_set(x_622, 1, x_569);
return x_622;
}
else
{
lean_object* x_623; 
x_623 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__4___rarg(x_10, x_617, x_16, x_620);
lean_dec(x_617);
lean_dec(x_10);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; 
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_624 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_624, 0, x_3);
lean_ctor_set(x_624, 1, x_569);
return x_624;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_625 = lean_ctor_get(x_623, 0);
lean_inc(x_625);
lean_dec(x_623);
x_626 = l_Array_append___rarg(x_14, x_571);
x_627 = lean_ctor_get(x_625, 1);
lean_inc(x_627);
lean_dec(x_625);
x_1 = x_626;
x_2 = x_627;
x_8 = x_569;
goto _start;
}
}
}
case 5:
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; 
x_629 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_630 = lean_alloc_ctor(0, 2, 0);
} else {
 x_630 = x_572;
}
lean_ctor_set(x_630, 0, x_570);
lean_ctor_set(x_630, 1, x_629);
x_631 = lean_array_get_size(x_10);
x_632 = lean_unsigned_to_nat(1u);
x_633 = lean_nat_sub(x_631, x_632);
x_634 = lean_nat_dec_lt(x_16, x_631);
lean_dec(x_631);
if (x_634 == 0)
{
lean_object* x_635; 
lean_dec(x_633);
lean_dec(x_630);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_635 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_635, 0, x_3);
lean_ctor_set(x_635, 1, x_569);
return x_635;
}
else
{
lean_object* x_636; 
lean_inc(x_633);
x_636 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__5___rarg(x_10, x_630, x_16, x_633);
lean_dec(x_630);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; lean_object* x_638; 
lean_dec(x_571);
x_637 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_638 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__6___rarg(x_10, x_637, x_16, x_633);
lean_dec(x_10);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_3);
lean_ctor_set(x_639, 1, x_569);
return x_639;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_640 = lean_ctor_get(x_638, 0);
lean_inc(x_640);
lean_dec(x_638);
x_641 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_642 = l_Array_append___rarg(x_14, x_641);
x_643 = lean_ctor_get(x_640, 1);
lean_inc(x_643);
lean_dec(x_640);
x_1 = x_642;
x_2 = x_643;
x_8 = x_569;
goto _start;
}
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_645 = lean_ctor_get(x_636, 0);
lean_inc(x_645);
lean_dec(x_636);
lean_inc(x_14);
x_646 = l_Array_append___rarg(x_14, x_571);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec(x_645);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_648 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_646, x_647, x_3, x_4, x_5, x_6, x_7, x_569);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_651 = x_648;
} else {
 lean_dec_ref(x_648);
 x_651 = lean_box(0);
}
x_652 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_653 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7___rarg(x_10, x_652, x_16, x_633);
lean_dec(x_10);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_651)) {
 x_654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_654 = x_651;
}
lean_ctor_set(x_654, 0, x_649);
lean_ctor_set(x_654, 1, x_650);
return x_654;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_651);
x_655 = lean_ctor_get(x_653, 0);
lean_inc(x_655);
lean_dec(x_653);
x_656 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_657 = l_Array_append___rarg(x_14, x_656);
x_658 = lean_ctor_get(x_655, 1);
lean_inc(x_658);
lean_dec(x_655);
x_1 = x_657;
x_2 = x_658;
x_3 = x_649;
x_8 = x_650;
goto _start;
}
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_dec(x_633);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_660 = lean_ctor_get(x_648, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_648, 1);
lean_inc(x_661);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_662 = x_648;
} else {
 lean_dec_ref(x_648);
 x_662 = lean_box(0);
}
if (lean_is_scalar(x_662)) {
 x_663 = lean_alloc_ctor(1, 2, 0);
} else {
 x_663 = x_662;
}
lean_ctor_set(x_663, 0, x_660);
lean_ctor_set(x_663, 1, x_661);
return x_663;
}
}
}
}
default: 
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; 
x_664 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_665 = lean_alloc_ctor(0, 2, 0);
} else {
 x_665 = x_572;
}
lean_ctor_set(x_665, 0, x_570);
lean_ctor_set(x_665, 1, x_664);
x_666 = lean_array_get_size(x_10);
x_667 = lean_unsigned_to_nat(1u);
x_668 = lean_nat_sub(x_666, x_667);
x_669 = lean_nat_dec_lt(x_16, x_666);
lean_dec(x_666);
if (x_669 == 0)
{
lean_object* x_670; 
lean_dec(x_668);
lean_dec(x_665);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_670 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_670, 0, x_3);
lean_ctor_set(x_670, 1, x_569);
return x_670;
}
else
{
lean_object* x_671; 
x_671 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__8___rarg(x_10, x_665, x_16, x_668);
lean_dec(x_665);
lean_dec(x_10);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; 
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_672 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_672, 0, x_3);
lean_ctor_set(x_672, 1, x_569);
return x_672;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_671, 0);
lean_inc(x_673);
lean_dec(x_671);
x_674 = l_Array_append___rarg(x_14, x_571);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
lean_dec(x_673);
x_1 = x_674;
x_2 = x_675;
x_8 = x_569;
goto _start;
}
}
}
}
}
else
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_ctor_get(x_17, 1);
lean_inc(x_677);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_678 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_14, x_677, x_3, x_4, x_5, x_6, x_7, x_569);
if (lean_obj_tag(x_678) == 0)
{
switch (lean_obj_tag(x_570)) {
case 0:
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; uint8_t x_687; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 1);
lean_inc(x_680);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_681 = x_678;
} else {
 lean_dec_ref(x_678);
 x_681 = lean_box(0);
}
x_682 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_683 = lean_alloc_ctor(0, 2, 0);
} else {
 x_683 = x_572;
}
lean_ctor_set(x_683, 0, x_570);
lean_ctor_set(x_683, 1, x_682);
x_684 = lean_array_get_size(x_10);
x_685 = lean_unsigned_to_nat(1u);
x_686 = lean_nat_sub(x_684, x_685);
x_687 = lean_nat_dec_lt(x_16, x_684);
lean_dec(x_684);
if (x_687 == 0)
{
lean_object* x_688; 
lean_dec(x_686);
lean_dec(x_683);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_681)) {
 x_688 = lean_alloc_ctor(0, 2, 0);
} else {
 x_688 = x_681;
}
lean_ctor_set(x_688, 0, x_679);
lean_ctor_set(x_688, 1, x_680);
return x_688;
}
else
{
lean_object* x_689; 
x_689 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9___rarg(x_10, x_683, x_16, x_686);
lean_dec(x_683);
lean_dec(x_10);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; 
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_681)) {
 x_690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_690 = x_681;
}
lean_ctor_set(x_690, 0, x_679);
lean_ctor_set(x_690, 1, x_680);
return x_690;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_681);
x_691 = lean_ctor_get(x_689, 0);
lean_inc(x_691);
lean_dec(x_689);
x_692 = l_Array_append___rarg(x_14, x_571);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
lean_dec(x_691);
x_1 = x_692;
x_2 = x_693;
x_3 = x_679;
x_8 = x_680;
goto _start;
}
}
}
case 1:
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; uint8_t x_703; 
x_695 = lean_ctor_get(x_678, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_678, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_697 = x_678;
} else {
 lean_dec_ref(x_678);
 x_697 = lean_box(0);
}
x_698 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_699 = x_572;
}
lean_ctor_set(x_699, 0, x_570);
lean_ctor_set(x_699, 1, x_698);
x_700 = lean_array_get_size(x_10);
x_701 = lean_unsigned_to_nat(1u);
x_702 = lean_nat_sub(x_700, x_701);
x_703 = lean_nat_dec_lt(x_16, x_700);
lean_dec(x_700);
if (x_703 == 0)
{
lean_object* x_704; 
lean_dec(x_702);
lean_dec(x_699);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_697)) {
 x_704 = lean_alloc_ctor(0, 2, 0);
} else {
 x_704 = x_697;
}
lean_ctor_set(x_704, 0, x_695);
lean_ctor_set(x_704, 1, x_696);
return x_704;
}
else
{
lean_object* x_705; 
x_705 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10___rarg(x_10, x_699, x_16, x_702);
lean_dec(x_699);
lean_dec(x_10);
if (lean_obj_tag(x_705) == 0)
{
lean_object* x_706; 
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_697)) {
 x_706 = lean_alloc_ctor(0, 2, 0);
} else {
 x_706 = x_697;
}
lean_ctor_set(x_706, 0, x_695);
lean_ctor_set(x_706, 1, x_696);
return x_706;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec(x_697);
x_707 = lean_ctor_get(x_705, 0);
lean_inc(x_707);
lean_dec(x_705);
x_708 = l_Array_append___rarg(x_14, x_571);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
lean_dec(x_707);
x_1 = x_708;
x_2 = x_709;
x_3 = x_695;
x_8 = x_696;
goto _start;
}
}
}
case 2:
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; uint8_t x_719; 
x_711 = lean_ctor_get(x_678, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_678, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_713 = x_678;
} else {
 lean_dec_ref(x_678);
 x_713 = lean_box(0);
}
x_714 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_715 = lean_alloc_ctor(0, 2, 0);
} else {
 x_715 = x_572;
}
lean_ctor_set(x_715, 0, x_570);
lean_ctor_set(x_715, 1, x_714);
x_716 = lean_array_get_size(x_10);
x_717 = lean_unsigned_to_nat(1u);
x_718 = lean_nat_sub(x_716, x_717);
x_719 = lean_nat_dec_lt(x_16, x_716);
lean_dec(x_716);
if (x_719 == 0)
{
lean_object* x_720; 
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_713)) {
 x_720 = lean_alloc_ctor(0, 2, 0);
} else {
 x_720 = x_713;
}
lean_ctor_set(x_720, 0, x_711);
lean_ctor_set(x_720, 1, x_712);
return x_720;
}
else
{
lean_object* x_721; 
x_721 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11___rarg(x_10, x_715, x_16, x_718);
lean_dec(x_715);
lean_dec(x_10);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; 
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_713)) {
 x_722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_722 = x_713;
}
lean_ctor_set(x_722, 0, x_711);
lean_ctor_set(x_722, 1, x_712);
return x_722;
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; 
lean_dec(x_713);
x_723 = lean_ctor_get(x_721, 0);
lean_inc(x_723);
lean_dec(x_721);
x_724 = l_Array_append___rarg(x_14, x_571);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
x_1 = x_724;
x_2 = x_725;
x_3 = x_711;
x_8 = x_712;
goto _start;
}
}
}
case 3:
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_727 = lean_ctor_get(x_678, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_678, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_729 = x_678;
} else {
 lean_dec_ref(x_678);
 x_729 = lean_box(0);
}
if (lean_is_scalar(x_729)) {
 x_730 = lean_alloc_ctor(0, 2, 0);
} else {
 x_730 = x_729;
}
lean_ctor_set(x_730, 0, x_727);
lean_ctor_set(x_730, 1, x_728);
return x_730;
}
case 4:
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; uint8_t x_739; 
x_731 = lean_ctor_get(x_678, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_678, 1);
lean_inc(x_732);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_733 = x_678;
} else {
 lean_dec_ref(x_678);
 x_733 = lean_box(0);
}
x_734 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_735 = x_572;
}
lean_ctor_set(x_735, 0, x_570);
lean_ctor_set(x_735, 1, x_734);
x_736 = lean_array_get_size(x_10);
x_737 = lean_unsigned_to_nat(1u);
x_738 = lean_nat_sub(x_736, x_737);
x_739 = lean_nat_dec_lt(x_16, x_736);
lean_dec(x_736);
if (x_739 == 0)
{
lean_object* x_740; 
lean_dec(x_738);
lean_dec(x_735);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_733)) {
 x_740 = lean_alloc_ctor(0, 2, 0);
} else {
 x_740 = x_733;
}
lean_ctor_set(x_740, 0, x_731);
lean_ctor_set(x_740, 1, x_732);
return x_740;
}
else
{
lean_object* x_741; 
x_741 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12___rarg(x_10, x_735, x_16, x_738);
lean_dec(x_735);
lean_dec(x_10);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; 
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_733)) {
 x_742 = lean_alloc_ctor(0, 2, 0);
} else {
 x_742 = x_733;
}
lean_ctor_set(x_742, 0, x_731);
lean_ctor_set(x_742, 1, x_732);
return x_742;
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_733);
x_743 = lean_ctor_get(x_741, 0);
lean_inc(x_743);
lean_dec(x_741);
x_744 = l_Array_append___rarg(x_14, x_571);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_1 = x_744;
x_2 = x_745;
x_3 = x_731;
x_8 = x_732;
goto _start;
}
}
}
case 5:
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; uint8_t x_755; 
x_747 = lean_ctor_get(x_678, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_678, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_749 = x_678;
} else {
 lean_dec_ref(x_678);
 x_749 = lean_box(0);
}
x_750 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_751 = lean_alloc_ctor(0, 2, 0);
} else {
 x_751 = x_572;
}
lean_ctor_set(x_751, 0, x_570);
lean_ctor_set(x_751, 1, x_750);
x_752 = lean_array_get_size(x_10);
x_753 = lean_unsigned_to_nat(1u);
x_754 = lean_nat_sub(x_752, x_753);
x_755 = lean_nat_dec_lt(x_16, x_752);
lean_dec(x_752);
if (x_755 == 0)
{
lean_object* x_756; 
lean_dec(x_754);
lean_dec(x_751);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_749)) {
 x_756 = lean_alloc_ctor(0, 2, 0);
} else {
 x_756 = x_749;
}
lean_ctor_set(x_756, 0, x_747);
lean_ctor_set(x_756, 1, x_748);
return x_756;
}
else
{
lean_object* x_757; 
lean_inc(x_754);
x_757 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13___rarg(x_10, x_751, x_16, x_754);
lean_dec(x_751);
if (lean_obj_tag(x_757) == 0)
{
lean_object* x_758; lean_object* x_759; 
lean_dec(x_571);
x_758 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_759 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14___rarg(x_10, x_758, x_16, x_754);
lean_dec(x_10);
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_760; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_749)) {
 x_760 = lean_alloc_ctor(0, 2, 0);
} else {
 x_760 = x_749;
}
lean_ctor_set(x_760, 0, x_747);
lean_ctor_set(x_760, 1, x_748);
return x_760;
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_749);
x_761 = lean_ctor_get(x_759, 0);
lean_inc(x_761);
lean_dec(x_759);
x_762 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_763 = l_Array_append___rarg(x_14, x_762);
x_764 = lean_ctor_get(x_761, 1);
lean_inc(x_764);
lean_dec(x_761);
x_1 = x_763;
x_2 = x_764;
x_3 = x_747;
x_8 = x_748;
goto _start;
}
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_749);
x_766 = lean_ctor_get(x_757, 0);
lean_inc(x_766);
lean_dec(x_757);
lean_inc(x_14);
x_767 = l_Array_append___rarg(x_14, x_571);
x_768 = lean_ctor_get(x_766, 1);
lean_inc(x_768);
lean_dec(x_766);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_769 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_767, x_768, x_747, x_4, x_5, x_6, x_7, x_748);
if (lean_obj_tag(x_769) == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_770 = lean_ctor_get(x_769, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_769, 1);
lean_inc(x_771);
if (lean_is_exclusive(x_769)) {
 lean_ctor_release(x_769, 0);
 lean_ctor_release(x_769, 1);
 x_772 = x_769;
} else {
 lean_dec_ref(x_769);
 x_772 = lean_box(0);
}
x_773 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_774 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15___rarg(x_10, x_773, x_16, x_754);
lean_dec(x_10);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_772)) {
 x_775 = lean_alloc_ctor(0, 2, 0);
} else {
 x_775 = x_772;
}
lean_ctor_set(x_775, 0, x_770);
lean_ctor_set(x_775, 1, x_771);
return x_775;
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; 
lean_dec(x_772);
x_776 = lean_ctor_get(x_774, 0);
lean_inc(x_776);
lean_dec(x_774);
x_777 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_778 = l_Array_append___rarg(x_14, x_777);
x_779 = lean_ctor_get(x_776, 1);
lean_inc(x_779);
lean_dec(x_776);
x_1 = x_778;
x_2 = x_779;
x_3 = x_770;
x_8 = x_771;
goto _start;
}
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
lean_dec(x_754);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_781 = lean_ctor_get(x_769, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_769, 1);
lean_inc(x_782);
if (lean_is_exclusive(x_769)) {
 lean_ctor_release(x_769, 0);
 lean_ctor_release(x_769, 1);
 x_783 = x_769;
} else {
 lean_dec_ref(x_769);
 x_783 = lean_box(0);
}
if (lean_is_scalar(x_783)) {
 x_784 = lean_alloc_ctor(1, 2, 0);
} else {
 x_784 = x_783;
}
lean_ctor_set(x_784, 0, x_781);
lean_ctor_set(x_784, 1, x_782);
return x_784;
}
}
}
}
default: 
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; uint8_t x_793; 
x_785 = lean_ctor_get(x_678, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_678, 1);
lean_inc(x_786);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_787 = x_678;
} else {
 lean_dec_ref(x_678);
 x_787 = lean_box(0);
}
x_788 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_572)) {
 x_789 = lean_alloc_ctor(0, 2, 0);
} else {
 x_789 = x_572;
}
lean_ctor_set(x_789, 0, x_570);
lean_ctor_set(x_789, 1, x_788);
x_790 = lean_array_get_size(x_10);
x_791 = lean_unsigned_to_nat(1u);
x_792 = lean_nat_sub(x_790, x_791);
x_793 = lean_nat_dec_lt(x_16, x_790);
lean_dec(x_790);
if (x_793 == 0)
{
lean_object* x_794; 
lean_dec(x_792);
lean_dec(x_789);
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_787)) {
 x_794 = lean_alloc_ctor(0, 2, 0);
} else {
 x_794 = x_787;
}
lean_ctor_set(x_794, 0, x_785);
lean_ctor_set(x_794, 1, x_786);
return x_794;
}
else
{
lean_object* x_795; 
x_795 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16___rarg(x_10, x_789, x_16, x_792);
lean_dec(x_789);
lean_dec(x_10);
if (lean_obj_tag(x_795) == 0)
{
lean_object* x_796; 
lean_dec(x_571);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_787)) {
 x_796 = lean_alloc_ctor(0, 2, 0);
} else {
 x_796 = x_787;
}
lean_ctor_set(x_796, 0, x_785);
lean_ctor_set(x_796, 1, x_786);
return x_796;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
lean_dec(x_787);
x_797 = lean_ctor_get(x_795, 0);
lean_inc(x_797);
lean_dec(x_795);
x_798 = l_Array_append___rarg(x_14, x_571);
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
lean_dec(x_797);
x_1 = x_798;
x_2 = x_799;
x_3 = x_785;
x_8 = x_786;
goto _start;
}
}
}
}
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_801 = lean_ctor_get(x_678, 0);
lean_inc(x_801);
x_802 = lean_ctor_get(x_678, 1);
lean_inc(x_802);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_803 = x_678;
} else {
 lean_dec_ref(x_678);
 x_803 = lean_box(0);
}
if (lean_is_scalar(x_803)) {
 x_804 = lean_alloc_ctor(1, 2, 0);
} else {
 x_804 = x_803;
}
lean_ctor_set(x_804, 0, x_801);
lean_ctor_set(x_804, 1, x_802);
return x_804;
}
}
}
}
else
{
uint8_t x_805; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_805 = !lean_is_exclusive(x_20);
if (x_805 == 0)
{
return x_20;
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_806 = lean_ctor_get(x_20, 0);
x_807 = lean_ctor_get(x_20, 1);
lean_inc(x_807);
lean_inc(x_806);
lean_dec(x_20);
x_808 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_808, 0, x_806);
lean_ctor_set(x_808, 1, x_807);
return x_808;
}
}
}
else
{
lean_object* x_809; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_809 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_809, 0, x_3);
lean_ctor_set(x_809, 1, x_8);
return x_809;
}
}
else
{
lean_object* x_810; lean_object* x_811; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_810 = l_Array_append___rarg(x_3, x_9);
x_811 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_811, 0, x_810);
lean_ctor_set(x_811, 1, x_8);
return x_811;
}
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch_process(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatch_process___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__6___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__7___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__8___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__9___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__10___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__11___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__12___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__13___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__14___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__15___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getMatch_process___spec__16___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_14, 1);
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = l_Lean_Meta_DiscrTree_instBEqKey;
x_26 = l_Lean_Meta_DiscrTree_instHashableKey;
x_27 = l_Std_PersistentHashMap_find_x3f___rarg(x_25, x_26, x_1, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_14, 0, x_8);
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_14);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_24, x_28, x_8, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_dec(x_15);
x_40 = l_Lean_Meta_DiscrTree_instBEqKey;
x_41 = l_Lean_Meta_DiscrTree_instHashableKey;
x_42 = l_Std_PersistentHashMap_find_x3f___rarg(x_40, x_41, x_1, x_16);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_39, x_44, x_8, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_52 = x_45;
} else {
 lean_dec_ref(x_45);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_58 = lean_ctor_get_uint8(x_10, 0);
x_59 = lean_ctor_get_uint8(x_10, 1);
x_60 = lean_ctor_get_uint8(x_10, 2);
x_61 = lean_ctor_get_uint8(x_10, 3);
x_62 = lean_ctor_get_uint8(x_10, 4);
x_63 = lean_ctor_get_uint8(x_10, 6);
x_64 = lean_ctor_get_uint8(x_10, 7);
x_65 = lean_ctor_get_uint8(x_10, 8);
x_66 = lean_ctor_get_uint8(x_10, 9);
x_67 = lean_ctor_get_uint8(x_10, 10);
lean_dec(x_10);
x_68 = 2;
x_69 = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(x_69, 0, x_58);
lean_ctor_set_uint8(x_69, 1, x_59);
lean_ctor_set_uint8(x_69, 2, x_60);
lean_ctor_set_uint8(x_69, 3, x_61);
lean_ctor_set_uint8(x_69, 4, x_62);
lean_ctor_set_uint8(x_69, 5, x_68);
lean_ctor_set_uint8(x_69, 6, x_63);
lean_ctor_set_uint8(x_69, 7, x_64);
lean_ctor_set_uint8(x_69, 8, x_65);
lean_ctor_set_uint8(x_69, 9, x_66);
lean_ctor_set_uint8(x_69, 10, x_67);
lean_ctor_set(x_3, 0, x_69);
x_70 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_71 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_70, x_70, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 3)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_72);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_8);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
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
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_80 = l_Lean_Meta_DiscrTree_instBEqKey;
x_81 = l_Lean_Meta_DiscrTree_instHashableKey;
x_82 = l_Std_PersistentHashMap_find_x3f___rarg(x_80, x_81, x_1, x_73);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
lean_dec(x_79);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_8);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_79, x_84, x_8, x_3, x_4, x_5, x_6, x_77);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = lean_ctor_get(x_71, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_71, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_96 = x_71;
} else {
 lean_dec_ref(x_71);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; 
x_98 = lean_ctor_get(x_3, 0);
x_99 = lean_ctor_get(x_3, 1);
x_100 = lean_ctor_get(x_3, 2);
x_101 = lean_ctor_get(x_3, 3);
x_102 = lean_ctor_get(x_3, 4);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_3);
x_103 = lean_ctor_get_uint8(x_98, 0);
x_104 = lean_ctor_get_uint8(x_98, 1);
x_105 = lean_ctor_get_uint8(x_98, 2);
x_106 = lean_ctor_get_uint8(x_98, 3);
x_107 = lean_ctor_get_uint8(x_98, 4);
x_108 = lean_ctor_get_uint8(x_98, 6);
x_109 = lean_ctor_get_uint8(x_98, 7);
x_110 = lean_ctor_get_uint8(x_98, 8);
x_111 = lean_ctor_get_uint8(x_98, 9);
x_112 = lean_ctor_get_uint8(x_98, 10);
if (lean_is_exclusive(x_98)) {
 x_113 = x_98;
} else {
 lean_dec_ref(x_98);
 x_113 = lean_box(0);
}
x_114 = 2;
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 0, 11);
} else {
 x_115 = x_113;
}
lean_ctor_set_uint8(x_115, 0, x_103);
lean_ctor_set_uint8(x_115, 1, x_104);
lean_ctor_set_uint8(x_115, 2, x_105);
lean_ctor_set_uint8(x_115, 3, x_106);
lean_ctor_set_uint8(x_115, 4, x_107);
lean_ctor_set_uint8(x_115, 5, x_114);
lean_ctor_set_uint8(x_115, 6, x_108);
lean_ctor_set_uint8(x_115, 7, x_109);
lean_ctor_set_uint8(x_115, 8, x_110);
lean_ctor_set_uint8(x_115, 9, x_111);
lean_ctor_set_uint8(x_115, 10, x_112);
x_116 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_99);
lean_ctor_set(x_116, 2, x_100);
lean_ctor_set(x_116, 3, x_101);
lean_ctor_set(x_116, 4, x_102);
x_117 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_116);
x_118 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_117, x_117, x_116, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 3)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_119);
lean_dec(x_116);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_122 = x_118;
} else {
 lean_dec_ref(x_118);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_8);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
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
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
lean_dec(x_119);
x_127 = l_Lean_Meta_DiscrTree_instBEqKey;
x_128 = l_Lean_Meta_DiscrTree_instHashableKey;
x_129 = l_Std_PersistentHashMap_find_x3f___rarg(x_127, x_128, x_1, x_120);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
lean_dec(x_126);
lean_dec(x_116);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_125)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_125;
}
lean_ctor_set(x_130, 0, x_8);
lean_ctor_set(x_130, 1, x_124);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Lean_Meta_DiscrTree_getMatch_process___rarg(x_126, x_131, x_8, x_116, x_4, x_5, x_6, x_124);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
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
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_132, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_139 = x_132;
} else {
 lean_dec_ref(x_132);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_116);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_141 = lean_ctor_get(x_118, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_118, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_143 = x_118;
} else {
 lean_dec_ref(x_118);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatch___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify_process_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_2(x_4, x_12, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify_process_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getUnify_process_match__1___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify_process_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_DiscrTree_getUnify_process_match__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
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
x_20 = x_3 + x_19;
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__10___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__11___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__12___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__13___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__14___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__16___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_4 == x_5;
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
x_22 = x_4 + x_21;
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__16___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify_process___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_23 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__16___rarg(x_2, x_13, x_14, x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_29 = l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___spec__1(x_2);
x_30 = lean_array_pop(x_2);
x_31 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_32 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_29, x_31, x_31, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
switch (lean_obj_tag(x_34)) {
case 0:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_33, 1);
x_40 = lean_ctor_get(x_33, 0);
lean_dec(x_40);
x_41 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_42 = lean_array_get(x_41, x_26, x_10);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_box(3);
x_45 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_42);
x_46 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_46);
x_47 = lean_array_get_size(x_26);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_47, x_48);
x_50 = lean_nat_dec_lt(x_10, x_47);
lean_dec(x_47);
if (x_50 == 0)
{
lean_dec(x_49);
lean_dec(x_33);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_51; 
x_51 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(x_26, x_33, x_10, x_49);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_51) == 0)
{
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_free_object(x_32);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Array_append___rarg(x_30, x_39);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_1 = x_10;
x_2 = x_53;
x_3 = x_54;
x_9 = x_36;
goto _start;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_free_object(x_32);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_57 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_56, x_4, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
x_61 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_61);
x_62 = lean_array_get_size(x_26);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_62, x_63);
x_65 = lean_nat_dec_lt(x_10, x_62);
lean_dec(x_62);
if (x_65 == 0)
{
lean_dec(x_64);
lean_dec(x_33);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_57;
}
else
{
lean_object* x_66; 
x_66 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_26, x_33, x_10, x_64);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_66) == 0)
{
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_57;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_57);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Array_append___rarg(x_30, x_39);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_1 = x_10;
x_2 = x_68;
x_3 = x_69;
x_4 = x_59;
x_9 = x_60;
goto _start;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_57, 0);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_57);
x_73 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_73);
x_74 = lean_array_get_size(x_26);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_74, x_75);
x_77 = lean_nat_dec_lt(x_10, x_74);
lean_dec(x_74);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_76);
lean_dec(x_33);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_72);
return x_78;
}
else
{
lean_object* x_79; 
x_79 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_26, x_33, x_10, x_76);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_72);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Array_append___rarg(x_30, x_39);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_1 = x_10;
x_2 = x_82;
x_3 = x_83;
x_4 = x_71;
x_9 = x_72;
goto _start;
}
}
}
}
else
{
uint8_t x_85; 
lean_free_object(x_33);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_57);
if (x_85 == 0)
{
return x_57;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_57, 0);
x_87 = lean_ctor_get(x_57, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_57);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_89 = lean_ctor_get(x_33, 1);
lean_inc(x_89);
lean_dec(x_33);
x_90 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_91 = lean_array_get(x_90, x_26, x_10);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_box(3);
x_94 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_92, x_93);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_91);
x_95 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_34);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_get_size(x_26);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_sub(x_97, x_98);
x_100 = lean_nat_dec_lt(x_10, x_97);
lean_dec(x_97);
if (x_100 == 0)
{
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_89);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_101; 
x_101 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(x_26, x_96, x_10, x_99);
lean_dec(x_96);
lean_dec(x_26);
if (lean_obj_tag(x_101) == 0)
{
lean_dec(x_89);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_32);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Array_append___rarg(x_30, x_89);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_1 = x_10;
x_2 = x_103;
x_3 = x_104;
x_9 = x_36;
goto _start;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_free_object(x_32);
x_106 = lean_ctor_get(x_91, 1);
lean_inc(x_106);
lean_dec(x_91);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_107 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_106, x_4, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_34);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_array_get_size(x_26);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_sub(x_113, x_114);
x_116 = lean_nat_dec_lt(x_10, x_113);
lean_dec(x_113);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_89);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_110)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_110;
}
lean_ctor_set(x_117, 0, x_108);
lean_ctor_set(x_117, 1, x_109);
return x_117;
}
else
{
lean_object* x_118; 
x_118 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_26, x_112, x_10, x_115);
lean_dec(x_112);
lean_dec(x_26);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
lean_dec(x_89);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_110)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_110;
}
lean_ctor_set(x_119, 0, x_108);
lean_ctor_set(x_119, 1, x_109);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_110);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
x_121 = l_Array_append___rarg(x_30, x_89);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_1 = x_10;
x_2 = x_121;
x_3 = x_122;
x_4 = x_108;
x_9 = x_109;
goto _start;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_89);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_124 = lean_ctor_get(x_107, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_107, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_126 = x_107;
} else {
 lean_dec_ref(x_107);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_128 = lean_ctor_get(x_32, 1);
lean_inc(x_128);
lean_dec(x_32);
x_129 = lean_ctor_get(x_33, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_130 = x_33;
} else {
 lean_dec_ref(x_33);
 x_130 = lean_box(0);
}
x_131 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_132 = lean_array_get(x_131, x_26, x_10);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_box(3);
x_135 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_133, x_134);
lean_dec(x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec(x_132);
x_136 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_130)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_130;
}
lean_ctor_set(x_137, 0, x_34);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_array_get_size(x_26);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_sub(x_138, x_139);
x_141 = lean_nat_dec_lt(x_10, x_138);
lean_dec(x_138);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_140);
lean_dec(x_137);
lean_dec(x_129);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_4);
lean_ctor_set(x_142, 1, x_128);
return x_142;
}
else
{
lean_object* x_143; 
x_143 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(x_26, x_137, x_10, x_140);
lean_dec(x_137);
lean_dec(x_26);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
lean_dec(x_129);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_4);
lean_ctor_set(x_144, 1, x_128);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Array_append___rarg(x_30, x_129);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_1 = x_10;
x_2 = x_146;
x_3 = x_147;
x_9 = x_128;
goto _start;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_132, 1);
lean_inc(x_149);
lean_dec(x_132);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_150 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_149, x_4, x_5, x_6, x_7, x_8, x_128);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_130)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_130;
}
lean_ctor_set(x_155, 0, x_34);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_array_get_size(x_26);
x_157 = lean_unsigned_to_nat(1u);
x_158 = lean_nat_sub(x_156, x_157);
x_159 = lean_nat_dec_lt(x_10, x_156);
lean_dec(x_156);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_158);
lean_dec(x_155);
lean_dec(x_129);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_153)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_153;
}
lean_ctor_set(x_160, 0, x_151);
lean_ctor_set(x_160, 1, x_152);
return x_160;
}
else
{
lean_object* x_161; 
x_161 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_26, x_155, x_10, x_158);
lean_dec(x_155);
lean_dec(x_26);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
lean_dec(x_129);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_153)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_153;
}
lean_ctor_set(x_162, 0, x_151);
lean_ctor_set(x_162, 1, x_152);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_153);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Array_append___rarg(x_30, x_129);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_1 = x_10;
x_2 = x_164;
x_3 = x_165;
x_4 = x_151;
x_9 = x_152;
goto _start;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_167 = lean_ctor_get(x_150, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_150, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_169 = x_150;
} else {
 lean_dec_ref(x_150);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
}
case 1:
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_32);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = lean_ctor_get(x_32, 1);
x_173 = lean_ctor_get(x_32, 0);
lean_dec(x_173);
x_174 = !lean_is_exclusive(x_33);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_175 = lean_ctor_get(x_33, 1);
x_176 = lean_ctor_get(x_33, 0);
lean_dec(x_176);
x_177 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_178 = lean_array_get(x_177, x_26, x_10);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_box(3);
x_181 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_179, x_180);
lean_dec(x_179);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
lean_dec(x_178);
x_182 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_182);
x_183 = lean_array_get_size(x_26);
x_184 = lean_unsigned_to_nat(1u);
x_185 = lean_nat_sub(x_183, x_184);
x_186 = lean_nat_dec_lt(x_10, x_183);
lean_dec(x_183);
if (x_186 == 0)
{
lean_dec(x_185);
lean_dec(x_33);
lean_dec(x_175);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_187; 
x_187 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(x_26, x_33, x_10, x_185);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_187) == 0)
{
lean_dec(x_175);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_free_object(x_32);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec(x_187);
x_189 = l_Array_append___rarg(x_30, x_175);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_1 = x_10;
x_2 = x_189;
x_3 = x_190;
x_9 = x_172;
goto _start;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_free_object(x_32);
x_192 = lean_ctor_get(x_178, 1);
lean_inc(x_192);
lean_dec(x_178);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_193 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_192, x_4, x_5, x_6, x_7, x_8, x_172);
if (lean_obj_tag(x_193) == 0)
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
x_197 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_197);
x_198 = lean_array_get_size(x_26);
x_199 = lean_unsigned_to_nat(1u);
x_200 = lean_nat_sub(x_198, x_199);
x_201 = lean_nat_dec_lt(x_10, x_198);
lean_dec(x_198);
if (x_201 == 0)
{
lean_dec(x_200);
lean_dec(x_33);
lean_dec(x_175);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_193;
}
else
{
lean_object* x_202; 
x_202 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_26, x_33, x_10, x_200);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_202) == 0)
{
lean_dec(x_175);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_193;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_free_object(x_193);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec(x_202);
x_204 = l_Array_append___rarg(x_30, x_175);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_1 = x_10;
x_2 = x_204;
x_3 = x_205;
x_4 = x_195;
x_9 = x_196;
goto _start;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_207 = lean_ctor_get(x_193, 0);
x_208 = lean_ctor_get(x_193, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_193);
x_209 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_209);
x_210 = lean_array_get_size(x_26);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_nat_sub(x_210, x_211);
x_213 = lean_nat_dec_lt(x_10, x_210);
lean_dec(x_210);
if (x_213 == 0)
{
lean_object* x_214; 
lean_dec(x_212);
lean_dec(x_33);
lean_dec(x_175);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_207);
lean_ctor_set(x_214, 1, x_208);
return x_214;
}
else
{
lean_object* x_215; 
x_215 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_26, x_33, x_10, x_212);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; 
lean_dec(x_175);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_207);
lean_ctor_set(x_216, 1, x_208);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l_Array_append___rarg(x_30, x_175);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_1 = x_10;
x_2 = x_218;
x_3 = x_219;
x_4 = x_207;
x_9 = x_208;
goto _start;
}
}
}
}
else
{
uint8_t x_221; 
lean_free_object(x_33);
lean_dec(x_175);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_221 = !lean_is_exclusive(x_193);
if (x_221 == 0)
{
return x_193;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_193, 0);
x_223 = lean_ctor_get(x_193, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_193);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_225 = lean_ctor_get(x_33, 1);
lean_inc(x_225);
lean_dec(x_33);
x_226 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_227 = lean_array_get(x_226, x_26, x_10);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_box(3);
x_230 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_228, x_229);
lean_dec(x_228);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
lean_dec(x_227);
x_231 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_34);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_array_get_size(x_26);
x_234 = lean_unsigned_to_nat(1u);
x_235 = lean_nat_sub(x_233, x_234);
x_236 = lean_nat_dec_lt(x_10, x_233);
lean_dec(x_233);
if (x_236 == 0)
{
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_225);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_237; 
x_237 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(x_26, x_232, x_10, x_235);
lean_dec(x_232);
lean_dec(x_26);
if (lean_obj_tag(x_237) == 0)
{
lean_dec(x_225);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_free_object(x_32);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec(x_237);
x_239 = l_Array_append___rarg(x_30, x_225);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_1 = x_10;
x_2 = x_239;
x_3 = x_240;
x_9 = x_172;
goto _start;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_free_object(x_32);
x_242 = lean_ctor_get(x_227, 1);
lean_inc(x_242);
lean_dec(x_227);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_243 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_242, x_4, x_5, x_6, x_7, x_8, x_172);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
x_247 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_34);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_array_get_size(x_26);
x_250 = lean_unsigned_to_nat(1u);
x_251 = lean_nat_sub(x_249, x_250);
x_252 = lean_nat_dec_lt(x_10, x_249);
lean_dec(x_249);
if (x_252 == 0)
{
lean_object* x_253; 
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_225);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_246)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_246;
}
lean_ctor_set(x_253, 0, x_244);
lean_ctor_set(x_253, 1, x_245);
return x_253;
}
else
{
lean_object* x_254; 
x_254 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_26, x_248, x_10, x_251);
lean_dec(x_248);
lean_dec(x_26);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; 
lean_dec(x_225);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_246)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_246;
}
lean_ctor_set(x_255, 0, x_244);
lean_ctor_set(x_255, 1, x_245);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_246);
x_256 = lean_ctor_get(x_254, 0);
lean_inc(x_256);
lean_dec(x_254);
x_257 = l_Array_append___rarg(x_30, x_225);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_1 = x_10;
x_2 = x_257;
x_3 = x_258;
x_4 = x_244;
x_9 = x_245;
goto _start;
}
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_225);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_260 = lean_ctor_get(x_243, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_243, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_262 = x_243;
} else {
 lean_dec_ref(x_243);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_264 = lean_ctor_get(x_32, 1);
lean_inc(x_264);
lean_dec(x_32);
x_265 = lean_ctor_get(x_33, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_266 = x_33;
} else {
 lean_dec_ref(x_33);
 x_266 = lean_box(0);
}
x_267 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_268 = lean_array_get(x_267, x_26, x_10);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_box(3);
x_271 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_269, x_270);
lean_dec(x_269);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
lean_dec(x_268);
x_272 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_266)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_266;
}
lean_ctor_set(x_273, 0, x_34);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_array_get_size(x_26);
x_275 = lean_unsigned_to_nat(1u);
x_276 = lean_nat_sub(x_274, x_275);
x_277 = lean_nat_dec_lt(x_10, x_274);
lean_dec(x_274);
if (x_277 == 0)
{
lean_object* x_278; 
lean_dec(x_276);
lean_dec(x_273);
lean_dec(x_265);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_4);
lean_ctor_set(x_278, 1, x_264);
return x_278;
}
else
{
lean_object* x_279; 
x_279 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(x_26, x_273, x_10, x_276);
lean_dec(x_273);
lean_dec(x_26);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; 
lean_dec(x_265);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_4);
lean_ctor_set(x_280, 1, x_264);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_279, 0);
lean_inc(x_281);
lean_dec(x_279);
x_282 = l_Array_append___rarg(x_30, x_265);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_1 = x_10;
x_2 = x_282;
x_3 = x_283;
x_9 = x_264;
goto _start;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_268, 1);
lean_inc(x_285);
lean_dec(x_268);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_286 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_285, x_4, x_5, x_6, x_7, x_8, x_264);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
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
x_290 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_266)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_266;
}
lean_ctor_set(x_291, 0, x_34);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_array_get_size(x_26);
x_293 = lean_unsigned_to_nat(1u);
x_294 = lean_nat_sub(x_292, x_293);
x_295 = lean_nat_dec_lt(x_10, x_292);
lean_dec(x_292);
if (x_295 == 0)
{
lean_object* x_296; 
lean_dec(x_294);
lean_dec(x_291);
lean_dec(x_265);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_289)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_289;
}
lean_ctor_set(x_296, 0, x_287);
lean_ctor_set(x_296, 1, x_288);
return x_296;
}
else
{
lean_object* x_297; 
x_297 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_26, x_291, x_10, x_294);
lean_dec(x_291);
lean_dec(x_26);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; 
lean_dec(x_265);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_289)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_289;
}
lean_ctor_set(x_298, 0, x_287);
lean_ctor_set(x_298, 1, x_288);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_289);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
lean_dec(x_297);
x_300 = l_Array_append___rarg(x_30, x_265);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_1 = x_10;
x_2 = x_300;
x_3 = x_301;
x_4 = x_287;
x_9 = x_288;
goto _start;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_303 = lean_ctor_get(x_286, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_286, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_305 = x_286;
} else {
 lean_dec_ref(x_286);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
}
}
case 2:
{
uint8_t x_307; 
x_307 = !lean_is_exclusive(x_32);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_308 = lean_ctor_get(x_32, 1);
x_309 = lean_ctor_get(x_32, 0);
lean_dec(x_309);
x_310 = !lean_is_exclusive(x_33);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_311 = lean_ctor_get(x_33, 1);
x_312 = lean_ctor_get(x_33, 0);
lean_dec(x_312);
x_313 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_314 = lean_array_get(x_313, x_26, x_10);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_box(3);
x_317 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_315, x_316);
lean_dec(x_315);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
lean_dec(x_314);
x_318 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_318);
x_319 = lean_array_get_size(x_26);
x_320 = lean_unsigned_to_nat(1u);
x_321 = lean_nat_sub(x_319, x_320);
x_322 = lean_nat_dec_lt(x_10, x_319);
lean_dec(x_319);
if (x_322 == 0)
{
lean_dec(x_321);
lean_dec(x_33);
lean_dec(x_311);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_323; 
x_323 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(x_26, x_33, x_10, x_321);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_323) == 0)
{
lean_dec(x_311);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_free_object(x_32);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
lean_dec(x_323);
x_325 = l_Array_append___rarg(x_30, x_311);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_1 = x_10;
x_2 = x_325;
x_3 = x_326;
x_9 = x_308;
goto _start;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; 
lean_free_object(x_32);
x_328 = lean_ctor_get(x_314, 1);
lean_inc(x_328);
lean_dec(x_314);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_329 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_328, x_4, x_5, x_6, x_7, x_8, x_308);
if (lean_obj_tag(x_329) == 0)
{
uint8_t x_330; 
x_330 = !lean_is_exclusive(x_329);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_331 = lean_ctor_get(x_329, 0);
x_332 = lean_ctor_get(x_329, 1);
x_333 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_333);
x_334 = lean_array_get_size(x_26);
x_335 = lean_unsigned_to_nat(1u);
x_336 = lean_nat_sub(x_334, x_335);
x_337 = lean_nat_dec_lt(x_10, x_334);
lean_dec(x_334);
if (x_337 == 0)
{
lean_dec(x_336);
lean_dec(x_33);
lean_dec(x_311);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_329;
}
else
{
lean_object* x_338; 
x_338 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_26, x_33, x_10, x_336);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_338) == 0)
{
lean_dec(x_311);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_329;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_free_object(x_329);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec(x_338);
x_340 = l_Array_append___rarg(x_30, x_311);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_1 = x_10;
x_2 = x_340;
x_3 = x_341;
x_4 = x_331;
x_9 = x_332;
goto _start;
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_343 = lean_ctor_get(x_329, 0);
x_344 = lean_ctor_get(x_329, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_329);
x_345 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_345);
x_346 = lean_array_get_size(x_26);
x_347 = lean_unsigned_to_nat(1u);
x_348 = lean_nat_sub(x_346, x_347);
x_349 = lean_nat_dec_lt(x_10, x_346);
lean_dec(x_346);
if (x_349 == 0)
{
lean_object* x_350; 
lean_dec(x_348);
lean_dec(x_33);
lean_dec(x_311);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_343);
lean_ctor_set(x_350, 1, x_344);
return x_350;
}
else
{
lean_object* x_351; 
x_351 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_26, x_33, x_10, x_348);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; 
lean_dec(x_311);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_343);
lean_ctor_set(x_352, 1, x_344);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
lean_dec(x_351);
x_354 = l_Array_append___rarg(x_30, x_311);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_1 = x_10;
x_2 = x_354;
x_3 = x_355;
x_4 = x_343;
x_9 = x_344;
goto _start;
}
}
}
}
else
{
uint8_t x_357; 
lean_free_object(x_33);
lean_dec(x_311);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_357 = !lean_is_exclusive(x_329);
if (x_357 == 0)
{
return x_329;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_329, 0);
x_359 = lean_ctor_get(x_329, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_329);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
}
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_361 = lean_ctor_get(x_33, 1);
lean_inc(x_361);
lean_dec(x_33);
x_362 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_363 = lean_array_get(x_362, x_26, x_10);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_box(3);
x_366 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_364, x_365);
lean_dec(x_364);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
lean_dec(x_363);
x_367 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_34);
lean_ctor_set(x_368, 1, x_367);
x_369 = lean_array_get_size(x_26);
x_370 = lean_unsigned_to_nat(1u);
x_371 = lean_nat_sub(x_369, x_370);
x_372 = lean_nat_dec_lt(x_10, x_369);
lean_dec(x_369);
if (x_372 == 0)
{
lean_dec(x_371);
lean_dec(x_368);
lean_dec(x_361);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_373; 
x_373 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(x_26, x_368, x_10, x_371);
lean_dec(x_368);
lean_dec(x_26);
if (lean_obj_tag(x_373) == 0)
{
lean_dec(x_361);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_free_object(x_32);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
lean_dec(x_373);
x_375 = l_Array_append___rarg(x_30, x_361);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
x_1 = x_10;
x_2 = x_375;
x_3 = x_376;
x_9 = x_308;
goto _start;
}
}
}
else
{
lean_object* x_378; lean_object* x_379; 
lean_free_object(x_32);
x_378 = lean_ctor_get(x_363, 1);
lean_inc(x_378);
lean_dec(x_363);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_379 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_378, x_4, x_5, x_6, x_7, x_8, x_308);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_382 = x_379;
} else {
 lean_dec_ref(x_379);
 x_382 = lean_box(0);
}
x_383 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_34);
lean_ctor_set(x_384, 1, x_383);
x_385 = lean_array_get_size(x_26);
x_386 = lean_unsigned_to_nat(1u);
x_387 = lean_nat_sub(x_385, x_386);
x_388 = lean_nat_dec_lt(x_10, x_385);
lean_dec(x_385);
if (x_388 == 0)
{
lean_object* x_389; 
lean_dec(x_387);
lean_dec(x_384);
lean_dec(x_361);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_382)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_382;
}
lean_ctor_set(x_389, 0, x_380);
lean_ctor_set(x_389, 1, x_381);
return x_389;
}
else
{
lean_object* x_390; 
x_390 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_26, x_384, x_10, x_387);
lean_dec(x_384);
lean_dec(x_26);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; 
lean_dec(x_361);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_382)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_382;
}
lean_ctor_set(x_391, 0, x_380);
lean_ctor_set(x_391, 1, x_381);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_382);
x_392 = lean_ctor_get(x_390, 0);
lean_inc(x_392);
lean_dec(x_390);
x_393 = l_Array_append___rarg(x_30, x_361);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_1 = x_10;
x_2 = x_393;
x_3 = x_394;
x_4 = x_380;
x_9 = x_381;
goto _start;
}
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_361);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_396 = lean_ctor_get(x_379, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_379, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_398 = x_379;
} else {
 lean_dec_ref(x_379);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_400 = lean_ctor_get(x_32, 1);
lean_inc(x_400);
lean_dec(x_32);
x_401 = lean_ctor_get(x_33, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_402 = x_33;
} else {
 lean_dec_ref(x_33);
 x_402 = lean_box(0);
}
x_403 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_404 = lean_array_get(x_403, x_26, x_10);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_box(3);
x_407 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_405, x_406);
lean_dec(x_405);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
lean_dec(x_404);
x_408 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_402)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_402;
}
lean_ctor_set(x_409, 0, x_34);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_array_get_size(x_26);
x_411 = lean_unsigned_to_nat(1u);
x_412 = lean_nat_sub(x_410, x_411);
x_413 = lean_nat_dec_lt(x_10, x_410);
lean_dec(x_410);
if (x_413 == 0)
{
lean_object* x_414; 
lean_dec(x_412);
lean_dec(x_409);
lean_dec(x_401);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_4);
lean_ctor_set(x_414, 1, x_400);
return x_414;
}
else
{
lean_object* x_415; 
x_415 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(x_26, x_409, x_10, x_412);
lean_dec(x_409);
lean_dec(x_26);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; 
lean_dec(x_401);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_4);
lean_ctor_set(x_416, 1, x_400);
return x_416;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_415, 0);
lean_inc(x_417);
lean_dec(x_415);
x_418 = l_Array_append___rarg(x_30, x_401);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_1 = x_10;
x_2 = x_418;
x_3 = x_419;
x_9 = x_400;
goto _start;
}
}
}
else
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_404, 1);
lean_inc(x_421);
lean_dec(x_404);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_422 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_421, x_4, x_5, x_6, x_7, x_8, x_400);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_425 = x_422;
} else {
 lean_dec_ref(x_422);
 x_425 = lean_box(0);
}
x_426 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_402)) {
 x_427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_427 = x_402;
}
lean_ctor_set(x_427, 0, x_34);
lean_ctor_set(x_427, 1, x_426);
x_428 = lean_array_get_size(x_26);
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_nat_sub(x_428, x_429);
x_431 = lean_nat_dec_lt(x_10, x_428);
lean_dec(x_428);
if (x_431 == 0)
{
lean_object* x_432; 
lean_dec(x_430);
lean_dec(x_427);
lean_dec(x_401);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_425)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_425;
}
lean_ctor_set(x_432, 0, x_423);
lean_ctor_set(x_432, 1, x_424);
return x_432;
}
else
{
lean_object* x_433; 
x_433 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_26, x_427, x_10, x_430);
lean_dec(x_427);
lean_dec(x_26);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; 
lean_dec(x_401);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_425)) {
 x_434 = lean_alloc_ctor(0, 2, 0);
} else {
 x_434 = x_425;
}
lean_ctor_set(x_434, 0, x_423);
lean_ctor_set(x_434, 1, x_424);
return x_434;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_425);
x_435 = lean_ctor_get(x_433, 0);
lean_inc(x_435);
lean_dec(x_433);
x_436 = l_Array_append___rarg(x_30, x_401);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
x_1 = x_10;
x_2 = x_436;
x_3 = x_437;
x_4 = x_423;
x_9 = x_424;
goto _start;
}
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_439 = lean_ctor_get(x_422, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_422, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_441 = x_422;
} else {
 lean_dec_ref(x_422);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
}
}
case 3:
{
uint8_t x_443; 
lean_dec(x_33);
x_443 = !lean_is_exclusive(x_32);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_444 = lean_ctor_get(x_32, 1);
x_445 = lean_ctor_get(x_32, 0);
lean_dec(x_445);
x_446 = lean_array_get_size(x_26);
x_447 = lean_nat_dec_lt(x_10, x_446);
if (x_447 == 0)
{
lean_dec(x_446);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
uint8_t x_448; 
x_448 = lean_nat_dec_le(x_446, x_446);
if (x_448 == 0)
{
lean_dec(x_446);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
size_t x_449; size_t x_450; lean_object* x_451; 
lean_free_object(x_32);
x_449 = 0;
x_450 = lean_usize_of_nat(x_446);
lean_dec(x_446);
x_451 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(x_30, x_26, x_449, x_450, x_4, x_5, x_6, x_7, x_8, x_444);
lean_dec(x_26);
return x_451;
}
}
}
else
{
lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_452 = lean_ctor_get(x_32, 1);
lean_inc(x_452);
lean_dec(x_32);
x_453 = lean_array_get_size(x_26);
x_454 = lean_nat_dec_lt(x_10, x_453);
if (x_454 == 0)
{
lean_object* x_455; 
lean_dec(x_453);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_4);
lean_ctor_set(x_455, 1, x_452);
return x_455;
}
else
{
uint8_t x_456; 
x_456 = lean_nat_dec_le(x_453, x_453);
if (x_456 == 0)
{
lean_object* x_457; 
lean_dec(x_453);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_4);
lean_ctor_set(x_457, 1, x_452);
return x_457;
}
else
{
size_t x_458; size_t x_459; lean_object* x_460; 
x_458 = 0;
x_459 = lean_usize_of_nat(x_453);
lean_dec(x_453);
x_460 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(x_30, x_26, x_458, x_459, x_4, x_5, x_6, x_7, x_8, x_452);
lean_dec(x_26);
return x_460;
}
}
}
}
case 4:
{
uint8_t x_461; 
x_461 = !lean_is_exclusive(x_32);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; uint8_t x_464; 
x_462 = lean_ctor_get(x_32, 1);
x_463 = lean_ctor_get(x_32, 0);
lean_dec(x_463);
x_464 = !lean_is_exclusive(x_33);
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
x_465 = lean_ctor_get(x_33, 1);
x_466 = lean_ctor_get(x_33, 0);
lean_dec(x_466);
x_467 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_468 = lean_array_get(x_467, x_26, x_10);
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_box(3);
x_471 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_469, x_470);
lean_dec(x_469);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
lean_dec(x_468);
x_472 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_472);
x_473 = lean_array_get_size(x_26);
x_474 = lean_unsigned_to_nat(1u);
x_475 = lean_nat_sub(x_473, x_474);
x_476 = lean_nat_dec_lt(x_10, x_473);
lean_dec(x_473);
if (x_476 == 0)
{
lean_dec(x_475);
lean_dec(x_33);
lean_dec(x_465);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_477; 
x_477 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(x_26, x_33, x_10, x_475);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_477) == 0)
{
lean_dec(x_465);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_free_object(x_32);
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
lean_dec(x_477);
x_479 = l_Array_append___rarg(x_30, x_465);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec(x_478);
x_1 = x_10;
x_2 = x_479;
x_3 = x_480;
x_9 = x_462;
goto _start;
}
}
}
else
{
lean_object* x_482; lean_object* x_483; 
lean_free_object(x_32);
x_482 = lean_ctor_get(x_468, 1);
lean_inc(x_482);
lean_dec(x_468);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_483 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_482, x_4, x_5, x_6, x_7, x_8, x_462);
if (lean_obj_tag(x_483) == 0)
{
uint8_t x_484; 
x_484 = !lean_is_exclusive(x_483);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; 
x_485 = lean_ctor_get(x_483, 0);
x_486 = lean_ctor_get(x_483, 1);
x_487 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_487);
x_488 = lean_array_get_size(x_26);
x_489 = lean_unsigned_to_nat(1u);
x_490 = lean_nat_sub(x_488, x_489);
x_491 = lean_nat_dec_lt(x_10, x_488);
lean_dec(x_488);
if (x_491 == 0)
{
lean_dec(x_490);
lean_dec(x_33);
lean_dec(x_465);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_483;
}
else
{
lean_object* x_492; 
x_492 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(x_26, x_33, x_10, x_490);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_492) == 0)
{
lean_dec(x_465);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_483;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_free_object(x_483);
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
lean_dec(x_492);
x_494 = l_Array_append___rarg(x_30, x_465);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_1 = x_10;
x_2 = x_494;
x_3 = x_495;
x_4 = x_485;
x_9 = x_486;
goto _start;
}
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_497 = lean_ctor_get(x_483, 0);
x_498 = lean_ctor_get(x_483, 1);
lean_inc(x_498);
lean_inc(x_497);
lean_dec(x_483);
x_499 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_499);
x_500 = lean_array_get_size(x_26);
x_501 = lean_unsigned_to_nat(1u);
x_502 = lean_nat_sub(x_500, x_501);
x_503 = lean_nat_dec_lt(x_10, x_500);
lean_dec(x_500);
if (x_503 == 0)
{
lean_object* x_504; 
lean_dec(x_502);
lean_dec(x_33);
lean_dec(x_465);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_504, 0, x_497);
lean_ctor_set(x_504, 1, x_498);
return x_504;
}
else
{
lean_object* x_505; 
x_505 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(x_26, x_33, x_10, x_502);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; 
lean_dec(x_465);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_498);
return x_506;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_505, 0);
lean_inc(x_507);
lean_dec(x_505);
x_508 = l_Array_append___rarg(x_30, x_465);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_1 = x_10;
x_2 = x_508;
x_3 = x_509;
x_4 = x_497;
x_9 = x_498;
goto _start;
}
}
}
}
else
{
uint8_t x_511; 
lean_free_object(x_33);
lean_dec(x_465);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_511 = !lean_is_exclusive(x_483);
if (x_511 == 0)
{
return x_483;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_512 = lean_ctor_get(x_483, 0);
x_513 = lean_ctor_get(x_483, 1);
lean_inc(x_513);
lean_inc(x_512);
lean_dec(x_483);
x_514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
return x_514;
}
}
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; 
x_515 = lean_ctor_get(x_33, 1);
lean_inc(x_515);
lean_dec(x_33);
x_516 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_517 = lean_array_get(x_516, x_26, x_10);
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_box(3);
x_520 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_518, x_519);
lean_dec(x_518);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; 
lean_dec(x_517);
x_521 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_522, 0, x_34);
lean_ctor_set(x_522, 1, x_521);
x_523 = lean_array_get_size(x_26);
x_524 = lean_unsigned_to_nat(1u);
x_525 = lean_nat_sub(x_523, x_524);
x_526 = lean_nat_dec_lt(x_10, x_523);
lean_dec(x_523);
if (x_526 == 0)
{
lean_dec(x_525);
lean_dec(x_522);
lean_dec(x_515);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_527; 
x_527 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(x_26, x_522, x_10, x_525);
lean_dec(x_522);
lean_dec(x_26);
if (lean_obj_tag(x_527) == 0)
{
lean_dec(x_515);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_free_object(x_32);
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
lean_dec(x_527);
x_529 = l_Array_append___rarg(x_30, x_515);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
lean_dec(x_528);
x_1 = x_10;
x_2 = x_529;
x_3 = x_530;
x_9 = x_462;
goto _start;
}
}
}
else
{
lean_object* x_532; lean_object* x_533; 
lean_free_object(x_32);
x_532 = lean_ctor_get(x_517, 1);
lean_inc(x_532);
lean_dec(x_517);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_533 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_532, x_4, x_5, x_6, x_7, x_8, x_462);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_536 = x_533;
} else {
 lean_dec_ref(x_533);
 x_536 = lean_box(0);
}
x_537 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_34);
lean_ctor_set(x_538, 1, x_537);
x_539 = lean_array_get_size(x_26);
x_540 = lean_unsigned_to_nat(1u);
x_541 = lean_nat_sub(x_539, x_540);
x_542 = lean_nat_dec_lt(x_10, x_539);
lean_dec(x_539);
if (x_542 == 0)
{
lean_object* x_543; 
lean_dec(x_541);
lean_dec(x_538);
lean_dec(x_515);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_536)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_536;
}
lean_ctor_set(x_543, 0, x_534);
lean_ctor_set(x_543, 1, x_535);
return x_543;
}
else
{
lean_object* x_544; 
x_544 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(x_26, x_538, x_10, x_541);
lean_dec(x_538);
lean_dec(x_26);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; 
lean_dec(x_515);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_536)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_536;
}
lean_ctor_set(x_545, 0, x_534);
lean_ctor_set(x_545, 1, x_535);
return x_545;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_536);
x_546 = lean_ctor_get(x_544, 0);
lean_inc(x_546);
lean_dec(x_544);
x_547 = l_Array_append___rarg(x_30, x_515);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec(x_546);
x_1 = x_10;
x_2 = x_547;
x_3 = x_548;
x_4 = x_534;
x_9 = x_535;
goto _start;
}
}
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_515);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_550 = lean_ctor_get(x_533, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_533, 1);
lean_inc(x_551);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_552 = x_533;
} else {
 lean_dec_ref(x_533);
 x_552 = lean_box(0);
}
if (lean_is_scalar(x_552)) {
 x_553 = lean_alloc_ctor(1, 2, 0);
} else {
 x_553 = x_552;
}
lean_ctor_set(x_553, 0, x_550);
lean_ctor_set(x_553, 1, x_551);
return x_553;
}
}
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; 
x_554 = lean_ctor_get(x_32, 1);
lean_inc(x_554);
lean_dec(x_32);
x_555 = lean_ctor_get(x_33, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_556 = x_33;
} else {
 lean_dec_ref(x_33);
 x_556 = lean_box(0);
}
x_557 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_558 = lean_array_get(x_557, x_26, x_10);
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_box(3);
x_561 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_559, x_560);
lean_dec(x_559);
if (x_561 == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; 
lean_dec(x_558);
x_562 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_556)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_556;
}
lean_ctor_set(x_563, 0, x_34);
lean_ctor_set(x_563, 1, x_562);
x_564 = lean_array_get_size(x_26);
x_565 = lean_unsigned_to_nat(1u);
x_566 = lean_nat_sub(x_564, x_565);
x_567 = lean_nat_dec_lt(x_10, x_564);
lean_dec(x_564);
if (x_567 == 0)
{
lean_object* x_568; 
lean_dec(x_566);
lean_dec(x_563);
lean_dec(x_555);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_568, 0, x_4);
lean_ctor_set(x_568, 1, x_554);
return x_568;
}
else
{
lean_object* x_569; 
x_569 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(x_26, x_563, x_10, x_566);
lean_dec(x_563);
lean_dec(x_26);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; 
lean_dec(x_555);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_570 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_570, 0, x_4);
lean_ctor_set(x_570, 1, x_554);
return x_570;
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_571 = lean_ctor_get(x_569, 0);
lean_inc(x_571);
lean_dec(x_569);
x_572 = l_Array_append___rarg(x_30, x_555);
x_573 = lean_ctor_get(x_571, 1);
lean_inc(x_573);
lean_dec(x_571);
x_1 = x_10;
x_2 = x_572;
x_3 = x_573;
x_9 = x_554;
goto _start;
}
}
}
else
{
lean_object* x_575; lean_object* x_576; 
x_575 = lean_ctor_get(x_558, 1);
lean_inc(x_575);
lean_dec(x_558);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_576 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_575, x_4, x_5, x_6, x_7, x_8, x_554);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; uint8_t x_585; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_579 = x_576;
} else {
 lean_dec_ref(x_576);
 x_579 = lean_box(0);
}
x_580 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_556)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_556;
}
lean_ctor_set(x_581, 0, x_34);
lean_ctor_set(x_581, 1, x_580);
x_582 = lean_array_get_size(x_26);
x_583 = lean_unsigned_to_nat(1u);
x_584 = lean_nat_sub(x_582, x_583);
x_585 = lean_nat_dec_lt(x_10, x_582);
lean_dec(x_582);
if (x_585 == 0)
{
lean_object* x_586; 
lean_dec(x_584);
lean_dec(x_581);
lean_dec(x_555);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_579)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_579;
}
lean_ctor_set(x_586, 0, x_577);
lean_ctor_set(x_586, 1, x_578);
return x_586;
}
else
{
lean_object* x_587; 
x_587 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(x_26, x_581, x_10, x_584);
lean_dec(x_581);
lean_dec(x_26);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; 
lean_dec(x_555);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_579)) {
 x_588 = lean_alloc_ctor(0, 2, 0);
} else {
 x_588 = x_579;
}
lean_ctor_set(x_588, 0, x_577);
lean_ctor_set(x_588, 1, x_578);
return x_588;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; 
lean_dec(x_579);
x_589 = lean_ctor_get(x_587, 0);
lean_inc(x_589);
lean_dec(x_587);
x_590 = l_Array_append___rarg(x_30, x_555);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
x_1 = x_10;
x_2 = x_590;
x_3 = x_591;
x_4 = x_577;
x_9 = x_578;
goto _start;
}
}
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_593 = lean_ctor_get(x_576, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_576, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_595 = x_576;
} else {
 lean_dec_ref(x_576);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(1, 2, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_593);
lean_ctor_set(x_596, 1, x_594);
return x_596;
}
}
}
}
case 5:
{
lean_object* x_597; lean_object* x_598; uint8_t x_599; 
x_597 = lean_ctor_get(x_32, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_598 = x_32;
} else {
 lean_dec_ref(x_32);
 x_598 = lean_box(0);
}
x_599 = !lean_is_exclusive(x_33);
if (x_599 == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; uint8_t x_606; 
x_600 = lean_ctor_get(x_33, 1);
x_601 = lean_ctor_get(x_33, 0);
lean_dec(x_601);
x_602 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_603 = lean_array_get(x_602, x_26, x_10);
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_box(3);
x_606 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_604, x_605);
lean_dec(x_604);
if (x_606 == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; 
lean_dec(x_603);
x_623 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_623);
x_624 = lean_array_get_size(x_26);
x_625 = lean_unsigned_to_nat(1u);
x_626 = lean_nat_sub(x_624, x_625);
x_627 = lean_nat_dec_lt(x_10, x_624);
lean_dec(x_624);
if (x_627 == 0)
{
lean_dec(x_626);
lean_dec(x_33);
lean_dec(x_600);
x_607 = x_4;
x_608 = x_597;
goto block_622;
}
else
{
lean_object* x_628; 
x_628 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__11___rarg(x_26, x_33, x_10, x_626);
lean_dec(x_33);
if (lean_obj_tag(x_628) == 0)
{
lean_dec(x_600);
x_607 = x_4;
x_608 = x_597;
goto block_622;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
lean_dec(x_628);
lean_inc(x_30);
x_630 = l_Array_append___rarg(x_30, x_600);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec(x_629);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_632 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_630, x_631, x_4, x_5, x_6, x_7, x_8, x_597);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_607 = x_633;
x_608 = x_634;
goto block_622;
}
else
{
uint8_t x_635; 
lean_dec(x_598);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_635 = !lean_is_exclusive(x_632);
if (x_635 == 0)
{
return x_632;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_632, 0);
x_637 = lean_ctor_get(x_632, 1);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_632);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
return x_638;
}
}
}
}
block_622:
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; 
x_609 = lean_array_get_size(x_26);
x_610 = lean_unsigned_to_nat(1u);
x_611 = lean_nat_sub(x_609, x_610);
x_612 = lean_nat_dec_lt(x_10, x_609);
lean_dec(x_609);
if (x_612 == 0)
{
lean_object* x_613; 
lean_dec(x_611);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_598)) {
 x_613 = lean_alloc_ctor(0, 2, 0);
} else {
 x_613 = x_598;
}
lean_ctor_set(x_613, 0, x_607);
lean_ctor_set(x_613, 1, x_608);
return x_613;
}
else
{
lean_object* x_614; lean_object* x_615; 
x_614 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_615 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__10___rarg(x_26, x_614, x_10, x_611);
lean_dec(x_26);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; 
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_598)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_598;
}
lean_ctor_set(x_616, 0, x_607);
lean_ctor_set(x_616, 1, x_608);
return x_616;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_598);
x_617 = lean_ctor_get(x_615, 0);
lean_inc(x_617);
lean_dec(x_615);
x_618 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_619 = l_Array_append___rarg(x_30, x_618);
x_620 = lean_ctor_get(x_617, 1);
lean_inc(x_620);
lean_dec(x_617);
x_1 = x_10;
x_2 = x_619;
x_3 = x_620;
x_4 = x_607;
x_9 = x_608;
goto _start;
}
}
}
}
else
{
lean_object* x_639; lean_object* x_640; 
lean_dec(x_598);
x_639 = lean_ctor_get(x_603, 1);
lean_inc(x_639);
lean_dec(x_603);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_640 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_639, x_4, x_5, x_6, x_7, x_8, x_597);
if (lean_obj_tag(x_640) == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; uint8_t x_664; 
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_643 = x_640;
} else {
 lean_dec_ref(x_640);
 x_643 = lean_box(0);
}
x_660 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_660);
x_661 = lean_array_get_size(x_26);
x_662 = lean_unsigned_to_nat(1u);
x_663 = lean_nat_sub(x_661, x_662);
x_664 = lean_nat_dec_lt(x_10, x_661);
lean_dec(x_661);
if (x_664 == 0)
{
lean_dec(x_663);
lean_dec(x_33);
lean_dec(x_600);
x_644 = x_641;
x_645 = x_642;
goto block_659;
}
else
{
lean_object* x_665; 
x_665 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__13___rarg(x_26, x_33, x_10, x_663);
lean_dec(x_33);
if (lean_obj_tag(x_665) == 0)
{
lean_dec(x_600);
x_644 = x_641;
x_645 = x_642;
goto block_659;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
lean_dec(x_665);
lean_inc(x_30);
x_667 = l_Array_append___rarg(x_30, x_600);
x_668 = lean_ctor_get(x_666, 1);
lean_inc(x_668);
lean_dec(x_666);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_669 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_667, x_668, x_641, x_5, x_6, x_7, x_8, x_642);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec(x_669);
x_644 = x_670;
x_645 = x_671;
goto block_659;
}
else
{
uint8_t x_672; 
lean_dec(x_643);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_672 = !lean_is_exclusive(x_669);
if (x_672 == 0)
{
return x_669;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_669, 0);
x_674 = lean_ctor_get(x_669, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_669);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
}
block_659:
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; 
x_646 = lean_array_get_size(x_26);
x_647 = lean_unsigned_to_nat(1u);
x_648 = lean_nat_sub(x_646, x_647);
x_649 = lean_nat_dec_lt(x_10, x_646);
lean_dec(x_646);
if (x_649 == 0)
{
lean_object* x_650; 
lean_dec(x_648);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_643)) {
 x_650 = lean_alloc_ctor(0, 2, 0);
} else {
 x_650 = x_643;
}
lean_ctor_set(x_650, 0, x_644);
lean_ctor_set(x_650, 1, x_645);
return x_650;
}
else
{
lean_object* x_651; lean_object* x_652; 
x_651 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_652 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__12___rarg(x_26, x_651, x_10, x_648);
lean_dec(x_26);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; 
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_643)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_643;
}
lean_ctor_set(x_653, 0, x_644);
lean_ctor_set(x_653, 1, x_645);
return x_653;
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_643);
x_654 = lean_ctor_get(x_652, 0);
lean_inc(x_654);
lean_dec(x_652);
x_655 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_656 = l_Array_append___rarg(x_30, x_655);
x_657 = lean_ctor_get(x_654, 1);
lean_inc(x_657);
lean_dec(x_654);
x_1 = x_10;
x_2 = x_656;
x_3 = x_657;
x_4 = x_644;
x_9 = x_645;
goto _start;
}
}
}
}
else
{
uint8_t x_676; 
lean_free_object(x_33);
lean_dec(x_600);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_676 = !lean_is_exclusive(x_640);
if (x_676 == 0)
{
return x_640;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_640, 0);
x_678 = lean_ctor_get(x_640, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_640);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
return x_679;
}
}
}
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; 
x_680 = lean_ctor_get(x_33, 1);
lean_inc(x_680);
lean_dec(x_33);
x_681 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_682 = lean_array_get(x_681, x_26, x_10);
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = lean_box(3);
x_685 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_683, x_684);
lean_dec(x_683);
if (x_685 == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; uint8_t x_707; 
lean_dec(x_682);
x_702 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_703, 0, x_34);
lean_ctor_set(x_703, 1, x_702);
x_704 = lean_array_get_size(x_26);
x_705 = lean_unsigned_to_nat(1u);
x_706 = lean_nat_sub(x_704, x_705);
x_707 = lean_nat_dec_lt(x_10, x_704);
lean_dec(x_704);
if (x_707 == 0)
{
lean_dec(x_706);
lean_dec(x_703);
lean_dec(x_680);
x_686 = x_4;
x_687 = x_597;
goto block_701;
}
else
{
lean_object* x_708; 
x_708 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__11___rarg(x_26, x_703, x_10, x_706);
lean_dec(x_703);
if (lean_obj_tag(x_708) == 0)
{
lean_dec(x_680);
x_686 = x_4;
x_687 = x_597;
goto block_701;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
lean_dec(x_708);
lean_inc(x_30);
x_710 = l_Array_append___rarg(x_30, x_680);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
lean_dec(x_709);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_712 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_710, x_711, x_4, x_5, x_6, x_7, x_8, x_597);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
x_686 = x_713;
x_687 = x_714;
goto block_701;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
lean_dec(x_598);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_715 = lean_ctor_get(x_712, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_712, 1);
lean_inc(x_716);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_717 = x_712;
} else {
 lean_dec_ref(x_712);
 x_717 = lean_box(0);
}
if (lean_is_scalar(x_717)) {
 x_718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_718 = x_717;
}
lean_ctor_set(x_718, 0, x_715);
lean_ctor_set(x_718, 1, x_716);
return x_718;
}
}
}
block_701:
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; 
x_688 = lean_array_get_size(x_26);
x_689 = lean_unsigned_to_nat(1u);
x_690 = lean_nat_sub(x_688, x_689);
x_691 = lean_nat_dec_lt(x_10, x_688);
lean_dec(x_688);
if (x_691 == 0)
{
lean_object* x_692; 
lean_dec(x_690);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_598)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_598;
}
lean_ctor_set(x_692, 0, x_686);
lean_ctor_set(x_692, 1, x_687);
return x_692;
}
else
{
lean_object* x_693; lean_object* x_694; 
x_693 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_694 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__10___rarg(x_26, x_693, x_10, x_690);
lean_dec(x_26);
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; 
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_598)) {
 x_695 = lean_alloc_ctor(0, 2, 0);
} else {
 x_695 = x_598;
}
lean_ctor_set(x_695, 0, x_686);
lean_ctor_set(x_695, 1, x_687);
return x_695;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_598);
x_696 = lean_ctor_get(x_694, 0);
lean_inc(x_696);
lean_dec(x_694);
x_697 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_698 = l_Array_append___rarg(x_30, x_697);
x_699 = lean_ctor_get(x_696, 1);
lean_inc(x_699);
lean_dec(x_696);
x_1 = x_10;
x_2 = x_698;
x_3 = x_699;
x_4 = x_686;
x_9 = x_687;
goto _start;
}
}
}
}
else
{
lean_object* x_719; lean_object* x_720; 
lean_dec(x_598);
x_719 = lean_ctor_get(x_682, 1);
lean_inc(x_719);
lean_dec(x_682);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_720 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_719, x_4, x_5, x_6, x_7, x_8, x_597);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; uint8_t x_745; 
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_723 = x_720;
} else {
 lean_dec_ref(x_720);
 x_723 = lean_box(0);
}
x_740 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_741 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_741, 0, x_34);
lean_ctor_set(x_741, 1, x_740);
x_742 = lean_array_get_size(x_26);
x_743 = lean_unsigned_to_nat(1u);
x_744 = lean_nat_sub(x_742, x_743);
x_745 = lean_nat_dec_lt(x_10, x_742);
lean_dec(x_742);
if (x_745 == 0)
{
lean_dec(x_744);
lean_dec(x_741);
lean_dec(x_680);
x_724 = x_721;
x_725 = x_722;
goto block_739;
}
else
{
lean_object* x_746; 
x_746 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__13___rarg(x_26, x_741, x_10, x_744);
lean_dec(x_741);
if (lean_obj_tag(x_746) == 0)
{
lean_dec(x_680);
x_724 = x_721;
x_725 = x_722;
goto block_739;
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_747 = lean_ctor_get(x_746, 0);
lean_inc(x_747);
lean_dec(x_746);
lean_inc(x_30);
x_748 = l_Array_append___rarg(x_30, x_680);
x_749 = lean_ctor_get(x_747, 1);
lean_inc(x_749);
lean_dec(x_747);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_750 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_748, x_749, x_721, x_5, x_6, x_7, x_8, x_722);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
lean_dec(x_750);
x_724 = x_751;
x_725 = x_752;
goto block_739;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; 
lean_dec(x_723);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_753 = lean_ctor_get(x_750, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_750, 1);
lean_inc(x_754);
if (lean_is_exclusive(x_750)) {
 lean_ctor_release(x_750, 0);
 lean_ctor_release(x_750, 1);
 x_755 = x_750;
} else {
 lean_dec_ref(x_750);
 x_755 = lean_box(0);
}
if (lean_is_scalar(x_755)) {
 x_756 = lean_alloc_ctor(1, 2, 0);
} else {
 x_756 = x_755;
}
lean_ctor_set(x_756, 0, x_753);
lean_ctor_set(x_756, 1, x_754);
return x_756;
}
}
}
block_739:
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; 
x_726 = lean_array_get_size(x_26);
x_727 = lean_unsigned_to_nat(1u);
x_728 = lean_nat_sub(x_726, x_727);
x_729 = lean_nat_dec_lt(x_10, x_726);
lean_dec(x_726);
if (x_729 == 0)
{
lean_object* x_730; 
lean_dec(x_728);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_723)) {
 x_730 = lean_alloc_ctor(0, 2, 0);
} else {
 x_730 = x_723;
}
lean_ctor_set(x_730, 0, x_724);
lean_ctor_set(x_730, 1, x_725);
return x_730;
}
else
{
lean_object* x_731; lean_object* x_732; 
x_731 = l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1;
x_732 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__12___rarg(x_26, x_731, x_10, x_728);
lean_dec(x_26);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; 
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_723)) {
 x_733 = lean_alloc_ctor(0, 2, 0);
} else {
 x_733 = x_723;
}
lean_ctor_set(x_733, 0, x_724);
lean_ctor_set(x_733, 1, x_725);
return x_733;
}
else
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_dec(x_723);
x_734 = lean_ctor_get(x_732, 0);
lean_inc(x_734);
lean_dec(x_732);
x_735 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_736 = l_Array_append___rarg(x_30, x_735);
x_737 = lean_ctor_get(x_734, 1);
lean_inc(x_737);
lean_dec(x_734);
x_1 = x_10;
x_2 = x_736;
x_3 = x_737;
x_4 = x_724;
x_9 = x_725;
goto _start;
}
}
}
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_680);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_757 = lean_ctor_get(x_720, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_720, 1);
lean_inc(x_758);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_759 = x_720;
} else {
 lean_dec_ref(x_720);
 x_759 = lean_box(0);
}
if (lean_is_scalar(x_759)) {
 x_760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_760 = x_759;
}
lean_ctor_set(x_760, 0, x_757);
lean_ctor_set(x_760, 1, x_758);
return x_760;
}
}
}
}
default: 
{
uint8_t x_761; 
x_761 = !lean_is_exclusive(x_32);
if (x_761 == 0)
{
lean_object* x_762; lean_object* x_763; uint8_t x_764; 
x_762 = lean_ctor_get(x_32, 1);
x_763 = lean_ctor_get(x_32, 0);
lean_dec(x_763);
x_764 = !lean_is_exclusive(x_33);
if (x_764 == 0)
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; uint8_t x_771; 
x_765 = lean_ctor_get(x_33, 1);
x_766 = lean_ctor_get(x_33, 0);
lean_dec(x_766);
x_767 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_768 = lean_array_get(x_767, x_26, x_10);
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_box(3);
x_771 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_769, x_770);
lean_dec(x_769);
if (x_771 == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; uint8_t x_776; 
lean_dec(x_768);
x_772 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_772);
x_773 = lean_array_get_size(x_26);
x_774 = lean_unsigned_to_nat(1u);
x_775 = lean_nat_sub(x_773, x_774);
x_776 = lean_nat_dec_lt(x_10, x_773);
lean_dec(x_773);
if (x_776 == 0)
{
lean_dec(x_775);
lean_dec(x_33);
lean_dec(x_765);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_777; 
x_777 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__14___rarg(x_26, x_33, x_10, x_775);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_777) == 0)
{
lean_dec(x_765);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
lean_free_object(x_32);
x_778 = lean_ctor_get(x_777, 0);
lean_inc(x_778);
lean_dec(x_777);
x_779 = l_Array_append___rarg(x_30, x_765);
x_780 = lean_ctor_get(x_778, 1);
lean_inc(x_780);
lean_dec(x_778);
x_1 = x_10;
x_2 = x_779;
x_3 = x_780;
x_9 = x_762;
goto _start;
}
}
}
else
{
lean_object* x_782; lean_object* x_783; 
lean_free_object(x_32);
x_782 = lean_ctor_get(x_768, 1);
lean_inc(x_782);
lean_dec(x_768);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_783 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_782, x_4, x_5, x_6, x_7, x_8, x_762);
if (lean_obj_tag(x_783) == 0)
{
uint8_t x_784; 
x_784 = !lean_is_exclusive(x_783);
if (x_784 == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_785 = lean_ctor_get(x_783, 0);
x_786 = lean_ctor_get(x_783, 1);
x_787 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_787);
x_788 = lean_array_get_size(x_26);
x_789 = lean_unsigned_to_nat(1u);
x_790 = lean_nat_sub(x_788, x_789);
x_791 = lean_nat_dec_lt(x_10, x_788);
lean_dec(x_788);
if (x_791 == 0)
{
lean_dec(x_790);
lean_dec(x_33);
lean_dec(x_765);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_783;
}
else
{
lean_object* x_792; 
x_792 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15___rarg(x_26, x_33, x_10, x_790);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_792) == 0)
{
lean_dec(x_765);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_783;
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_free_object(x_783);
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
lean_dec(x_792);
x_794 = l_Array_append___rarg(x_30, x_765);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec(x_793);
x_1 = x_10;
x_2 = x_794;
x_3 = x_795;
x_4 = x_785;
x_9 = x_786;
goto _start;
}
}
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; uint8_t x_803; 
x_797 = lean_ctor_get(x_783, 0);
x_798 = lean_ctor_get(x_783, 1);
lean_inc(x_798);
lean_inc(x_797);
lean_dec(x_783);
x_799 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
lean_ctor_set(x_33, 1, x_799);
x_800 = lean_array_get_size(x_26);
x_801 = lean_unsigned_to_nat(1u);
x_802 = lean_nat_sub(x_800, x_801);
x_803 = lean_nat_dec_lt(x_10, x_800);
lean_dec(x_800);
if (x_803 == 0)
{
lean_object* x_804; 
lean_dec(x_802);
lean_dec(x_33);
lean_dec(x_765);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_804 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_804, 0, x_797);
lean_ctor_set(x_804, 1, x_798);
return x_804;
}
else
{
lean_object* x_805; 
x_805 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15___rarg(x_26, x_33, x_10, x_802);
lean_dec(x_33);
lean_dec(x_26);
if (lean_obj_tag(x_805) == 0)
{
lean_object* x_806; 
lean_dec(x_765);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_806 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_806, 0, x_797);
lean_ctor_set(x_806, 1, x_798);
return x_806;
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_807 = lean_ctor_get(x_805, 0);
lean_inc(x_807);
lean_dec(x_805);
x_808 = l_Array_append___rarg(x_30, x_765);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec(x_807);
x_1 = x_10;
x_2 = x_808;
x_3 = x_809;
x_4 = x_797;
x_9 = x_798;
goto _start;
}
}
}
}
else
{
uint8_t x_811; 
lean_free_object(x_33);
lean_dec(x_765);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_811 = !lean_is_exclusive(x_783);
if (x_811 == 0)
{
return x_783;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_812 = lean_ctor_get(x_783, 0);
x_813 = lean_ctor_get(x_783, 1);
lean_inc(x_813);
lean_inc(x_812);
lean_dec(x_783);
x_814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_814, 0, x_812);
lean_ctor_set(x_814, 1, x_813);
return x_814;
}
}
}
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; uint8_t x_820; 
x_815 = lean_ctor_get(x_33, 1);
lean_inc(x_815);
lean_dec(x_33);
x_816 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_817 = lean_array_get(x_816, x_26, x_10);
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
x_819 = lean_box(3);
x_820 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_818, x_819);
lean_dec(x_818);
if (x_820 == 0)
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; uint8_t x_826; 
lean_dec(x_817);
x_821 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_822 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_822, 0, x_34);
lean_ctor_set(x_822, 1, x_821);
x_823 = lean_array_get_size(x_26);
x_824 = lean_unsigned_to_nat(1u);
x_825 = lean_nat_sub(x_823, x_824);
x_826 = lean_nat_dec_lt(x_10, x_823);
lean_dec(x_823);
if (x_826 == 0)
{
lean_dec(x_825);
lean_dec(x_822);
lean_dec(x_815);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_827; 
x_827 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__14___rarg(x_26, x_822, x_10, x_825);
lean_dec(x_822);
lean_dec(x_26);
if (lean_obj_tag(x_827) == 0)
{
lean_dec(x_815);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; 
lean_free_object(x_32);
x_828 = lean_ctor_get(x_827, 0);
lean_inc(x_828);
lean_dec(x_827);
x_829 = l_Array_append___rarg(x_30, x_815);
x_830 = lean_ctor_get(x_828, 1);
lean_inc(x_830);
lean_dec(x_828);
x_1 = x_10;
x_2 = x_829;
x_3 = x_830;
x_9 = x_762;
goto _start;
}
}
}
else
{
lean_object* x_832; lean_object* x_833; 
lean_free_object(x_32);
x_832 = lean_ctor_get(x_817, 1);
lean_inc(x_832);
lean_dec(x_817);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_833 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_832, x_4, x_5, x_6, x_7, x_8, x_762);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; 
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_836 = x_833;
} else {
 lean_dec_ref(x_833);
 x_836 = lean_box(0);
}
x_837 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
x_838 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_838, 0, x_34);
lean_ctor_set(x_838, 1, x_837);
x_839 = lean_array_get_size(x_26);
x_840 = lean_unsigned_to_nat(1u);
x_841 = lean_nat_sub(x_839, x_840);
x_842 = lean_nat_dec_lt(x_10, x_839);
lean_dec(x_839);
if (x_842 == 0)
{
lean_object* x_843; 
lean_dec(x_841);
lean_dec(x_838);
lean_dec(x_815);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_836)) {
 x_843 = lean_alloc_ctor(0, 2, 0);
} else {
 x_843 = x_836;
}
lean_ctor_set(x_843, 0, x_834);
lean_ctor_set(x_843, 1, x_835);
return x_843;
}
else
{
lean_object* x_844; 
x_844 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15___rarg(x_26, x_838, x_10, x_841);
lean_dec(x_838);
lean_dec(x_26);
if (lean_obj_tag(x_844) == 0)
{
lean_object* x_845; 
lean_dec(x_815);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_836)) {
 x_845 = lean_alloc_ctor(0, 2, 0);
} else {
 x_845 = x_836;
}
lean_ctor_set(x_845, 0, x_834);
lean_ctor_set(x_845, 1, x_835);
return x_845;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
lean_dec(x_836);
x_846 = lean_ctor_get(x_844, 0);
lean_inc(x_846);
lean_dec(x_844);
x_847 = l_Array_append___rarg(x_30, x_815);
x_848 = lean_ctor_get(x_846, 1);
lean_inc(x_848);
lean_dec(x_846);
x_1 = x_10;
x_2 = x_847;
x_3 = x_848;
x_4 = x_834;
x_9 = x_835;
goto _start;
}
}
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; 
lean_dec(x_815);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_850 = lean_ctor_get(x_833, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_833, 1);
lean_inc(x_851);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_852 = x_833;
} else {
 lean_dec_ref(x_833);
 x_852 = lean_box(0);
}
if (lean_is_scalar(x_852)) {
 x_853 = lean_alloc_ctor(1, 2, 0);
} else {
 x_853 = x_852;
}
lean_ctor_set(x_853, 0, x_850);
lean_ctor_set(x_853, 1, x_851);
return x_853;
}
}
}
}
else
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; uint8_t x_861; 
x_854 = lean_ctor_get(x_32, 1);
lean_inc(x_854);
lean_dec(x_32);
x_855 = lean_ctor_get(x_33, 1);
lean_inc(x_855);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_856 = x_33;
} else {
 lean_dec_ref(x_33);
 x_856 = lean_box(0);
}
x_857 = l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2;
x_858 = lean_array_get(x_857, x_26, x_10);
x_859 = lean_ctor_get(x_858, 0);
lean_inc(x_859);
x_860 = lean_box(3);
x_861 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_88_(x_859, x_860);
lean_dec(x_859);
if (x_861 == 0)
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; uint8_t x_867; 
lean_dec(x_858);
x_862 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_856)) {
 x_863 = lean_alloc_ctor(0, 2, 0);
} else {
 x_863 = x_856;
}
lean_ctor_set(x_863, 0, x_34);
lean_ctor_set(x_863, 1, x_862);
x_864 = lean_array_get_size(x_26);
x_865 = lean_unsigned_to_nat(1u);
x_866 = lean_nat_sub(x_864, x_865);
x_867 = lean_nat_dec_lt(x_10, x_864);
lean_dec(x_864);
if (x_867 == 0)
{
lean_object* x_868; 
lean_dec(x_866);
lean_dec(x_863);
lean_dec(x_855);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_868 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_868, 0, x_4);
lean_ctor_set(x_868, 1, x_854);
return x_868;
}
else
{
lean_object* x_869; 
x_869 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__14___rarg(x_26, x_863, x_10, x_866);
lean_dec(x_863);
lean_dec(x_26);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; 
lean_dec(x_855);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_870 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_870, 0, x_4);
lean_ctor_set(x_870, 1, x_854);
return x_870;
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_871 = lean_ctor_get(x_869, 0);
lean_inc(x_871);
lean_dec(x_869);
x_872 = l_Array_append___rarg(x_30, x_855);
x_873 = lean_ctor_get(x_871, 1);
lean_inc(x_873);
lean_dec(x_871);
x_1 = x_10;
x_2 = x_872;
x_3 = x_873;
x_9 = x_854;
goto _start;
}
}
}
else
{
lean_object* x_875; lean_object* x_876; 
x_875 = lean_ctor_get(x_858, 1);
lean_inc(x_875);
lean_dec(x_858);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_876 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_10, x_30, x_875, x_4, x_5, x_6, x_7, x_8, x_854);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; uint8_t x_885; 
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 1);
lean_inc(x_878);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 lean_ctor_release(x_876, 1);
 x_879 = x_876;
} else {
 lean_dec_ref(x_876);
 x_879 = lean_box(0);
}
x_880 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__2;
if (lean_is_scalar(x_856)) {
 x_881 = lean_alloc_ctor(0, 2, 0);
} else {
 x_881 = x_856;
}
lean_ctor_set(x_881, 0, x_34);
lean_ctor_set(x_881, 1, x_880);
x_882 = lean_array_get_size(x_26);
x_883 = lean_unsigned_to_nat(1u);
x_884 = lean_nat_sub(x_882, x_883);
x_885 = lean_nat_dec_lt(x_10, x_882);
lean_dec(x_882);
if (x_885 == 0)
{
lean_object* x_886; 
lean_dec(x_884);
lean_dec(x_881);
lean_dec(x_855);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_879)) {
 x_886 = lean_alloc_ctor(0, 2, 0);
} else {
 x_886 = x_879;
}
lean_ctor_set(x_886, 0, x_877);
lean_ctor_set(x_886, 1, x_878);
return x_886;
}
else
{
lean_object* x_887; 
x_887 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15___rarg(x_26, x_881, x_10, x_884);
lean_dec(x_881);
lean_dec(x_26);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; 
lean_dec(x_855);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_879)) {
 x_888 = lean_alloc_ctor(0, 2, 0);
} else {
 x_888 = x_879;
}
lean_ctor_set(x_888, 0, x_877);
lean_ctor_set(x_888, 1, x_878);
return x_888;
}
else
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; 
lean_dec(x_879);
x_889 = lean_ctor_get(x_887, 0);
lean_inc(x_889);
lean_dec(x_887);
x_890 = l_Array_append___rarg(x_30, x_855);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
lean_dec(x_889);
x_1 = x_10;
x_2 = x_890;
x_3 = x_891;
x_4 = x_877;
x_9 = x_878;
goto _start;
}
}
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
lean_dec(x_856);
lean_dec(x_855);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_893 = lean_ctor_get(x_876, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_876, 1);
lean_inc(x_894);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 lean_ctor_release(x_876, 1);
 x_895 = x_876;
} else {
 lean_dec_ref(x_876);
 x_895 = lean_box(0);
}
if (lean_is_scalar(x_895)) {
 x_896 = lean_alloc_ctor(1, 2, 0);
} else {
 x_896 = x_895;
}
lean_ctor_set(x_896, 0, x_893);
lean_ctor_set(x_896, 1, x_894);
return x_896;
}
}
}
}
}
}
else
{
uint8_t x_897; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_897 = !lean_is_exclusive(x_32);
if (x_897 == 0)
{
return x_32;
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_898 = lean_ctor_get(x_32, 0);
x_899 = lean_ctor_get(x_32, 1);
lean_inc(x_899);
lean_inc(x_898);
lean_dec(x_32);
x_900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_900, 0, x_898);
lean_ctor_set(x_900, 1, x_899);
return x_900;
}
}
}
else
{
lean_object* x_901; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_901 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_901, 0, x_4);
lean_ctor_set(x_901, 1, x_9);
return x_901;
}
}
else
{
lean_object* x_902; lean_object* x_903; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_902 = l_Array_append___rarg(x_4, x_25);
x_903 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_903, 0, x_902);
lean_ctor_set(x_903, 1, x_9);
return x_903;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify_process(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getUnify_process___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__6___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__7___rarg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__8___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__9___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__10___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__11___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__12___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__13___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__14___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at_Lean_Meta_DiscrTree_getUnify_process___spec__15___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__16___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify_process___spec__16___rarg(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_2 == x_3;
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
x_20 = x_2 + x_19;
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
x_27 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(x_26, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = x_2 + x_30;
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
x_38 = x_2 + x_37;
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg___boxed), 11, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Meta_DiscrTree_Key_arity(x_2);
x_10 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_11 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_9, x_10, x_3, x_1, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(x_8, x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_20 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___closed__1;
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_20, x_18, x_19, lean_box(0), x_21, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_19);
lean_dec(x_18);
return x_22;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg), 7, 0);
return x_4;
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
if (lean_obj_tag(x_26) == 3)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_29 = l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_28, x_3, x_4, x_5, x_6, x_27);
x_8 = x_29;
goto block_17;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_24, 1);
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
lean_inc(x_1);
x_34 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_35 = l_Lean_Meta_DiscrTree_instBEqKey;
x_36 = l_Lean_Meta_DiscrTree_instHashableKey;
x_37 = l_Std_PersistentHashMap_find_x3f___rarg(x_35, x_36, x_1, x_26);
if (lean_obj_tag(x_37) == 0)
{
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_24, 0, x_34);
x_8 = x_24;
goto block_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_24);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_39, x_33, x_38, x_34, x_3, x_4, x_5, x_6, x_31);
x_8 = x_40;
goto block_17;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_dec(x_25);
lean_inc(x_1);
x_43 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_44 = l_Lean_Meta_DiscrTree_instBEqKey;
x_45 = l_Lean_Meta_DiscrTree_instHashableKey;
x_46 = l_Std_PersistentHashMap_find_x3f___rarg(x_44, x_45, x_1, x_26);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_41);
x_8 = x_47;
goto block_17;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_49, x_42, x_48, x_43, x_3, x_4, x_5, x_6, x_41);
x_8 = x_50;
goto block_17;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
x_8 = x_24;
goto block_17;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_24, 0);
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_24);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_8 = x_54;
goto block_17;
}
}
}
else
{
uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; 
x_55 = lean_ctor_get_uint8(x_19, 0);
x_56 = lean_ctor_get_uint8(x_19, 1);
x_57 = lean_ctor_get_uint8(x_19, 2);
x_58 = lean_ctor_get_uint8(x_19, 3);
x_59 = lean_ctor_get_uint8(x_19, 4);
x_60 = lean_ctor_get_uint8(x_19, 6);
x_61 = lean_ctor_get_uint8(x_19, 7);
x_62 = lean_ctor_get_uint8(x_19, 8);
x_63 = lean_ctor_get_uint8(x_19, 9);
x_64 = lean_ctor_get_uint8(x_19, 10);
lean_dec(x_19);
x_65 = 2;
x_66 = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(x_66, 0, x_55);
lean_ctor_set_uint8(x_66, 1, x_56);
lean_ctor_set_uint8(x_66, 2, x_57);
lean_ctor_set_uint8(x_66, 3, x_58);
lean_ctor_set_uint8(x_66, 4, x_59);
lean_ctor_set_uint8(x_66, 5, x_65);
lean_ctor_set_uint8(x_66, 6, x_60);
lean_ctor_set_uint8(x_66, 7, x_61);
lean_ctor_set_uint8(x_66, 8, x_62);
lean_ctor_set_uint8(x_66, 9, x_63);
lean_ctor_set_uint8(x_66, 10, x_64);
lean_ctor_set(x_3, 0, x_66);
x_67 = 0;
x_68 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_69 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_67, x_68, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 3)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_70);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_74 = l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_73, x_3, x_4, x_5, x_6, x_72);
x_8 = x_74;
goto block_17;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_dec(x_70);
lean_inc(x_1);
x_78 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_79 = l_Lean_Meta_DiscrTree_instBEqKey;
x_80 = l_Lean_Meta_DiscrTree_instHashableKey;
x_81 = l_Std_PersistentHashMap_find_x3f___rarg(x_79, x_80, x_1, x_71);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
lean_dec(x_77);
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_76)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_76;
}
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_75);
x_8 = x_82;
goto block_17;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_76);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_84, x_77, x_83, x_78, x_3, x_4, x_5, x_6, x_75);
x_8 = x_85;
goto block_17;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_86 = lean_ctor_get(x_69, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_88 = x_69;
} else {
 lean_dec_ref(x_69);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
x_8 = x_89;
goto block_17;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_110; lean_object* x_111; 
x_90 = lean_ctor_get(x_3, 0);
x_91 = lean_ctor_get(x_3, 1);
x_92 = lean_ctor_get(x_3, 2);
x_93 = lean_ctor_get(x_3, 3);
x_94 = lean_ctor_get(x_3, 4);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_3);
x_95 = lean_ctor_get_uint8(x_90, 0);
x_96 = lean_ctor_get_uint8(x_90, 1);
x_97 = lean_ctor_get_uint8(x_90, 2);
x_98 = lean_ctor_get_uint8(x_90, 3);
x_99 = lean_ctor_get_uint8(x_90, 4);
x_100 = lean_ctor_get_uint8(x_90, 6);
x_101 = lean_ctor_get_uint8(x_90, 7);
x_102 = lean_ctor_get_uint8(x_90, 8);
x_103 = lean_ctor_get_uint8(x_90, 9);
x_104 = lean_ctor_get_uint8(x_90, 10);
if (lean_is_exclusive(x_90)) {
 x_105 = x_90;
} else {
 lean_dec_ref(x_90);
 x_105 = lean_box(0);
}
x_106 = 2;
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 0, 11);
} else {
 x_107 = x_105;
}
lean_ctor_set_uint8(x_107, 0, x_95);
lean_ctor_set_uint8(x_107, 1, x_96);
lean_ctor_set_uint8(x_107, 2, x_97);
lean_ctor_set_uint8(x_107, 3, x_98);
lean_ctor_set_uint8(x_107, 4, x_99);
lean_ctor_set_uint8(x_107, 5, x_106);
lean_ctor_set_uint8(x_107, 6, x_100);
lean_ctor_set_uint8(x_107, 7, x_101);
lean_ctor_set_uint8(x_107, 8, x_102);
lean_ctor_set_uint8(x_107, 9, x_103);
lean_ctor_set_uint8(x_107, 10, x_104);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_91);
lean_ctor_set(x_108, 2, x_92);
lean_ctor_set(x_108, 3, x_93);
lean_ctor_set(x_108, 4, x_94);
x_109 = 0;
x_110 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_108);
x_111 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs(x_2, x_109, x_110, x_108, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 3)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_112);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
x_116 = l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_115, x_108, x_4, x_5, x_6, x_114);
x_8 = x_116;
goto block_17;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
lean_dec(x_112);
lean_inc(x_1);
x_120 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult___rarg(x_1);
x_121 = l_Lean_Meta_DiscrTree_instBEqKey;
x_122 = l_Lean_Meta_DiscrTree_instHashableKey;
x_123 = l_Std_PersistentHashMap_find_x3f___rarg(x_121, x_122, x_1, x_113);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
lean_dec(x_119);
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_118)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_118;
}
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_117);
x_8 = x_124;
goto block_17;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_118);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_Lean_Meta_DiscrTree_getUnify_process___rarg(x_126, x_119, x_125, x_120, x_108, x_4, x_5, x_6, x_117);
x_8 = x_127;
goto block_17;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_128 = lean_ctor_get(x_111, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_111, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_130 = x_111;
} else {
 lean_dec_ref(x_111);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
x_8 = x_131;
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
lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getUnify___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(lean_object*);
lean_object* initialize_Lean_Meta_InferType(lean_object*);
lean_object* initialize_Lean_Meta_WHNF(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_DiscrTree(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(lean_io_mk_world());
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
l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1 = _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1();
lean_mark_persistent(l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__1);
l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2 = _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2();
lean_mark_persistent(l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__2);
l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3 = _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3();
lean_mark_persistent(l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__3);
l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4 = _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4();
lean_mark_persistent(l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__4);
l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5 = _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5();
lean_mark_persistent(l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__5);
l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6 = _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6();
lean_mark_persistent(l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__6);
l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7 = _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7();
lean_mark_persistent(l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__7);
l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8 = _init_l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8();
lean_mark_persistent(l_List_map___at_Lean_Meta_DiscrTree_Trie_format___spec__1___rarg___closed__8);
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
l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__1 = _init_l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__1();
lean_mark_persistent(l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__1);
l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2 = _init_l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2();
lean_mark_persistent(l_Array_back___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__2___rarg___closed__2);
l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__1 = _init_l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__1);
l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__2 = _init_l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___spec__3___rarg___closed__2);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__5 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__5);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3);
l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1 = _init_l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_getMatch_process___rarg___closed__1);
l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___closed__1 = _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_foldlMAux___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
