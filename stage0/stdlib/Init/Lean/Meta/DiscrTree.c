// Lean compiler output
// Module: Init.Lean.Meta.DiscrTree
// Imports: Init.Lean.Meta.Basic Init.Lean.Meta.FunInfo Init.Lean.Meta.InferType
#include "runtime/lean.h"
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
uint8_t l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Init_Lean_Meta_DiscrTree_13__getMatchKeyArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Init_Lean_Meta_DiscrTree_7__pushArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__1(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_inhabited(lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__4;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__2(lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Inhabited(lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatch___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__1;
lean_object* l___private_Init_Lean_Meta_DiscrTree_10__insertVal(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__1;
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_join(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_hasFormat;
lean_object* l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__2;
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__2___rarg(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__5;
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_Key_inhabited;
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__2;
lean_object* l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__4(lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__5(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__7(lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Key_format___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_3__ignoreArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___boxed(lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_format(lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Meta_DiscrTree_DiscrTree_hasFormat(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_beq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_16__getStarResult___rarg(lean_object*);
lean_object* l_Lean_List_format___rarg(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_format(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_10__insertVal___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__7;
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__3;
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__2(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__3;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__3;
lean_object* l_Lean_Meta_DiscrTree_Key_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insert(lean_object*);
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__4(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__1(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__3(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__2___rarg(lean_object*, size_t, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_format___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_format___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binInsertM___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__2(lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__5(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPathAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___main___spec__1___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___boxed(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_hasFormat___closed__1;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__3(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_arrayHasFormat___rarg___closed__1;
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPathAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_2__tmpStar;
lean_object* l_Lean_Meta_DiscrTree_Key_arity(lean_object*);
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_5__whnfEta(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9(lean_object*);
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format___main(lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l___private_Init_Lean_Meta_DiscrTree_2__tmpStar___closed__1;
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__3(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_5__whnfEta___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__5(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_16__getStarResult(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__3___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3;
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__2(lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
extern lean_object* l_Lean_Literal_type___closed__2;
lean_object* l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_PersistentHashMap_empty___rarg___closed__2;
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__4(lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_hasLess;
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_format___spec__3(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__6;
lean_object* l_Lean_Meta_DiscrTree_format___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___main___spec__1(lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binInsertM___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath___closed__1;
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object*);
uint8_t l_Array_contains___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_3__ignoreArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_14__getUnifyKeyArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__3(lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__6(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__1;
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__6(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2;
lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__3___rarg(lean_object*);
extern lean_object* l_Lean_Format_paren___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5(lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_8__initCapacity;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main(lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatch___spec__1___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_String_quote(lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__2(lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty___closed__1;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__11(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatch___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__2;
extern lean_object* l_Lean_Format_paren___closed__2;
lean_object* l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1;
lean_object* l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__1;
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_DiscrTree_hasFormat___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__7(lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__3;
lean_object* l_Lean_Meta_DiscrTree_format___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__8;
lean_object* l_Lean_Meta_DiscrTree_format___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__3(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_arity___boxed(lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binInsertM___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__1(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format___main___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__6(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__3(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_hasFormat___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux(lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__10(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_hasFormat(lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_format___spec__1(lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__1(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__4(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__1;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_format___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_format___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_back___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__3(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__1;
lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
lean_object* l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__4(lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__2(lean_object*);
uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main(lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__3(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__2(lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__4;
lean_object* l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__9;
lean_object* l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__2;
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Trie_format___main___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_back___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__3___rarg___boxed(lean_object*);
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
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(1u);
return x_6;
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
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_Lean_Name_quickLt(x_8, x_10);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_name_eq(x_8, x_10);
if (x_13 == 0)
{
return x_12;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_9, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_box(0);
x_3 = x_16;
goto block_7;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = l_Lean_Name_quickLt(x_17, x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_name_eq(x_17, x_19);
if (x_22 == 0)
{
return x_21;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_lt(x_18, x_20);
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
lean_object* x_25; 
x_25 = lean_box(0);
x_3 = x_25;
goto block_7;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_2, 0);
x_28 = l_Lean_Literal_lt(x_26, x_27);
x_29 = l_coeDecidableEq(x_28);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_box(0);
x_3 = x_30;
goto block_7;
}
}
default: 
{
lean_object* x_31; 
x_31 = lean_box(0);
x_3 = x_31;
goto block_7;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_dec(x_3);
x_4 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_1);
x_5 = l_Lean_Meta_DiscrTree_Key_ctorIdx(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
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
lean_object* _init_l_Lean_Meta_DiscrTree_Key_hasLess() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Key_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Name_toString___closed__1;
x_3 = l_Lean_Name_toStringWithSep___main(x_2, x_1);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("*");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Key_format___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("◾");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_Key_format___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Key_format___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_Key_format(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_fmt___at_Lean_Meta_DiscrTree_Key_format___spec__1(x_4);
return x_5;
}
case 2:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_String_quote(x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
case 3:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_DiscrTree_Key_format___closed__2;
return x_12;
}
default: 
{
lean_object* x_13; 
x_13 = l_Lean_Meta_DiscrTree_Key_format___closed__4;
return x_13;
}
}
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_Key_hasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_format), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_Key_hasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_Key_hasFormat___closed__1;
return x_1;
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
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
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
lean_object* _init_l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PersistentHashMap_empty___rarg___closed__2;
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
x_2 = l_Lean_Meta_DiscrTree_empty___closed__1;
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_discr_tree_tmp");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__2;
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_2__tmpStar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId;
x_2 = l_Lean_mkMVar(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_2__tmpStar() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Init_Lean_Meta_DiscrTree_2__tmpStar___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_DiscrTree_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_empty___closed__1;
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_3__ignoreArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isProof(x_1, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_3, x_2);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*1 + 1);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; 
x_12 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
lean_dec(x_9);
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_isProof(x_1, x_4, x_5);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Meta_isType(x_1, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
lean_dec(x_27);
x_28 = 0;
x_29 = lean_box(x_28);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
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
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_5);
return x_40;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_3__ignoreArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_DiscrTree_3__ignoreArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_5);
lean_inc(x_8);
x_9 = l___private_Init_Lean_Meta_DiscrTree_3__ignoreArg(x_8, x_2, x_1, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_2, x_13);
lean_dec(x_2);
x_15 = lean_array_push(x_4, x_8);
x_2 = x_14;
x_3 = x_7;
x_4 = x_15;
x_6 = x_12;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_2, x_18);
lean_dec(x_2);
x_20 = l___private_Init_Lean_Meta_DiscrTree_2__tmpStar;
x_21 = lean_array_push(x_4, x_20);
x_2 = x_19;
x_3 = x_7;
x_4 = x_21;
x_6 = x_17;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_5__whnfEta___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_8 = l_Lean_Expr_etaExpandedStrict_x3f(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_9; 
lean_free_object(x_4);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_1 = x_9;
x_3 = x_7;
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_11);
x_13 = l_Lean_Expr_etaExpandedStrict_x3f(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_1 = x_15;
x_3 = x_12;
goto _start;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_5__whnfEta(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_DiscrTree_5__whnfEta___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("zero");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("add");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasAdd");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__8;
x_2 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__2;
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__4;
x_5 = lean_name_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__6;
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__9;
x_9 = lean_name_eq(x_1, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 1;
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
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_7__pushArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Init_Lean_Meta_DiscrTree_5__whnfEta___main(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Expr_getAppFn___main(x_7);
switch (lean_obj_tag(x_9)) {
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_free_object(x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux___main(x_7, x_11);
lean_inc(x_12);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_inc(x_3);
lean_inc(x_12);
x_14 = l_Lean_Meta_getFunInfoNArgs(x_9, x_12, x_3, x_8);
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
x_20 = l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___main(x_17, x_19, x_7, x_1, x_3, x_16);
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
lean_dec(x_7);
lean_dec(x_3);
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
case 2:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; 
lean_dec(x_7);
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
lean_dec(x_9);
x_37 = l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId;
x_38 = lean_name_eq(x_36, x_37);
x_39 = l_coeDecidableEq(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_free_object(x_5);
x_40 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(x_36, x_3, x_8);
lean_dec(x_3);
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = lean_box(3);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_1);
lean_ctor_set(x_40, 0, x_46);
return x_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_box(3);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_1);
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
lean_dec(x_52);
x_53 = lean_box(4);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_1);
lean_ctor_set(x_40, 0, x_54);
return x_40;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_dec(x_40);
x_56 = lean_box(4);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_1);
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
lean_dec(x_1);
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
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_36);
lean_dec(x_3);
x_63 = lean_box(3);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_1);
lean_ctor_set(x_5, 0, x_64);
return x_5;
}
}
case 4:
{
lean_object* x_65; uint8_t x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_9, 0);
lean_inc(x_65);
x_66 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar(x_65);
x_67 = l_coeDecidableEq(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_5);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_Expr_getAppNumArgsAux___main(x_7, x_68);
lean_inc(x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
lean_inc(x_3);
lean_inc(x_69);
x_71 = l_Lean_Meta_getFunInfoNArgs(x_9, x_69, x_3, x_8);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_69, x_75);
lean_dec(x_69);
x_77 = l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___main(x_74, x_76, x_7, x_1, x_3, x_73);
lean_dec(x_74);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_70);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_70);
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_77, 0);
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_77);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_71);
if (x_89 == 0)
{
return x_71;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_71, 0);
x_91 = lean_ctor_get(x_71, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_71);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_65);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
x_93 = lean_box(3);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_1);
lean_ctor_set(x_5, 0, x_94);
return x_5;
}
}
case 9:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_7);
lean_dec(x_3);
x_95 = lean_ctor_get(x_9, 0);
lean_inc(x_95);
lean_dec(x_9);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_1);
lean_ctor_set(x_5, 0, x_97);
return x_5;
}
default: 
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
x_98 = lean_box(4);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_1);
lean_ctor_set(x_5, 0, x_99);
return x_5;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_5, 0);
x_101 = lean_ctor_get(x_5, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_5);
x_102 = l_Lean_Expr_getAppFn___main(x_100);
switch (lean_obj_tag(x_102)) {
case 1:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Lean_Expr_getAppNumArgsAux___main(x_100, x_104);
lean_inc(x_105);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_3);
lean_inc(x_105);
x_107 = l_Lean_Meta_getFunInfoNArgs(x_102, x_105, x_3, x_101);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_sub(x_105, x_111);
lean_dec(x_105);
x_113 = l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___main(x_110, x_112, x_100, x_1, x_3, x_109);
lean_dec(x_110);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_106);
lean_ctor_set(x_117, 1, x_114);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_106);
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_3);
lean_dec(x_1);
x_123 = lean_ctor_get(x_107, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_107, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_125 = x_107;
} else {
 lean_dec_ref(x_107);
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
case 2:
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_130; 
lean_dec(x_100);
x_127 = lean_ctor_get(x_102, 0);
lean_inc(x_127);
lean_dec(x_102);
x_128 = l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId;
x_129 = lean_name_eq(x_127, x_128);
x_130 = l_coeDecidableEq(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(x_127, x_3, x_101);
lean_dec(x_3);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_135 = x_131;
} else {
 lean_dec_ref(x_131);
 x_135 = lean_box(0);
}
x_136 = lean_box(3);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_1);
if (lean_is_scalar(x_135)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_135;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_134);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_131, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_140 = x_131;
} else {
 lean_dec_ref(x_131);
 x_140 = lean_box(0);
}
x_141 = lean_box(4);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_1);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_139);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_1);
x_144 = lean_ctor_get(x_131, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_131, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_146 = x_131;
} else {
 lean_dec_ref(x_131);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_127);
lean_dec(x_3);
x_148 = lean_box(3);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_1);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_101);
return x_150;
}
}
case 4:
{
lean_object* x_151; uint8_t x_152; uint8_t x_153; 
x_151 = lean_ctor_get(x_102, 0);
lean_inc(x_151);
x_152 = l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar(x_151);
x_153 = l_coeDecidableEq(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_unsigned_to_nat(0u);
x_155 = l_Lean_Expr_getAppNumArgsAux___main(x_100, x_154);
lean_inc(x_155);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_151);
lean_ctor_set(x_156, 1, x_155);
lean_inc(x_3);
lean_inc(x_155);
x_157 = l_Lean_Meta_getFunInfoNArgs(x_102, x_155, x_3, x_101);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_nat_sub(x_155, x_161);
lean_dec(x_155);
x_163 = l___private_Init_Lean_Meta_DiscrTree_4__pushArgsAux___main(x_160, x_162, x_100, x_1, x_3, x_159);
lean_dec(x_160);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_156);
lean_ctor_set(x_167, 1, x_164);
if (lean_is_scalar(x_166)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_166;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_165);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_156);
x_169 = lean_ctor_get(x_163, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_163, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_171 = x_163;
} else {
 lean_dec_ref(x_163);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_100);
lean_dec(x_3);
lean_dec(x_1);
x_173 = lean_ctor_get(x_157, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_157, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_175 = x_157;
} else {
 lean_dec_ref(x_157);
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
lean_dec(x_151);
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_3);
x_177 = lean_box(3);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_1);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_101);
return x_179;
}
}
case 9:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_100);
lean_dec(x_3);
x_180 = lean_ctor_get(x_102, 0);
lean_inc(x_180);
lean_dec(x_102);
x_181 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_1);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_101);
return x_183;
}
default: 
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_3);
x_184 = lean_box(4);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_1);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_101);
return x_186;
}
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_3);
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_5);
if (x_187 == 0)
{
return x_5;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_5, 0);
x_189 = lean_ctor_get(x_5, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_5);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
}
lean_object* l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Expr_Inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_DiscrTree_mkPathAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; 
x_5 = l_Array_isEmpty___rarg(x_1);
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___main___spec__1(x_1);
x_8 = lean_array_pop(x_1);
lean_inc(x_3);
x_9 = l___private_Init_Lean_Meta_DiscrTree_7__pushArgs(x_8, x_7, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_array_push(x_2, x_12);
x_1 = x_13;
x_2 = x_14;
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
}
lean_object* l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___main___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___main___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_mkPathAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_DiscrTree_mkPathAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_8__initCapacity() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(8u);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_mkPath___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_DiscrTree_8__initCapacity;
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Meta_DiscrTree_mkPath___closed__1;
x_5 = lean_array_push(x_4, x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
x_9 = 2;
lean_ctor_set_uint8(x_7, sizeof(void*)*1 + 6, x_9);
x_10 = l_Lean_Meta_DiscrTree_mkPathAux___main(x_5, x_4, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_13 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 1);
x_14 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 2);
x_15 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 3);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 4);
x_17 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 5);
lean_inc(x_11);
lean_dec(x_7);
x_18 = 2;
x_19 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_12);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 2, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 3, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 4, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 5, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 6, x_18);
lean_ctor_set(x_2, 0, x_19);
x_20 = l_Lean_Meta_DiscrTree_mkPathAux___main(x_5, x_4, x_2, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
x_25 = lean_ctor_get(x_2, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
x_28 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 1);
x_29 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 2);
x_30 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 3);
x_31 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 4);
x_32 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_33 = x_21;
} else {
 lean_dec_ref(x_21);
 x_33 = lean_box(0);
}
x_34 = 2;
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 1, 7);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_27);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 1, x_28);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 2, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 3, x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 4, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 5, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 6, x_34);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_24);
lean_ctor_set(x_36, 4, x_25);
x_37 = l_Lean_Meta_DiscrTree_mkPathAux___main(x_5, x_4, x_36, x_3);
return x_37;
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_mkOptionalNode___closed__2;
x_7 = lean_array_push(x_6, x_2);
x_8 = l_Array_empty___closed__1;
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
x_13 = l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg(x_1, x_2, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_mkOptionalNode___closed__2;
x_16 = lean_array_push(x_15, x_14);
x_17 = l_Array_empty___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_DiscrTree_9__createNodes___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_9__createNodes___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_DiscrTree_9__createNodes___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_10__insertVal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; 
lean_inc(x_3);
x_4 = l_Array_contains___rarg(x_1, x_2, x_3);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_push(x_2, x_3);
return x_6;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_10__insertVal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_DiscrTree_10__insertVal___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_Trie_inhabited(lean_box(0));
return x_1;
}
}
lean_object* _init_l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_DiscrTree_Key_inhabited;
x_2 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_10 = lean_nat_add(x_8, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
x_13 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_14 = lean_array_get(x_13, x_6, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_7, 0);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_15, x_16);
x_18 = l_coeDecidableEq(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; 
lean_dec(x_9);
x_20 = l_Lean_Meta_DiscrTree_Key_lt(x_16, x_15);
lean_dec(x_15);
x_21 = l_coeDecidableEq(x_20);
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_8);
x_23 = lean_array_get_size(x_6);
x_24 = lean_nat_dec_lt(x_12, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_array_fget(x_6, x_12);
x_26 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__3;
x_27 = lean_array_fset(x_6, x_12, x_26);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_4, x_31);
x_33 = l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg(x_1, x_2, x_3, x_32, x_29);
lean_dec(x_32);
lean_ctor_set(x_25, 1, x_33);
lean_ctor_set(x_25, 0, x_5);
x_34 = lean_array_fset(x_27, x_12, x_25);
lean_dec(x_12);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_4, x_36);
x_38 = l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg(x_1, x_2, x_3, x_37, x_35);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_fset(x_27, x_12, x_39);
lean_dec(x_12);
return x_40;
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
uint8_t x_42; uint8_t x_43; 
lean_dec(x_15);
x_42 = lean_nat_dec_eq(x_12, x_8);
x_43 = l_coeDecidableEq(x_42);
if (x_43 == 0)
{
lean_dec(x_8);
x_8 = x_12;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_1);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_4, x_45);
x_47 = l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg(x_2, x_3, x_46);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_nat_add(x_8, x_45);
lean_dec(x_8);
x_50 = l_Array_insertAt___rarg(x_6, x_49, x_48);
lean_dec(x_49);
return x_50;
}
}
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Array_back___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__3___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_back___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_back___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__3___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Array_binInsertM___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_34; uint8_t x_71; uint8_t x_72; 
x_71 = l_Array_isEmpty___rarg(x_6);
x_72 = l_coeDecidableEq(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; 
x_73 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_get(x_73, x_6, x_74);
x_76 = lean_ctor_get(x_7, 0);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Meta_DiscrTree_Key_lt(x_76, x_77);
x_79 = l_coeDecidableEq(x_78);
x_80 = l_coeDecidableEq(x_79);
if (x_80 == 0)
{
uint8_t x_81; uint8_t x_82; 
x_81 = l_Lean_Meta_DiscrTree_Key_lt(x_77, x_76);
lean_dec(x_77);
x_82 = l_coeDecidableEq(x_81);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = 1;
x_34 = x_83;
goto block_70;
}
else
{
uint8_t x_84; 
x_84 = 0;
x_34 = x_84;
goto block_70;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_77);
lean_dec(x_1);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_4, x_85);
x_87 = l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg(x_2, x_3, x_86);
lean_dec(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_5);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Array_insertAt___rarg(x_6, x_74, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_1);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_4, x_90);
x_92 = l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg(x_2, x_3, x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_5);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_array_push(x_6, x_93);
return x_94;
}
block_33:
{
uint8_t x_9; 
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_get_size(x_6);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
x_18 = lean_nat_dec_lt(x_17, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_array_fget(x_6, x_17);
x_20 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__3;
x_21 = lean_array_fset(x_6, x_17, x_20);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = lean_nat_add(x_4, x_16);
x_26 = l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg(x_1, x_2, x_3, x_25, x_23);
lean_dec(x_25);
lean_ctor_set(x_19, 1, x_26);
lean_ctor_set(x_19, 0, x_5);
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
x_29 = lean_nat_add(x_4, x_16);
x_30 = l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg(x_1, x_2, x_3, x_29, x_28);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_fset(x_21, x_17, x_31);
lean_dec(x_17);
return x_32;
}
}
}
}
block_70:
{
uint8_t x_35; 
x_35 = l_coeDecidableEq(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; 
x_36 = l_Array_back___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__3___rarg(x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_7, 0);
x_39 = l_Lean_Meta_DiscrTree_Key_lt(x_37, x_38);
x_40 = l_coeDecidableEq(x_39);
x_41 = l_coeDecidableEq(x_40);
if (x_41 == 0)
{
uint8_t x_42; uint8_t x_43; 
x_42 = l_Lean_Meta_DiscrTree_Key_lt(x_38, x_37);
lean_dec(x_37);
x_43 = l_coeDecidableEq(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = 1;
x_8 = x_44;
goto block_33;
}
else
{
uint8_t x_45; 
x_45 = 0;
x_8 = x_45;
goto block_33;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_37);
lean_dec(x_1);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_4, x_46);
x_48 = l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg(x_2, x_3, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_push(x_6, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_array_get_size(x_6);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_lt(x_52, x_51);
lean_dec(x_51);
if (x_53 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_array_fget(x_6, x_52);
x_55 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__3;
x_56 = lean_array_fset(x_6, x_52, x_55);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_54, 1);
x_59 = lean_ctor_get(x_54, 0);
lean_dec(x_59);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_4, x_60);
x_62 = l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg(x_1, x_2, x_3, x_61, x_58);
lean_dec(x_61);
lean_ctor_set(x_54, 1, x_62);
lean_ctor_set(x_54, 0, x_5);
x_63 = lean_array_fset(x_56, x_52, x_54);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_dec(x_54);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_4, x_65);
x_67 = l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg(x_1, x_2, x_3, x_66, x_64);
lean_dec(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_5);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_array_fset(x_56, x_52, x_68);
return x_69;
}
}
}
}
}
}
lean_object* l_Array_binInsertM___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binInsertM___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l___private_Init_Lean_Meta_DiscrTree_10__insertVal___rarg(x_1, x_7, x_3);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_fget(x_2, x_4);
x_13 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Array_binInsertM___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_12, x_8, x_14);
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
x_20 = l___private_Init_Lean_Meta_DiscrTree_10__insertVal___rarg(x_1, x_16, x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_array_fget(x_2, x_4);
x_23 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
lean_inc(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Array_binInsertM___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_22, x_17, x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_back___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__3___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__3___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_binInsertM___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_binInsertM___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_DiscrTree_11__insertAux___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_11__insertAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_DiscrTree_11__insertAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l_Lean_Meta_DiscrTree_Key_beq(x_5, x_9);
lean_dec(x_9);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_DiscrTree_Key_beq(x_3, x_11);
lean_dec(x_11);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = x_2 >> x_5;
x_1 = x_17;
x_2 = x_18;
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
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(x_21, x_22, lean_box(0), x_23, x_3);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = l_Lean_Meta_DiscrTree_Key_beq(x_3, x_17);
lean_dec(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_2 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_26 = lean_array_fset(x_5, x_2, x_3);
x_27 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_28 = lean_array_fset(x_5, x_2, x_3);
x_29 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Meta_DiscrTree_Key_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
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
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = l_Lean_Meta_DiscrTree_Key_beq(x_4, x_19);
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_15);
x_23 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_array_fset(x_17, x_12, x_24);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_26 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = l_Lean_Meta_DiscrTree_Key_beq(x_4, x_27);
x_30 = l_coeDecidableEq(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_PersistentHashMap_mkCollisionNode___rarg(x_27, x_28, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_35 = lean_array_fset(x_17, x_12, x_34);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
}
}
case 1:
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = x_2 >> x_9;
x_39 = x_3 + x_8;
x_40 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_37, x_38, x_39, x_4, x_5);
lean_ctor_set(x_15, 0, x_40);
x_41 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_41);
return x_1;
}
else
{
lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
lean_dec(x_15);
x_43 = x_2 >> x_9;
x_44 = x_3 + x_8;
x_45 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_42, x_43, x_44, x_4, x_5);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_49 = lean_array_fset(x_17, x_12, x_48);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_49);
return x_1;
}
}
}
}
else
{
lean_object* x_50; size_t x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_dec(x_1);
x_51 = 1;
x_52 = 5;
x_53 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_54 = x_2 & x_53;
x_55 = lean_usize_to_nat(x_54);
x_56 = lean_array_get_size(x_50);
x_57 = lean_nat_dec_lt(x_55, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_4);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_50);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_array_fget(x_50, x_55);
x_60 = lean_box(2);
x_61 = lean_array_fset(x_50, x_55, x_60);
switch (lean_obj_tag(x_59)) {
case 0:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_64 = x_59;
} else {
 lean_dec_ref(x_59);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Meta_DiscrTree_Key_beq(x_4, x_62);
x_66 = l_coeDecidableEq(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_64);
x_67 = l_PersistentHashMap_mkCollisionNode___rarg(x_62, x_63, x_4, x_5);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_array_fset(x_61, x_55, x_68);
lean_dec(x_55);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
lean_dec(x_62);
if (lean_is_scalar(x_64)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_64;
}
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_5);
x_72 = lean_array_fset(x_61, x_55, x_71);
lean_dec(x_55);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
case 1:
{
lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_59, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_75 = x_59;
} else {
 lean_dec_ref(x_59);
 x_75 = lean_box(0);
}
x_76 = x_2 >> x_52;
x_77 = x_3 + x_51;
x_78 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_74, x_76, x_77, x_4, x_5);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_array_fset(x_61, x_55, x_79);
lean_dec(x_55);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
default: 
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_4);
lean_ctor_set(x_82, 1, x_5);
x_83 = lean_array_fset(x_61, x_55, x_82);
lean_dec(x_55);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; size_t x_94; uint8_t x_95; 
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__6___rarg(x_1, x_85, x_4, x_5);
x_94 = 7;
x_95 = x_94 <= x_3;
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_86);
x_97 = lean_unsigned_to_nat(4u);
x_98 = lean_nat_dec_lt(x_96, x_97);
lean_dec(x_96);
x_87 = x_98;
goto block_93;
}
else
{
uint8_t x_99; 
x_99 = 1;
x_87 = x_99;
goto block_93;
}
block_93:
{
uint8_t x_88; 
x_88 = l_coeDecidableEq(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(x_3, x_89, x_90, x_89, x_85, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_86;
}
}
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = l_Lean_Meta_DiscrTree_Key_beq(x_3, x_17);
lean_dec(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_2 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_26 = lean_array_fset(x_5, x_2, x_3);
x_27 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_28 = lean_array_fset(x_5, x_2, x_3);
x_29 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Meta_DiscrTree_Key_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
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
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = l_Lean_Meta_DiscrTree_Key_beq(x_4, x_19);
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_15);
x_23 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_array_fset(x_17, x_12, x_24);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_26 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = l_Lean_Meta_DiscrTree_Key_beq(x_4, x_27);
x_30 = l_coeDecidableEq(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_PersistentHashMap_mkCollisionNode___rarg(x_27, x_28, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_35 = lean_array_fset(x_17, x_12, x_34);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
}
}
case 1:
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = x_2 >> x_9;
x_39 = x_3 + x_8;
x_40 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_37, x_38, x_39, x_4, x_5);
lean_ctor_set(x_15, 0, x_40);
x_41 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_41);
return x_1;
}
else
{
lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
lean_dec(x_15);
x_43 = x_2 >> x_9;
x_44 = x_3 + x_8;
x_45 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_42, x_43, x_44, x_4, x_5);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_49 = lean_array_fset(x_17, x_12, x_48);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_49);
return x_1;
}
}
}
}
else
{
lean_object* x_50; size_t x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_dec(x_1);
x_51 = 1;
x_52 = 5;
x_53 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_54 = x_2 & x_53;
x_55 = lean_usize_to_nat(x_54);
x_56 = lean_array_get_size(x_50);
x_57 = lean_nat_dec_lt(x_55, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_4);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_50);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_array_fget(x_50, x_55);
x_60 = lean_box(2);
x_61 = lean_array_fset(x_50, x_55, x_60);
switch (lean_obj_tag(x_59)) {
case 0:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_64 = x_59;
} else {
 lean_dec_ref(x_59);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Meta_DiscrTree_Key_beq(x_4, x_62);
x_66 = l_coeDecidableEq(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_64);
x_67 = l_PersistentHashMap_mkCollisionNode___rarg(x_62, x_63, x_4, x_5);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_array_fset(x_61, x_55, x_68);
lean_dec(x_55);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
lean_dec(x_62);
if (lean_is_scalar(x_64)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_64;
}
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_5);
x_72 = lean_array_fset(x_61, x_55, x_71);
lean_dec(x_55);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
case 1:
{
lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_59, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_75 = x_59;
} else {
 lean_dec_ref(x_59);
 x_75 = lean_box(0);
}
x_76 = x_2 >> x_52;
x_77 = x_3 + x_51;
x_78 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_74, x_76, x_77, x_4, x_5);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_array_fset(x_61, x_55, x_79);
lean_dec(x_55);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
default: 
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_4);
lean_ctor_set(x_82, 1, x_5);
x_83 = lean_array_fset(x_61, x_55, x_82);
lean_dec(x_55);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; size_t x_94; uint8_t x_95; 
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__10___rarg(x_1, x_85, x_4, x_5);
x_94 = 7;
x_95 = x_94 <= x_3;
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_86);
x_97 = lean_unsigned_to_nat(4u);
x_98 = lean_nat_dec_lt(x_96, x_97);
lean_dec(x_96);
x_87 = x_98;
goto block_93;
}
else
{
uint8_t x_99; 
x_99 = 1;
x_87 = x_99;
goto block_93;
}
block_93:
{
uint8_t x_88; 
x_88 = l_coeDecidableEq(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(x_3, x_89, x_90, x_89, x_85, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_86;
}
}
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_Inhabited(lean_box(0));
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.Meta.DiscrTree");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid key sequence");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2;
x_2 = lean_unsigned_to_nat(228u);
x_3 = lean_unsigned_to_nat(21u);
x_4 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_DiscrTree_insertCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; 
x_5 = l_Array_isEmpty___rarg(x_3);
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_DiscrTree_Key_inhabited;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get(x_7, x_3, x_8);
lean_inc(x_2);
x_10 = l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg(x_2, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l___private_Init_Lean_Meta_DiscrTree_9__createNodes___main___rarg(x_3, x_4, x_11);
x_13 = l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__4___rarg(x_2, x_9, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___rarg(x_1, x_3, x_4, x_15, x_14);
x_17 = l_PersistentHashMap_insert___at_Lean_Meta_DiscrTree_insertCore___spec__8___rarg(x_2, x_9, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1;
x_19 = l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4;
x_20 = lean_panic_fn(x_18, x_19);
return x_20;
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
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__2___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_insertCore___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__7___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__5___rarg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__11___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_DiscrTree_insertCore___spec__9___rarg(x_1, x_6, x_7, x_4, x_5);
return x_8;
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
lean_object* l_Lean_Meta_DiscrTree_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_DiscrTree_mkPath(x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Meta_DiscrTree_insertCore___rarg(x_1, x_2, x_9, x_4);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l_Lean_Meta_DiscrTree_insertCore___rarg(x_1, x_2, x_11, x_4);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_insert___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_Key_format(x_1);
return x_2;
}
}
lean_object* _init_l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" => ");
return x_1;
}
}
lean_object* _init_l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg(x_1, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_Meta_DiscrTree_Key_format(x_8);
x_11 = 0;
x_12 = l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2;
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_11);
x_14 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg(x_1, x_9);
lean_dec(x_9);
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_11);
x_16 = l_Lean_Format_paren___closed__2;
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_11);
x_18 = l_Lean_Format_paren___closed__3;
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_11);
x_20 = l_Lean_Format_paren___closed__1;
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_format_group(x_21);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_11);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_24);
return x_2;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
x_27 = l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg(x_1, x_26);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Meta_DiscrTree_Key_format(x_28);
x_31 = 0;
x_32 = l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2;
x_33 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_31);
x_34 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg(x_1, x_29);
lean_dec(x_29);
x_35 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_31);
x_36 = l_Lean_Format_paren___closed__2;
x_37 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_31);
x_38 = l_Lean_Format_paren___closed__3;
x_39 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_31);
x_40 = l_Lean_Format_paren___closed__1;
x_41 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_format_group(x_41);
x_43 = lean_box(1);
x_44 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_31);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_27);
return x_45;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_List_format___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Array_toList___rarg(x_2);
x_4 = l_Lean_List_format___rarg(x_1, x_3);
x_5 = 0;
x_6 = l_Lean_arrayHasFormat___rarg___closed__1;
x_7 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_5);
return x_7;
}
}
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("node");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__2;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_format___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Array_isEmpty___rarg(x_3);
x_6 = l_coeDecidableEq(x_5);
x_7 = l_Array_toList___rarg(x_4);
lean_inc(x_1);
x_8 = l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg(x_1, x_7);
x_9 = l_Lean_Format_join(x_8);
lean_dec(x_8);
if (x_6 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__3___rarg(x_1, x_3);
x_11 = 0;
x_12 = l_Lean_Format_flatten___main___closed__1;
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_11);
x_14 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__2;
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_11);
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_11);
x_17 = l_Lean_Format_paren___closed__2;
x_18 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_11);
x_19 = l_Lean_Format_paren___closed__3;
x_20 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_11);
x_21 = l_Lean_Format_paren___closed__1;
x_22 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_format_group(x_22);
x_24 = lean_format_group(x_23);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_25 = 0;
x_26 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__3;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_25);
x_28 = l_Lean_Format_paren___closed__2;
x_29 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_25);
x_30 = l_Lean_Format_paren___closed__3;
x_31 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_25);
x_32 = l_Lean_Format_paren___closed__1;
x_33 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_format_group(x_33);
x_35 = lean_format_group(x_34);
return x_35;
}
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_format___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format___main___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_fmt___at_Lean_Meta_DiscrTree_Trie_format___main___spec__3___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_format___main___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DiscrTree_Trie_format___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_hasFormat___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_Trie_hasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_hasFormat___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_format___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_fmt___at_Lean_Meta_DiscrTree_format___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_unbox(x_14);
lean_dec(x_14);
x_17 = l_coeDecidableEq(x_16);
x_18 = l_Lean_Meta_DiscrTree_Key_format(x_11);
x_19 = 0;
x_20 = l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2;
x_21 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_19);
lean_inc(x_1);
x_22 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg(x_1, x_12);
lean_dec(x_12);
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_19);
x_24 = l_Lean_Format_paren___closed__2;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_19);
x_26 = l_Lean_Format_paren___closed__3;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_19);
x_28 = l_Lean_Format_paren___closed__1;
x_29 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_format_group(x_29);
if (x_17 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_19);
x_33 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_19);
x_34 = lean_box(x_19);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_34);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_19);
x_38 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_19);
x_39 = lean_box(x_19);
lean_ctor_set(x_5, 1, x_38);
lean_ctor_set(x_5, 0, x_39);
x_4 = x_10;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_41 = lean_ctor_get(x_5, 0);
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_5);
x_43 = lean_unbox(x_41);
lean_dec(x_41);
x_44 = l_coeDecidableEq(x_43);
x_45 = l_Lean_Meta_DiscrTree_Key_format(x_11);
x_46 = 0;
x_47 = l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2;
x_48 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_46);
lean_inc(x_1);
x_49 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg(x_1, x_12);
lean_dec(x_12);
x_50 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_46);
x_51 = l_Lean_Format_paren___closed__2;
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_46);
x_53 = l_Lean_Format_paren___closed__3;
x_54 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_46);
x_55 = l_Lean_Format_paren___closed__1;
x_56 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_format_group(x_56);
if (x_44 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_box(1);
x_59 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_59, 0, x_42);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_46);
x_60 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_46);
x_61 = lean_box(x_46);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_4 = x_10;
x_5 = x_62;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_65, 0, x_42);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_46);
x_66 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_57);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_46);
x_67 = lean_box(x_46);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_4 = x_10;
x_5 = x_68;
goto _start;
}
}
}
case 1:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_8, 0);
lean_inc(x_70);
lean_dec(x_8);
lean_inc(x_1);
x_71 = l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_format___spec__3___rarg(x_1, x_70, x_5);
lean_dec(x_70);
x_4 = x_10;
x_5 = x_71;
goto _start;
}
default: 
{
x_4 = x_10;
goto _start;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_unbox(x_12);
lean_dec(x_12);
x_15 = l_coeDecidableEq(x_14);
x_16 = l_Lean_Meta_DiscrTree_Key_format(x_9);
x_17 = 0;
x_18 = l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2;
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_17);
lean_inc(x_1);
x_20 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg(x_1, x_10);
lean_dec(x_10);
x_21 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_17);
x_22 = l_Lean_Format_paren___closed__2;
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_17);
x_24 = l_Lean_Format_paren___closed__3;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_17);
x_26 = l_Lean_Format_paren___closed__1;
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_format_group(x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
if (x_15 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_17);
x_33 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_17);
x_34 = lean_box(x_17);
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_34);
x_5 = x_30;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_37, 0, x_13);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_17);
x_38 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_17);
x_39 = lean_box(x_17);
lean_ctor_set(x_6, 1, x_38);
lean_ctor_set(x_6, 0, x_39);
x_5 = x_30;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_41 = lean_ctor_get(x_6, 0);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_43 = lean_unbox(x_41);
lean_dec(x_41);
x_44 = l_coeDecidableEq(x_43);
x_45 = l_Lean_Meta_DiscrTree_Key_format(x_9);
x_46 = 0;
x_47 = l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2;
x_48 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_46);
lean_inc(x_1);
x_49 = l_Lean_Meta_DiscrTree_Trie_format___main___rarg(x_1, x_10);
lean_dec(x_10);
x_50 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_46);
x_51 = l_Lean_Format_paren___closed__2;
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_46);
x_53 = l_Lean_Format_paren___closed__3;
x_54 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_46);
x_55 = l_Lean_Format_paren___closed__1;
x_56 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_format_group(x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_5, x_58);
lean_dec(x_5);
if (x_44 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_box(1);
x_61 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_61, 0, x_42);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_46);
x_62 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_46);
x_63 = lean_box(x_46);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_5 = x_59;
x_6 = x_64;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_67, 0, x_42);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_46);
x_68 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_57);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_46);
x_69 = lean_box(x_46);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_5 = x_59;
x_6 = x_70;
goto _start;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__5___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_format___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__4___rarg(x_1, x_4, x_4, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__5___rarg(x_1, x_7, x_8, x_7, x_9, x_3);
return x_10;
}
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_format___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_format___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_format___spec__3___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DiscrTree_format___rarg___closed__1() {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Meta_DiscrTree_format___rarg___closed__1;
x_4 = l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__2___rarg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_format_group(x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_DiscrTree_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_fmt___at_Lean_Meta_DiscrTree_format___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_fmt___at_Lean_Meta_DiscrTree_format___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_format___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_format___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_format___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_format___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_DiscrTree_format___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DiscrTree_format___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_DiscrTree_DiscrTree_hasFormat___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_DiscrTree_hasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_DiscrTree_hasFormat___rarg), 1, 0);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(4);
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Init_Lean_Meta_DiscrTree_5__whnfEta___main(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Expr_getAppFn___main(x_7);
switch (lean_obj_tag(x_9)) {
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux___main(x_7, x_11);
lean_inc(x_12);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_empty_array_with_capacity(x_12);
lean_dec(x_12);
x_15 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_7, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
case 2:
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_7);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l_coeDecidableEq(x_2);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 4);
lean_dec(x_19);
x_21 = l_coeDecidableEq(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_5);
x_22 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(x_17, x_3, x_8);
lean_dec(x_3);
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
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__2;
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__2;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_22, 0);
lean_dec(x_32);
x_33 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1;
lean_ctor_set(x_22, 0, x_33);
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_22);
if (x_37 == 0)
{
return x_22;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_17);
lean_dec(x_3);
x_41 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__2;
lean_ctor_set(x_5, 0, x_41);
return x_5;
}
}
else
{
lean_object* x_42; 
lean_dec(x_17);
lean_dec(x_3);
x_42 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1;
lean_ctor_set(x_5, 0, x_42);
return x_5;
}
}
case 4:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
x_43 = lean_ctor_get(x_9, 0);
lean_inc(x_43);
lean_dec(x_9);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Lean_Expr_getAppNumArgsAux___main(x_7, x_44);
lean_inc(x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_empty_array_with_capacity(x_45);
lean_dec(x_45);
x_48 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_7, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_5, 0, x_49);
return x_5;
}
case 9:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_3);
x_50 = lean_ctor_get(x_9, 0);
lean_inc(x_50);
lean_dec(x_9);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Array_empty___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_5, 0, x_53);
return x_5;
}
default: 
{
lean_object* x_54; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
x_54 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1;
lean_ctor_set(x_5, 0, x_54);
return x_5;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = lean_ctor_get(x_5, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_5);
x_57 = l_Lean_Expr_getAppFn___main(x_55);
switch (lean_obj_tag(x_57)) {
case 1:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_3);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lean_Expr_getAppNumArgsAux___main(x_55, x_59);
lean_inc(x_60);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_mk_empty_array_with_capacity(x_60);
lean_dec(x_60);
x_63 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_55, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_56);
return x_65;
}
case 2:
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_55);
x_66 = lean_ctor_get(x_57, 0);
lean_inc(x_66);
lean_dec(x_57);
x_67 = l_coeDecidableEq(x_2);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_3, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_68, sizeof(void*)*1 + 4);
lean_dec(x_68);
x_70 = l_coeDecidableEq(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = l_Lean_Meta_isReadOnlyOrSyntheticOpaqueExprMVar(x_66, x_3, x_56);
lean_dec(x_3);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
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
x_76 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__2;
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_79 = x_71;
} else {
 lean_dec_ref(x_71);
 x_79 = lean_box(0);
}
x_80 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1;
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_71, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_71, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_84 = x_71;
} else {
 lean_dec_ref(x_71);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_66);
lean_dec(x_3);
x_86 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__2;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_56);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_66);
lean_dec(x_3);
x_88 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_56);
return x_89;
}
}
case 4:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_3);
x_90 = lean_ctor_get(x_57, 0);
lean_inc(x_90);
lean_dec(x_57);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Lean_Expr_getAppNumArgsAux___main(x_55, x_91);
lean_inc(x_92);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_mk_empty_array_with_capacity(x_92);
lean_dec(x_92);
x_95 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_55, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_56);
return x_97;
}
case 9:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_55);
lean_dec(x_3);
x_98 = lean_ctor_get(x_57, 0);
lean_inc(x_98);
lean_dec(x_57);
x_99 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = l_Array_empty___closed__1;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_56);
return x_102;
}
default: 
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_3);
x_103 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1;
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_56);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_5);
if (x_105 == 0)
{
return x_5;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_5, 0);
x_107 = lean_ctor_get(x_5, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_5);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_13__getMatchKeyArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_14__getUnifyKeyArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
x_15 = l_coeDecidableEq(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_4);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
x_18 = l_coeDecidableEq(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_9, x_21);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_9, x_24);
lean_dec(x_9);
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_3);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
x_3 = x_29;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
x_15 = l_coeDecidableEq(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_4);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
x_18 = l_coeDecidableEq(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_9, x_21);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_9, x_24);
lean_dec(x_9);
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_3);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
x_3 = x_29;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
x_15 = l_coeDecidableEq(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_4);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
x_18 = l_coeDecidableEq(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_9, x_21);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_9, x_24);
lean_dec(x_9);
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_3);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
x_3 = x_29;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
x_15 = l_coeDecidableEq(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_4);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
x_18 = l_coeDecidableEq(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_9, x_21);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_9, x_24);
lean_dec(x_9);
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_3);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
x_3 = x_29;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Array_isEmpty___rarg(x_1);
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
lean_dec(x_6);
x_10 = l_Array_isEmpty___rarg(x_7);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___main___spec__1(x_1);
x_13 = lean_array_pop(x_1);
x_14 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_7, x_15);
x_17 = 1;
lean_inc(x_4);
x_18 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(x_12, x_17, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
switch (lean_obj_tag(x_20)) {
case 0:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_19, 1);
x_26 = lean_ctor_get(x_19, 0);
lean_dec(x_26);
x_27 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
lean_ctor_set(x_19, 1, x_27);
x_28 = lean_array_get_size(x_7);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_28, x_29);
lean_dec(x_28);
x_31 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__1___rarg(x_7, x_19, x_15, x_30);
lean_dec(x_19);
lean_dec(x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
lean_dec(x_25);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
x_33 = lean_box(3);
x_34 = l_Lean_Meta_DiscrTree_Key_beq(x_32, x_33);
lean_dec(x_32);
x_35 = l_coeDecidableEq(x_34);
if (x_35 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
lean_object* x_36; 
lean_free_object(x_18);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_36;
x_5 = x_22;
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
lean_free_object(x_18);
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
lean_dec(x_31);
x_39 = lean_ctor_get(x_16, 0);
lean_inc(x_39);
x_40 = lean_box(3);
x_41 = l_Lean_Meta_DiscrTree_Key_beq(x_39, x_40);
lean_dec(x_39);
x_42 = l_coeDecidableEq(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_16);
x_43 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_25, x_25, x_15, x_13);
lean_dec(x_25);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_1 = x_43;
x_2 = x_44;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_47 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_46, x_3, x_4, x_22);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_25, x_25, x_15, x_13);
lean_dec(x_25);
x_51 = lean_ctor_get(x_38, 1);
lean_inc(x_51);
lean_dec(x_38);
x_1 = x_50;
x_2 = x_51;
x_3 = x_48;
x_5 = x_49;
goto _start;
}
else
{
uint8_t x_53; 
lean_dec(x_38);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_dec(x_19);
x_58 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_20);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_get_size(x_7);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_60, x_61);
lean_dec(x_60);
x_63 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__1___rarg(x_7, x_59, x_15, x_62);
lean_dec(x_59);
lean_dec(x_7);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; 
lean_dec(x_57);
x_64 = lean_ctor_get(x_16, 0);
lean_inc(x_64);
x_65 = lean_box(3);
x_66 = l_Lean_Meta_DiscrTree_Key_beq(x_64, x_65);
lean_dec(x_64);
x_67 = l_coeDecidableEq(x_66);
if (x_67 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
lean_object* x_68; 
lean_free_object(x_18);
x_68 = lean_ctor_get(x_16, 1);
lean_inc(x_68);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_68;
x_5 = x_22;
goto _start;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; 
lean_free_object(x_18);
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_ctor_get(x_16, 0);
lean_inc(x_71);
x_72 = lean_box(3);
x_73 = l_Lean_Meta_DiscrTree_Key_beq(x_71, x_72);
lean_dec(x_71);
x_74 = l_coeDecidableEq(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_16);
x_75 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_57, x_57, x_15, x_13);
lean_dec(x_57);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_1 = x_75;
x_2 = x_76;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_16, 1);
lean_inc(x_78);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_79 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_78, x_3, x_4, x_22);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_57, x_57, x_15, x_13);
lean_dec(x_57);
x_83 = lean_ctor_get(x_70, 1);
lean_inc(x_83);
lean_dec(x_70);
x_1 = x_82;
x_2 = x_83;
x_3 = x_80;
x_5 = x_81;
goto _start;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_70);
lean_dec(x_57);
lean_dec(x_13);
lean_dec(x_4);
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_87 = x_79;
} else {
 lean_dec_ref(x_79);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_89 = lean_ctor_get(x_18, 1);
lean_inc(x_89);
lean_dec(x_18);
x_90 = lean_ctor_get(x_19, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_91 = x_19;
} else {
 lean_dec_ref(x_19);
 x_91 = lean_box(0);
}
x_92 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_20);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_array_get_size(x_7);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_sub(x_94, x_95);
lean_dec(x_94);
x_97 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__1___rarg(x_7, x_93, x_15, x_96);
lean_dec(x_93);
lean_dec(x_7);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; 
lean_dec(x_90);
x_98 = lean_ctor_get(x_16, 0);
lean_inc(x_98);
x_99 = lean_box(3);
x_100 = l_Lean_Meta_DiscrTree_Key_beq(x_98, x_99);
lean_dec(x_98);
x_101 = l_coeDecidableEq(x_100);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_3);
lean_ctor_set(x_102, 1, x_89);
return x_102;
}
else
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_16, 1);
lean_inc(x_103);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_103;
x_5 = x_89;
goto _start;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; 
x_105 = lean_ctor_get(x_97, 0);
lean_inc(x_105);
lean_dec(x_97);
x_106 = lean_ctor_get(x_16, 0);
lean_inc(x_106);
x_107 = lean_box(3);
x_108 = l_Lean_Meta_DiscrTree_Key_beq(x_106, x_107);
lean_dec(x_106);
x_109 = l_coeDecidableEq(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_16);
x_110 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_90, x_90, x_15, x_13);
lean_dec(x_90);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_dec(x_105);
x_1 = x_110;
x_2 = x_111;
x_5 = x_89;
goto _start;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_16, 1);
lean_inc(x_113);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_114 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_113, x_3, x_4, x_89);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_90, x_90, x_15, x_13);
lean_dec(x_90);
x_118 = lean_ctor_get(x_105, 1);
lean_inc(x_118);
lean_dec(x_105);
x_1 = x_117;
x_2 = x_118;
x_3 = x_115;
x_5 = x_116;
goto _start;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_105);
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_4);
x_120 = lean_ctor_get(x_114, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_122 = x_114;
} else {
 lean_dec_ref(x_114);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
}
case 1:
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_18);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_18, 1);
x_126 = lean_ctor_get(x_18, 0);
lean_dec(x_126);
x_127 = !lean_is_exclusive(x_19);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_ctor_get(x_19, 1);
x_129 = lean_ctor_get(x_19, 0);
lean_dec(x_129);
x_130 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
lean_ctor_set(x_19, 1, x_130);
x_131 = lean_array_get_size(x_7);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_nat_sub(x_131, x_132);
lean_dec(x_131);
x_134 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__2___rarg(x_7, x_19, x_15, x_133);
lean_dec(x_19);
lean_dec(x_7);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
lean_dec(x_128);
x_135 = lean_ctor_get(x_16, 0);
lean_inc(x_135);
x_136 = lean_box(3);
x_137 = l_Lean_Meta_DiscrTree_Key_beq(x_135, x_136);
lean_dec(x_135);
x_138 = l_coeDecidableEq(x_137);
if (x_138 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
lean_object* x_139; 
lean_free_object(x_18);
x_139 = lean_ctor_get(x_16, 1);
lean_inc(x_139);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_139;
x_5 = x_125;
goto _start;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; uint8_t x_145; 
lean_free_object(x_18);
x_141 = lean_ctor_get(x_134, 0);
lean_inc(x_141);
lean_dec(x_134);
x_142 = lean_ctor_get(x_16, 0);
lean_inc(x_142);
x_143 = lean_box(3);
x_144 = l_Lean_Meta_DiscrTree_Key_beq(x_142, x_143);
lean_dec(x_142);
x_145 = l_coeDecidableEq(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_16);
x_146 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_128, x_128, x_15, x_13);
lean_dec(x_128);
x_147 = lean_ctor_get(x_141, 1);
lean_inc(x_147);
lean_dec(x_141);
x_1 = x_146;
x_2 = x_147;
x_5 = x_125;
goto _start;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_16, 1);
lean_inc(x_149);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_150 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_149, x_3, x_4, x_125);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_128, x_128, x_15, x_13);
lean_dec(x_128);
x_154 = lean_ctor_get(x_141, 1);
lean_inc(x_154);
lean_dec(x_141);
x_1 = x_153;
x_2 = x_154;
x_3 = x_151;
x_5 = x_152;
goto _start;
}
else
{
uint8_t x_156; 
lean_dec(x_141);
lean_dec(x_128);
lean_dec(x_13);
lean_dec(x_4);
x_156 = !lean_is_exclusive(x_150);
if (x_156 == 0)
{
return x_150;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_150, 0);
x_158 = lean_ctor_get(x_150, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_150);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_160 = lean_ctor_get(x_19, 1);
lean_inc(x_160);
lean_dec(x_19);
x_161 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_20);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_array_get_size(x_7);
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_nat_sub(x_163, x_164);
lean_dec(x_163);
x_166 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__2___rarg(x_7, x_162, x_15, x_165);
lean_dec(x_162);
lean_dec(x_7);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; 
lean_dec(x_160);
x_167 = lean_ctor_get(x_16, 0);
lean_inc(x_167);
x_168 = lean_box(3);
x_169 = l_Lean_Meta_DiscrTree_Key_beq(x_167, x_168);
lean_dec(x_167);
x_170 = l_coeDecidableEq(x_169);
if (x_170 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
lean_object* x_171; 
lean_free_object(x_18);
x_171 = lean_ctor_get(x_16, 1);
lean_inc(x_171);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_171;
x_5 = x_125;
goto _start;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_177; 
lean_free_object(x_18);
x_173 = lean_ctor_get(x_166, 0);
lean_inc(x_173);
lean_dec(x_166);
x_174 = lean_ctor_get(x_16, 0);
lean_inc(x_174);
x_175 = lean_box(3);
x_176 = l_Lean_Meta_DiscrTree_Key_beq(x_174, x_175);
lean_dec(x_174);
x_177 = l_coeDecidableEq(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_16);
x_178 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_160, x_160, x_15, x_13);
lean_dec(x_160);
x_179 = lean_ctor_get(x_173, 1);
lean_inc(x_179);
lean_dec(x_173);
x_1 = x_178;
x_2 = x_179;
x_5 = x_125;
goto _start;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_16, 1);
lean_inc(x_181);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_182 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_181, x_3, x_4, x_125);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_160, x_160, x_15, x_13);
lean_dec(x_160);
x_186 = lean_ctor_get(x_173, 1);
lean_inc(x_186);
lean_dec(x_173);
x_1 = x_185;
x_2 = x_186;
x_3 = x_183;
x_5 = x_184;
goto _start;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_173);
lean_dec(x_160);
lean_dec(x_13);
lean_dec(x_4);
x_188 = lean_ctor_get(x_182, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_182, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_190 = x_182;
} else {
 lean_dec_ref(x_182);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_192 = lean_ctor_get(x_18, 1);
lean_inc(x_192);
lean_dec(x_18);
x_193 = lean_ctor_get(x_19, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_194 = x_19;
} else {
 lean_dec_ref(x_19);
 x_194 = lean_box(0);
}
x_195 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_20);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_array_get_size(x_7);
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_nat_sub(x_197, x_198);
lean_dec(x_197);
x_200 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__2___rarg(x_7, x_196, x_15, x_199);
lean_dec(x_196);
lean_dec(x_7);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_204; 
lean_dec(x_193);
x_201 = lean_ctor_get(x_16, 0);
lean_inc(x_201);
x_202 = lean_box(3);
x_203 = l_Lean_Meta_DiscrTree_Key_beq(x_201, x_202);
lean_dec(x_201);
x_204 = l_coeDecidableEq(x_203);
if (x_204 == 0)
{
lean_object* x_205; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_3);
lean_ctor_set(x_205, 1, x_192);
return x_205;
}
else
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_16, 1);
lean_inc(x_206);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_206;
x_5 = x_192;
goto _start;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_212; 
x_208 = lean_ctor_get(x_200, 0);
lean_inc(x_208);
lean_dec(x_200);
x_209 = lean_ctor_get(x_16, 0);
lean_inc(x_209);
x_210 = lean_box(3);
x_211 = l_Lean_Meta_DiscrTree_Key_beq(x_209, x_210);
lean_dec(x_209);
x_212 = l_coeDecidableEq(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_16);
x_213 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_193, x_193, x_15, x_13);
lean_dec(x_193);
x_214 = lean_ctor_get(x_208, 1);
lean_inc(x_214);
lean_dec(x_208);
x_1 = x_213;
x_2 = x_214;
x_5 = x_192;
goto _start;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_16, 1);
lean_inc(x_216);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_217 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_216, x_3, x_4, x_192);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_193, x_193, x_15, x_13);
lean_dec(x_193);
x_221 = lean_ctor_get(x_208, 1);
lean_inc(x_221);
lean_dec(x_208);
x_1 = x_220;
x_2 = x_221;
x_3 = x_218;
x_5 = x_219;
goto _start;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_208);
lean_dec(x_193);
lean_dec(x_13);
lean_dec(x_4);
x_223 = lean_ctor_get(x_217, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_217, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_225 = x_217;
} else {
 lean_dec_ref(x_217);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
}
}
}
case 2:
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_18);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_18, 1);
x_229 = lean_ctor_get(x_18, 0);
lean_dec(x_229);
x_230 = !lean_is_exclusive(x_19);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_231 = lean_ctor_get(x_19, 1);
x_232 = lean_ctor_get(x_19, 0);
lean_dec(x_232);
x_233 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
lean_ctor_set(x_19, 1, x_233);
x_234 = lean_array_get_size(x_7);
x_235 = lean_unsigned_to_nat(1u);
x_236 = lean_nat_sub(x_234, x_235);
lean_dec(x_234);
x_237 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__3___rarg(x_7, x_19, x_15, x_236);
lean_dec(x_19);
lean_dec(x_7);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_241; 
lean_dec(x_231);
x_238 = lean_ctor_get(x_16, 0);
lean_inc(x_238);
x_239 = lean_box(3);
x_240 = l_Lean_Meta_DiscrTree_Key_beq(x_238, x_239);
lean_dec(x_238);
x_241 = l_coeDecidableEq(x_240);
if (x_241 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
lean_object* x_242; 
lean_free_object(x_18);
x_242 = lean_ctor_get(x_16, 1);
lean_inc(x_242);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_242;
x_5 = x_228;
goto _start;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; uint8_t x_248; 
lean_free_object(x_18);
x_244 = lean_ctor_get(x_237, 0);
lean_inc(x_244);
lean_dec(x_237);
x_245 = lean_ctor_get(x_16, 0);
lean_inc(x_245);
x_246 = lean_box(3);
x_247 = l_Lean_Meta_DiscrTree_Key_beq(x_245, x_246);
lean_dec(x_245);
x_248 = l_coeDecidableEq(x_247);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_16);
x_249 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_231, x_231, x_15, x_13);
lean_dec(x_231);
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
lean_dec(x_244);
x_1 = x_249;
x_2 = x_250;
x_5 = x_228;
goto _start;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_16, 1);
lean_inc(x_252);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_253 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_252, x_3, x_4, x_228);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_231, x_231, x_15, x_13);
lean_dec(x_231);
x_257 = lean_ctor_get(x_244, 1);
lean_inc(x_257);
lean_dec(x_244);
x_1 = x_256;
x_2 = x_257;
x_3 = x_254;
x_5 = x_255;
goto _start;
}
else
{
uint8_t x_259; 
lean_dec(x_244);
lean_dec(x_231);
lean_dec(x_13);
lean_dec(x_4);
x_259 = !lean_is_exclusive(x_253);
if (x_259 == 0)
{
return x_253;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_253, 0);
x_261 = lean_ctor_get(x_253, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_253);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_263 = lean_ctor_get(x_19, 1);
lean_inc(x_263);
lean_dec(x_19);
x_264 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_20);
lean_ctor_set(x_265, 1, x_264);
x_266 = lean_array_get_size(x_7);
x_267 = lean_unsigned_to_nat(1u);
x_268 = lean_nat_sub(x_266, x_267);
lean_dec(x_266);
x_269 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__3___rarg(x_7, x_265, x_15, x_268);
lean_dec(x_265);
lean_dec(x_7);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_273; 
lean_dec(x_263);
x_270 = lean_ctor_get(x_16, 0);
lean_inc(x_270);
x_271 = lean_box(3);
x_272 = l_Lean_Meta_DiscrTree_Key_beq(x_270, x_271);
lean_dec(x_270);
x_273 = l_coeDecidableEq(x_272);
if (x_273 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
lean_object* x_274; 
lean_free_object(x_18);
x_274 = lean_ctor_get(x_16, 1);
lean_inc(x_274);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_274;
x_5 = x_228;
goto _start;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; uint8_t x_280; 
lean_free_object(x_18);
x_276 = lean_ctor_get(x_269, 0);
lean_inc(x_276);
lean_dec(x_269);
x_277 = lean_ctor_get(x_16, 0);
lean_inc(x_277);
x_278 = lean_box(3);
x_279 = l_Lean_Meta_DiscrTree_Key_beq(x_277, x_278);
lean_dec(x_277);
x_280 = l_coeDecidableEq(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_16);
x_281 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_263, x_263, x_15, x_13);
lean_dec(x_263);
x_282 = lean_ctor_get(x_276, 1);
lean_inc(x_282);
lean_dec(x_276);
x_1 = x_281;
x_2 = x_282;
x_5 = x_228;
goto _start;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_16, 1);
lean_inc(x_284);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_285 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_284, x_3, x_4, x_228);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_263, x_263, x_15, x_13);
lean_dec(x_263);
x_289 = lean_ctor_get(x_276, 1);
lean_inc(x_289);
lean_dec(x_276);
x_1 = x_288;
x_2 = x_289;
x_3 = x_286;
x_5 = x_287;
goto _start;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_276);
lean_dec(x_263);
lean_dec(x_13);
lean_dec(x_4);
x_291 = lean_ctor_get(x_285, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_285, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_293 = x_285;
} else {
 lean_dec_ref(x_285);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
}
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_295 = lean_ctor_get(x_18, 1);
lean_inc(x_295);
lean_dec(x_18);
x_296 = lean_ctor_get(x_19, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_297 = x_19;
} else {
 lean_dec_ref(x_19);
 x_297 = lean_box(0);
}
x_298 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
if (lean_is_scalar(x_297)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_297;
}
lean_ctor_set(x_299, 0, x_20);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_array_get_size(x_7);
x_301 = lean_unsigned_to_nat(1u);
x_302 = lean_nat_sub(x_300, x_301);
lean_dec(x_300);
x_303 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__3___rarg(x_7, x_299, x_15, x_302);
lean_dec(x_299);
lean_dec(x_7);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; uint8_t x_307; 
lean_dec(x_296);
x_304 = lean_ctor_get(x_16, 0);
lean_inc(x_304);
x_305 = lean_box(3);
x_306 = l_Lean_Meta_DiscrTree_Key_beq(x_304, x_305);
lean_dec(x_304);
x_307 = l_coeDecidableEq(x_306);
if (x_307 == 0)
{
lean_object* x_308; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_3);
lean_ctor_set(x_308, 1, x_295);
return x_308;
}
else
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_16, 1);
lean_inc(x_309);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_309;
x_5 = x_295;
goto _start;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; uint8_t x_315; 
x_311 = lean_ctor_get(x_303, 0);
lean_inc(x_311);
lean_dec(x_303);
x_312 = lean_ctor_get(x_16, 0);
lean_inc(x_312);
x_313 = lean_box(3);
x_314 = l_Lean_Meta_DiscrTree_Key_beq(x_312, x_313);
lean_dec(x_312);
x_315 = l_coeDecidableEq(x_314);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_16);
x_316 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_296, x_296, x_15, x_13);
lean_dec(x_296);
x_317 = lean_ctor_get(x_311, 1);
lean_inc(x_317);
lean_dec(x_311);
x_1 = x_316;
x_2 = x_317;
x_5 = x_295;
goto _start;
}
else
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_16, 1);
lean_inc(x_319);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_320 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_319, x_3, x_4, x_295);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_296, x_296, x_15, x_13);
lean_dec(x_296);
x_324 = lean_ctor_get(x_311, 1);
lean_inc(x_324);
lean_dec(x_311);
x_1 = x_323;
x_2 = x_324;
x_3 = x_321;
x_5 = x_322;
goto _start;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_311);
lean_dec(x_296);
lean_dec(x_13);
lean_dec(x_4);
x_326 = lean_ctor_get(x_320, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_320, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_328 = x_320;
} else {
 lean_dec_ref(x_320);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
}
}
}
}
case 3:
{
uint8_t x_330; 
lean_dec(x_19);
lean_dec(x_7);
x_330 = !lean_is_exclusive(x_18);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; uint8_t x_336; 
x_331 = lean_ctor_get(x_18, 1);
x_332 = lean_ctor_get(x_18, 0);
lean_dec(x_332);
x_333 = lean_ctor_get(x_16, 0);
lean_inc(x_333);
x_334 = lean_box(3);
x_335 = l_Lean_Meta_DiscrTree_Key_beq(x_333, x_334);
lean_dec(x_333);
x_336 = l_coeDecidableEq(x_335);
if (x_336 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
lean_object* x_337; 
lean_free_object(x_18);
x_337 = lean_ctor_get(x_16, 1);
lean_inc(x_337);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_337;
x_5 = x_331;
goto _start;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; uint8_t x_343; 
x_339 = lean_ctor_get(x_18, 1);
lean_inc(x_339);
lean_dec(x_18);
x_340 = lean_ctor_get(x_16, 0);
lean_inc(x_340);
x_341 = lean_box(3);
x_342 = l_Lean_Meta_DiscrTree_Key_beq(x_340, x_341);
lean_dec(x_340);
x_343 = l_coeDecidableEq(x_342);
if (x_343 == 0)
{
lean_object* x_344; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_3);
lean_ctor_set(x_344, 1, x_339);
return x_344;
}
else
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_16, 1);
lean_inc(x_345);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_345;
x_5 = x_339;
goto _start;
}
}
}
default: 
{
uint8_t x_347; 
x_347 = !lean_is_exclusive(x_18);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; uint8_t x_350; 
x_348 = lean_ctor_get(x_18, 1);
x_349 = lean_ctor_get(x_18, 0);
lean_dec(x_349);
x_350 = !lean_is_exclusive(x_19);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_351 = lean_ctor_get(x_19, 1);
x_352 = lean_ctor_get(x_19, 0);
lean_dec(x_352);
x_353 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
lean_ctor_set(x_19, 1, x_353);
x_354 = lean_array_get_size(x_7);
x_355 = lean_unsigned_to_nat(1u);
x_356 = lean_nat_sub(x_354, x_355);
lean_dec(x_354);
x_357 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__4___rarg(x_7, x_19, x_15, x_356);
lean_dec(x_19);
lean_dec(x_7);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; uint8_t x_361; 
lean_dec(x_351);
x_358 = lean_ctor_get(x_16, 0);
lean_inc(x_358);
x_359 = lean_box(3);
x_360 = l_Lean_Meta_DiscrTree_Key_beq(x_358, x_359);
lean_dec(x_358);
x_361 = l_coeDecidableEq(x_360);
if (x_361 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
lean_object* x_362; 
lean_free_object(x_18);
x_362 = lean_ctor_get(x_16, 1);
lean_inc(x_362);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_362;
x_5 = x_348;
goto _start;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; uint8_t x_368; 
lean_free_object(x_18);
x_364 = lean_ctor_get(x_357, 0);
lean_inc(x_364);
lean_dec(x_357);
x_365 = lean_ctor_get(x_16, 0);
lean_inc(x_365);
x_366 = lean_box(3);
x_367 = l_Lean_Meta_DiscrTree_Key_beq(x_365, x_366);
lean_dec(x_365);
x_368 = l_coeDecidableEq(x_367);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; 
lean_dec(x_16);
x_369 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_351, x_351, x_15, x_13);
lean_dec(x_351);
x_370 = lean_ctor_get(x_364, 1);
lean_inc(x_370);
lean_dec(x_364);
x_1 = x_369;
x_2 = x_370;
x_5 = x_348;
goto _start;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_16, 1);
lean_inc(x_372);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_373 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_372, x_3, x_4, x_348);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_351, x_351, x_15, x_13);
lean_dec(x_351);
x_377 = lean_ctor_get(x_364, 1);
lean_inc(x_377);
lean_dec(x_364);
x_1 = x_376;
x_2 = x_377;
x_3 = x_374;
x_5 = x_375;
goto _start;
}
else
{
uint8_t x_379; 
lean_dec(x_364);
lean_dec(x_351);
lean_dec(x_13);
lean_dec(x_4);
x_379 = !lean_is_exclusive(x_373);
if (x_379 == 0)
{
return x_373;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_373, 0);
x_381 = lean_ctor_get(x_373, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_373);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_383 = lean_ctor_get(x_19, 1);
lean_inc(x_383);
lean_dec(x_19);
x_384 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_20);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_array_get_size(x_7);
x_387 = lean_unsigned_to_nat(1u);
x_388 = lean_nat_sub(x_386, x_387);
lean_dec(x_386);
x_389 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__4___rarg(x_7, x_385, x_15, x_388);
lean_dec(x_385);
lean_dec(x_7);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; uint8_t x_393; 
lean_dec(x_383);
x_390 = lean_ctor_get(x_16, 0);
lean_inc(x_390);
x_391 = lean_box(3);
x_392 = l_Lean_Meta_DiscrTree_Key_beq(x_390, x_391);
lean_dec(x_390);
x_393 = l_coeDecidableEq(x_392);
if (x_393 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
lean_object* x_394; 
lean_free_object(x_18);
x_394 = lean_ctor_get(x_16, 1);
lean_inc(x_394);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_394;
x_5 = x_348;
goto _start;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; uint8_t x_400; 
lean_free_object(x_18);
x_396 = lean_ctor_get(x_389, 0);
lean_inc(x_396);
lean_dec(x_389);
x_397 = lean_ctor_get(x_16, 0);
lean_inc(x_397);
x_398 = lean_box(3);
x_399 = l_Lean_Meta_DiscrTree_Key_beq(x_397, x_398);
lean_dec(x_397);
x_400 = l_coeDecidableEq(x_399);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; 
lean_dec(x_16);
x_401 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_383, x_383, x_15, x_13);
lean_dec(x_383);
x_402 = lean_ctor_get(x_396, 1);
lean_inc(x_402);
lean_dec(x_396);
x_1 = x_401;
x_2 = x_402;
x_5 = x_348;
goto _start;
}
else
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_16, 1);
lean_inc(x_404);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_405 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_404, x_3, x_4, x_348);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_383, x_383, x_15, x_13);
lean_dec(x_383);
x_409 = lean_ctor_get(x_396, 1);
lean_inc(x_409);
lean_dec(x_396);
x_1 = x_408;
x_2 = x_409;
x_3 = x_406;
x_5 = x_407;
goto _start;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_396);
lean_dec(x_383);
lean_dec(x_13);
lean_dec(x_4);
x_411 = lean_ctor_get(x_405, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_405, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_413 = x_405;
} else {
 lean_dec_ref(x_405);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_412);
return x_414;
}
}
}
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_415 = lean_ctor_get(x_18, 1);
lean_inc(x_415);
lean_dec(x_18);
x_416 = lean_ctor_get(x_19, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_417 = x_19;
} else {
 lean_dec_ref(x_19);
 x_417 = lean_box(0);
}
x_418 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_20);
lean_ctor_set(x_419, 1, x_418);
x_420 = lean_array_get_size(x_7);
x_421 = lean_unsigned_to_nat(1u);
x_422 = lean_nat_sub(x_420, x_421);
lean_dec(x_420);
x_423 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__4___rarg(x_7, x_419, x_15, x_422);
lean_dec(x_419);
lean_dec(x_7);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; uint8_t x_426; uint8_t x_427; 
lean_dec(x_416);
x_424 = lean_ctor_get(x_16, 0);
lean_inc(x_424);
x_425 = lean_box(3);
x_426 = l_Lean_Meta_DiscrTree_Key_beq(x_424, x_425);
lean_dec(x_424);
x_427 = l_coeDecidableEq(x_426);
if (x_427 == 0)
{
lean_object* x_428; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_3);
lean_ctor_set(x_428, 1, x_415);
return x_428;
}
else
{
lean_object* x_429; 
x_429 = lean_ctor_get(x_16, 1);
lean_inc(x_429);
lean_dec(x_16);
x_1 = x_13;
x_2 = x_429;
x_5 = x_415;
goto _start;
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; uint8_t x_435; 
x_431 = lean_ctor_get(x_423, 0);
lean_inc(x_431);
lean_dec(x_423);
x_432 = lean_ctor_get(x_16, 0);
lean_inc(x_432);
x_433 = lean_box(3);
x_434 = l_Lean_Meta_DiscrTree_Key_beq(x_432, x_433);
lean_dec(x_432);
x_435 = l_coeDecidableEq(x_434);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_16);
x_436 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_416, x_416, x_15, x_13);
lean_dec(x_416);
x_437 = lean_ctor_get(x_431, 1);
lean_inc(x_437);
lean_dec(x_431);
x_1 = x_436;
x_2 = x_437;
x_5 = x_415;
goto _start;
}
else
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_ctor_get(x_16, 1);
lean_inc(x_439);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_13);
x_440 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_13, x_439, x_3, x_4, x_415);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_443 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_416, x_416, x_15, x_13);
lean_dec(x_416);
x_444 = lean_ctor_get(x_431, 1);
lean_inc(x_444);
lean_dec(x_431);
x_1 = x_443;
x_2 = x_444;
x_3 = x_441;
x_5 = x_442;
goto _start;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_431);
lean_dec(x_416);
lean_dec(x_13);
lean_dec(x_4);
x_446 = lean_ctor_get(x_440, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_440, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_448 = x_440;
} else {
 lean_dec_ref(x_440);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
}
}
}
}
}
else
{
uint8_t x_450; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_450 = !lean_is_exclusive(x_18);
if (x_450 == 0)
{
return x_18;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_18, 0);
x_452 = lean_ctor_get(x_18, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_18);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
else
{
lean_object* x_454; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_3);
lean_ctor_set(x_454, 1, x_5);
return x_454;
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_455 = lean_unsigned_to_nat(0u);
x_456 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_6, x_6, x_455, x_3);
lean_dec(x_6);
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_5);
return x_457;
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___rarg), 5, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l_Lean_Meta_DiscrTree_Key_beq(x_5, x_9);
lean_dec(x_9);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__2___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_DiscrTree_Key_beq(x_3, x_11);
lean_dec(x_11);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = x_2 >> x_5;
x_1 = x_17;
x_2 = x_18;
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
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__3___rarg(x_21, x_22, lean_box(0), x_23, x_3);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__2___rarg(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_16__getStarResult___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(3);
x_3 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__1___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_mkPath___closed__1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Meta_DiscrTree_mkPath___closed__1;
x_9 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_6, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_16__getStarResult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_DiscrTree_16__getStarResult___rarg), 1, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__2___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_DiscrTree_16__getStarResult___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l_Lean_Meta_DiscrTree_Key_beq(x_5, x_9);
lean_dec(x_9);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__2___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_DiscrTree_Key_beq(x_3, x_11);
lean_dec(x_11);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = x_2 >> x_5;
x_1 = x_17;
x_2 = x_18;
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
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__3___rarg(x_21, x_22, lean_box(0), x_23, x_3);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatch___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__2___rarg(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatch___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatch___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_5 = l___private_Init_Lean_Meta_DiscrTree_16__getStarResult___rarg(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 2;
lean_ctor_set_uint8(x_7, sizeof(void*)*1 + 6, x_9);
x_10 = 1;
lean_inc(x_3);
x_11 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(x_2, x_10, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 3)
{
lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_box(0);
x_17 = x_24;
goto block_22;
}
block_22:
{
lean_object* x_18; 
lean_dec(x_17);
x_18 = l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatch___spec__1___rarg(x_1, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_3);
if (lean_is_scalar(x_14)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_14;
}
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_16, x_20, x_5, x_3, x_13);
return x_21;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_7, 0);
x_30 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_31 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 1);
x_32 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 2);
x_33 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 3);
x_34 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 4);
x_35 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 5);
lean_inc(x_29);
lean_dec(x_7);
x_36 = 2;
x_37 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_30);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 1, x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 2, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 3, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 6, x_36);
lean_ctor_set(x_3, 0, x_37);
x_38 = 1;
lean_inc(x_3);
x_39 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(x_2, x_38, x_3, x_4);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
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
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
if (lean_obj_tag(x_43) == 3)
{
lean_object* x_51; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_3);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_5);
lean_ctor_set(x_51, 1, x_41);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_box(0);
x_45 = x_52;
goto block_50;
}
block_50:
{
lean_object* x_46; 
lean_dec(x_45);
x_46 = l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatch___spec__1___rarg(x_1, x_43);
lean_dec(x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec(x_44);
lean_dec(x_3);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_44, x_48, x_5, x_3, x_41);
return x_49;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
lean_dec(x_5);
lean_dec(x_1);
x_53 = lean_ctor_get(x_39, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_55 = x_39;
} else {
 lean_dec_ref(x_39);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_57 = lean_ctor_get(x_3, 0);
x_58 = lean_ctor_get(x_3, 1);
x_59 = lean_ctor_get(x_3, 2);
x_60 = lean_ctor_get(x_3, 3);
x_61 = lean_ctor_get(x_3, 4);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_3);
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_57, sizeof(void*)*1);
x_64 = lean_ctor_get_uint8(x_57, sizeof(void*)*1 + 1);
x_65 = lean_ctor_get_uint8(x_57, sizeof(void*)*1 + 2);
x_66 = lean_ctor_get_uint8(x_57, sizeof(void*)*1 + 3);
x_67 = lean_ctor_get_uint8(x_57, sizeof(void*)*1 + 4);
x_68 = lean_ctor_get_uint8(x_57, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_69 = x_57;
} else {
 lean_dec_ref(x_57);
 x_69 = lean_box(0);
}
x_70 = 2;
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 1, 7);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_63);
lean_ctor_set_uint8(x_71, sizeof(void*)*1 + 1, x_64);
lean_ctor_set_uint8(x_71, sizeof(void*)*1 + 2, x_65);
lean_ctor_set_uint8(x_71, sizeof(void*)*1 + 3, x_66);
lean_ctor_set_uint8(x_71, sizeof(void*)*1 + 4, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*1 + 5, x_68);
lean_ctor_set_uint8(x_71, sizeof(void*)*1 + 6, x_70);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_58);
lean_ctor_set(x_72, 2, x_59);
lean_ctor_set(x_72, 3, x_60);
lean_ctor_set(x_72, 4, x_61);
x_73 = 1;
lean_inc(x_72);
x_74 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(x_2, x_73, x_72, x_4);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
if (lean_obj_tag(x_78) == 3)
{
lean_object* x_86; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_72);
lean_dec(x_1);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_5);
lean_ctor_set(x_86, 1, x_76);
return x_86;
}
else
{
lean_object* x_87; 
x_87 = lean_box(0);
x_80 = x_87;
goto block_85;
}
block_85:
{
lean_object* x_81; 
lean_dec(x_80);
x_81 = l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatch___spec__1___rarg(x_1, x_78);
lean_dec(x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
lean_dec(x_79);
lean_dec(x_72);
if (lean_is_scalar(x_77)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_77;
}
lean_ctor_set(x_82, 0, x_5);
lean_ctor_set(x_82, 1, x_76);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Init_Lean_Meta_DiscrTree_15__getMatchAux___main___rarg(x_79, x_83, x_5, x_72, x_76);
return x_84;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_1);
x_88 = lean_ctor_get(x_74, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_90 = x_74;
} else {
 lean_dec_ref(x_74);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getMatch___rarg), 4, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getMatch___spec__2___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatch___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getMatch___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
x_15 = l_coeDecidableEq(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_4);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
x_18 = l_coeDecidableEq(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_9, x_21);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_9, x_24);
lean_dec(x_9);
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_3);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
x_3 = x_29;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
x_15 = l_coeDecidableEq(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_4);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
x_18 = l_coeDecidableEq(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_9, x_21);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_9, x_24);
lean_dec(x_9);
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_3);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
x_3 = x_29;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
x_15 = l_coeDecidableEq(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_4);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
x_18 = l_coeDecidableEq(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_9, x_21);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_9, x_24);
lean_dec(x_9);
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_3);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
x_3 = x_29;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_Meta_DiscrTree_Key_arity(x_14);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_2);
x_17 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_16, x_2, x_15, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_13;
x_5 = x_18;
x_7 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__4___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_13);
x_15 = l_coeDecidableEq(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_4);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_12);
lean_dec(x_12);
x_18 = l_coeDecidableEq(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_9, x_21);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_9, x_24);
lean_dec(x_9);
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_3);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
x_3 = x_29;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_array_fget(x_4, x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lean_Meta_DiscrTree_Key_arity(x_15);
lean_dec(x_15);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_1);
x_19 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_18, x_1, x_16, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_5 = x_14;
x_6 = x_20;
x_8 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__6___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_Array_isEmpty___rarg(x_11);
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__6___rarg(x_2, x_10, x_11, x_11, x_7, x_4, x_5, x_6);
lean_dec(x_11);
lean_dec(x_10);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = l_Array_isEmpty___rarg(x_2);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
uint8_t x_20; uint8_t x_21; 
lean_dec(x_16);
x_20 = l_Array_isEmpty___rarg(x_17);
x_21 = l_coeDecidableEq(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___main___spec__1(x_2);
x_23 = lean_array_pop(x_2);
x_24 = 0;
lean_inc(x_5);
x_25 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(x_22, x_24, x_5, x_6);
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_26, 1);
x_33 = lean_ctor_get(x_26, 0);
lean_dec(x_33);
x_34 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_35 = lean_array_get(x_34, x_17, x_7);
x_36 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
lean_ctor_set(x_26, 1, x_36);
x_37 = lean_array_get_size(x_17);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_37, x_38);
lean_dec(x_37);
x_40 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__1___rarg(x_17, x_26, x_7, x_39);
lean_dec(x_26);
lean_dec(x_17);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; 
lean_dec(x_32);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
x_42 = lean_box(3);
x_43 = l_Lean_Meta_DiscrTree_Key_beq(x_41, x_42);
lean_dec(x_41);
x_44 = l_coeDecidableEq(x_43);
if (x_44 == 0)
{
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
else
{
lean_object* x_45; 
lean_free_object(x_25);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_1 = x_7;
x_2 = x_23;
x_3 = x_45;
x_6 = x_29;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
lean_free_object(x_25);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
x_49 = lean_box(3);
x_50 = l_Lean_Meta_DiscrTree_Key_beq(x_48, x_49);
lean_dec(x_48);
x_51 = l_coeDecidableEq(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_35);
x_52 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_32, x_32, x_7, x_23);
lean_dec(x_32);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_1 = x_7;
x_2 = x_52;
x_3 = x_53;
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_35, 1);
lean_inc(x_55);
lean_dec(x_35);
lean_inc(x_5);
lean_inc(x_23);
x_56 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_55, x_4, x_5, x_29);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_32, x_32, x_7, x_23);
lean_dec(x_32);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_dec(x_47);
x_1 = x_7;
x_2 = x_59;
x_3 = x_60;
x_4 = x_57;
x_6 = x_58;
goto _start;
}
else
{
uint8_t x_62; 
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_56);
if (x_62 == 0)
{
return x_56;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_56, 0);
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_56);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_26, 1);
lean_inc(x_66);
lean_dec(x_26);
x_67 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_68 = lean_array_get(x_67, x_17, x_7);
x_69 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_27);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_get_size(x_17);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_sub(x_71, x_72);
lean_dec(x_71);
x_74 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__1___rarg(x_17, x_70, x_7, x_73);
lean_dec(x_70);
lean_dec(x_17);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; 
lean_dec(x_66);
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
x_76 = lean_box(3);
x_77 = l_Lean_Meta_DiscrTree_Key_beq(x_75, x_76);
lean_dec(x_75);
x_78 = l_coeDecidableEq(x_77);
if (x_78 == 0)
{
lean_dec(x_68);
lean_dec(x_23);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
else
{
lean_object* x_79; 
lean_free_object(x_25);
x_79 = lean_ctor_get(x_68, 1);
lean_inc(x_79);
lean_dec(x_68);
x_1 = x_7;
x_2 = x_23;
x_3 = x_79;
x_6 = x_29;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; 
lean_free_object(x_25);
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_ctor_get(x_68, 0);
lean_inc(x_82);
x_83 = lean_box(3);
x_84 = l_Lean_Meta_DiscrTree_Key_beq(x_82, x_83);
lean_dec(x_82);
x_85 = l_coeDecidableEq(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_68);
x_86 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_66, x_66, x_7, x_23);
lean_dec(x_66);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_1 = x_7;
x_2 = x_86;
x_3 = x_87;
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_68, 1);
lean_inc(x_89);
lean_dec(x_68);
lean_inc(x_5);
lean_inc(x_23);
x_90 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_89, x_4, x_5, x_29);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_66, x_66, x_7, x_23);
lean_dec(x_66);
x_94 = lean_ctor_get(x_81, 1);
lean_inc(x_94);
lean_dec(x_81);
x_1 = x_7;
x_2 = x_93;
x_3 = x_94;
x_4 = x_91;
x_6 = x_92;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_81);
lean_dec(x_66);
lean_dec(x_23);
lean_dec(x_5);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_25, 1);
lean_inc(x_100);
lean_dec(x_25);
x_101 = lean_ctor_get(x_26, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_102 = x_26;
} else {
 lean_dec_ref(x_26);
 x_102 = lean_box(0);
}
x_103 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_104 = lean_array_get(x_103, x_17, x_7);
x_105 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
if (lean_is_scalar(x_102)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_102;
}
lean_ctor_set(x_106, 0, x_27);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_array_get_size(x_17);
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_nat_sub(x_107, x_108);
lean_dec(x_107);
x_110 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__1___rarg(x_17, x_106, x_7, x_109);
lean_dec(x_106);
lean_dec(x_17);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; 
lean_dec(x_101);
x_111 = lean_ctor_get(x_104, 0);
lean_inc(x_111);
x_112 = lean_box(3);
x_113 = l_Lean_Meta_DiscrTree_Key_beq(x_111, x_112);
lean_dec(x_111);
x_114 = l_coeDecidableEq(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
lean_dec(x_104);
lean_dec(x_23);
lean_dec(x_5);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_4);
lean_ctor_set(x_115, 1, x_100);
return x_115;
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_104, 1);
lean_inc(x_116);
lean_dec(x_104);
x_1 = x_7;
x_2 = x_23;
x_3 = x_116;
x_6 = x_100;
goto _start;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_122; 
x_118 = lean_ctor_get(x_110, 0);
lean_inc(x_118);
lean_dec(x_110);
x_119 = lean_ctor_get(x_104, 0);
lean_inc(x_119);
x_120 = lean_box(3);
x_121 = l_Lean_Meta_DiscrTree_Key_beq(x_119, x_120);
lean_dec(x_119);
x_122 = l_coeDecidableEq(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_104);
x_123 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_101, x_101, x_7, x_23);
lean_dec(x_101);
x_124 = lean_ctor_get(x_118, 1);
lean_inc(x_124);
lean_dec(x_118);
x_1 = x_7;
x_2 = x_123;
x_3 = x_124;
x_6 = x_100;
goto _start;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_104, 1);
lean_inc(x_126);
lean_dec(x_104);
lean_inc(x_5);
lean_inc(x_23);
x_127 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_126, x_4, x_5, x_100);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_101, x_101, x_7, x_23);
lean_dec(x_101);
x_131 = lean_ctor_get(x_118, 1);
lean_inc(x_131);
lean_dec(x_118);
x_1 = x_7;
x_2 = x_130;
x_3 = x_131;
x_4 = x_128;
x_6 = x_129;
goto _start;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_118);
lean_dec(x_101);
lean_dec(x_23);
lean_dec(x_5);
x_133 = lean_ctor_get(x_127, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_135 = x_127;
} else {
 lean_dec_ref(x_127);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
}
}
case 1:
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_25);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_25, 1);
x_139 = lean_ctor_get(x_25, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_26);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_26, 1);
x_142 = lean_ctor_get(x_26, 0);
lean_dec(x_142);
x_143 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_144 = lean_array_get(x_143, x_17, x_7);
x_145 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
lean_ctor_set(x_26, 1, x_145);
x_146 = lean_array_get_size(x_17);
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_nat_sub(x_146, x_147);
lean_dec(x_146);
x_149 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__2___rarg(x_17, x_26, x_7, x_148);
lean_dec(x_26);
lean_dec(x_17);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_153; 
lean_dec(x_141);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_box(3);
x_152 = l_Lean_Meta_DiscrTree_Key_beq(x_150, x_151);
lean_dec(x_150);
x_153 = l_coeDecidableEq(x_152);
if (x_153 == 0)
{
lean_dec(x_144);
lean_dec(x_23);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
else
{
lean_object* x_154; 
lean_free_object(x_25);
x_154 = lean_ctor_get(x_144, 1);
lean_inc(x_154);
lean_dec(x_144);
x_1 = x_7;
x_2 = x_23;
x_3 = x_154;
x_6 = x_138;
goto _start;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_160; 
lean_free_object(x_25);
x_156 = lean_ctor_get(x_149, 0);
lean_inc(x_156);
lean_dec(x_149);
x_157 = lean_ctor_get(x_144, 0);
lean_inc(x_157);
x_158 = lean_box(3);
x_159 = l_Lean_Meta_DiscrTree_Key_beq(x_157, x_158);
lean_dec(x_157);
x_160 = l_coeDecidableEq(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_144);
x_161 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_141, x_141, x_7, x_23);
lean_dec(x_141);
x_162 = lean_ctor_get(x_156, 1);
lean_inc(x_162);
lean_dec(x_156);
x_1 = x_7;
x_2 = x_161;
x_3 = x_162;
x_6 = x_138;
goto _start;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_144, 1);
lean_inc(x_164);
lean_dec(x_144);
lean_inc(x_5);
lean_inc(x_23);
x_165 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_164, x_4, x_5, x_138);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_141, x_141, x_7, x_23);
lean_dec(x_141);
x_169 = lean_ctor_get(x_156, 1);
lean_inc(x_169);
lean_dec(x_156);
x_1 = x_7;
x_2 = x_168;
x_3 = x_169;
x_4 = x_166;
x_6 = x_167;
goto _start;
}
else
{
uint8_t x_171; 
lean_dec(x_156);
lean_dec(x_141);
lean_dec(x_23);
lean_dec(x_5);
x_171 = !lean_is_exclusive(x_165);
if (x_171 == 0)
{
return x_165;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_165, 0);
x_173 = lean_ctor_get(x_165, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_165);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_175 = lean_ctor_get(x_26, 1);
lean_inc(x_175);
lean_dec(x_26);
x_176 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_177 = lean_array_get(x_176, x_17, x_7);
x_178 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_27);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_array_get_size(x_17);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_sub(x_180, x_181);
lean_dec(x_180);
x_183 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__2___rarg(x_17, x_179, x_7, x_182);
lean_dec(x_179);
lean_dec(x_17);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_187; 
lean_dec(x_175);
x_184 = lean_ctor_get(x_177, 0);
lean_inc(x_184);
x_185 = lean_box(3);
x_186 = l_Lean_Meta_DiscrTree_Key_beq(x_184, x_185);
lean_dec(x_184);
x_187 = l_coeDecidableEq(x_186);
if (x_187 == 0)
{
lean_dec(x_177);
lean_dec(x_23);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
else
{
lean_object* x_188; 
lean_free_object(x_25);
x_188 = lean_ctor_get(x_177, 1);
lean_inc(x_188);
lean_dec(x_177);
x_1 = x_7;
x_2 = x_23;
x_3 = x_188;
x_6 = x_138;
goto _start;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; 
lean_free_object(x_25);
x_190 = lean_ctor_get(x_183, 0);
lean_inc(x_190);
lean_dec(x_183);
x_191 = lean_ctor_get(x_177, 0);
lean_inc(x_191);
x_192 = lean_box(3);
x_193 = l_Lean_Meta_DiscrTree_Key_beq(x_191, x_192);
lean_dec(x_191);
x_194 = l_coeDecidableEq(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_177);
x_195 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_175, x_175, x_7, x_23);
lean_dec(x_175);
x_196 = lean_ctor_get(x_190, 1);
lean_inc(x_196);
lean_dec(x_190);
x_1 = x_7;
x_2 = x_195;
x_3 = x_196;
x_6 = x_138;
goto _start;
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_177, 1);
lean_inc(x_198);
lean_dec(x_177);
lean_inc(x_5);
lean_inc(x_23);
x_199 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_198, x_4, x_5, x_138);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_175, x_175, x_7, x_23);
lean_dec(x_175);
x_203 = lean_ctor_get(x_190, 1);
lean_inc(x_203);
lean_dec(x_190);
x_1 = x_7;
x_2 = x_202;
x_3 = x_203;
x_4 = x_200;
x_6 = x_201;
goto _start;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_190);
lean_dec(x_175);
lean_dec(x_23);
lean_dec(x_5);
x_205 = lean_ctor_get(x_199, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_199, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_207 = x_199;
} else {
 lean_dec_ref(x_199);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_209 = lean_ctor_get(x_25, 1);
lean_inc(x_209);
lean_dec(x_25);
x_210 = lean_ctor_get(x_26, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_211 = x_26;
} else {
 lean_dec_ref(x_26);
 x_211 = lean_box(0);
}
x_212 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_213 = lean_array_get(x_212, x_17, x_7);
x_214 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
if (lean_is_scalar(x_211)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_211;
}
lean_ctor_set(x_215, 0, x_27);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_array_get_size(x_17);
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_nat_sub(x_216, x_217);
lean_dec(x_216);
x_219 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__2___rarg(x_17, x_215, x_7, x_218);
lean_dec(x_215);
lean_dec(x_17);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; uint8_t x_223; 
lean_dec(x_210);
x_220 = lean_ctor_get(x_213, 0);
lean_inc(x_220);
x_221 = lean_box(3);
x_222 = l_Lean_Meta_DiscrTree_Key_beq(x_220, x_221);
lean_dec(x_220);
x_223 = l_coeDecidableEq(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
lean_dec(x_213);
lean_dec(x_23);
lean_dec(x_5);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_4);
lean_ctor_set(x_224, 1, x_209);
return x_224;
}
else
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_213, 1);
lean_inc(x_225);
lean_dec(x_213);
x_1 = x_7;
x_2 = x_23;
x_3 = x_225;
x_6 = x_209;
goto _start;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_227 = lean_ctor_get(x_219, 0);
lean_inc(x_227);
lean_dec(x_219);
x_228 = lean_ctor_get(x_213, 0);
lean_inc(x_228);
x_229 = lean_box(3);
x_230 = l_Lean_Meta_DiscrTree_Key_beq(x_228, x_229);
lean_dec(x_228);
x_231 = l_coeDecidableEq(x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_213);
x_232 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_210, x_210, x_7, x_23);
lean_dec(x_210);
x_233 = lean_ctor_get(x_227, 1);
lean_inc(x_233);
lean_dec(x_227);
x_1 = x_7;
x_2 = x_232;
x_3 = x_233;
x_6 = x_209;
goto _start;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_213, 1);
lean_inc(x_235);
lean_dec(x_213);
lean_inc(x_5);
lean_inc(x_23);
x_236 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_235, x_4, x_5, x_209);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_210, x_210, x_7, x_23);
lean_dec(x_210);
x_240 = lean_ctor_get(x_227, 1);
lean_inc(x_240);
lean_dec(x_227);
x_1 = x_7;
x_2 = x_239;
x_3 = x_240;
x_4 = x_237;
x_6 = x_238;
goto _start;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_227);
lean_dec(x_210);
lean_dec(x_23);
lean_dec(x_5);
x_242 = lean_ctor_get(x_236, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_236, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_244 = x_236;
} else {
 lean_dec_ref(x_236);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
}
}
case 2:
{
uint8_t x_246; 
x_246 = !lean_is_exclusive(x_25);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_247 = lean_ctor_get(x_25, 1);
x_248 = lean_ctor_get(x_25, 0);
lean_dec(x_248);
x_249 = !lean_is_exclusive(x_26);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_250 = lean_ctor_get(x_26, 1);
x_251 = lean_ctor_get(x_26, 0);
lean_dec(x_251);
x_252 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_253 = lean_array_get(x_252, x_17, x_7);
x_254 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
lean_ctor_set(x_26, 1, x_254);
x_255 = lean_array_get_size(x_17);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_sub(x_255, x_256);
lean_dec(x_255);
x_258 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__3___rarg(x_17, x_26, x_7, x_257);
lean_dec(x_26);
lean_dec(x_17);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_262; 
lean_dec(x_250);
x_259 = lean_ctor_get(x_253, 0);
lean_inc(x_259);
x_260 = lean_box(3);
x_261 = l_Lean_Meta_DiscrTree_Key_beq(x_259, x_260);
lean_dec(x_259);
x_262 = l_coeDecidableEq(x_261);
if (x_262 == 0)
{
lean_dec(x_253);
lean_dec(x_23);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
else
{
lean_object* x_263; 
lean_free_object(x_25);
x_263 = lean_ctor_get(x_253, 1);
lean_inc(x_263);
lean_dec(x_253);
x_1 = x_7;
x_2 = x_23;
x_3 = x_263;
x_6 = x_247;
goto _start;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; uint8_t x_269; 
lean_free_object(x_25);
x_265 = lean_ctor_get(x_258, 0);
lean_inc(x_265);
lean_dec(x_258);
x_266 = lean_ctor_get(x_253, 0);
lean_inc(x_266);
x_267 = lean_box(3);
x_268 = l_Lean_Meta_DiscrTree_Key_beq(x_266, x_267);
lean_dec(x_266);
x_269 = l_coeDecidableEq(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_253);
x_270 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_250, x_250, x_7, x_23);
lean_dec(x_250);
x_271 = lean_ctor_get(x_265, 1);
lean_inc(x_271);
lean_dec(x_265);
x_1 = x_7;
x_2 = x_270;
x_3 = x_271;
x_6 = x_247;
goto _start;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_253, 1);
lean_inc(x_273);
lean_dec(x_253);
lean_inc(x_5);
lean_inc(x_23);
x_274 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_273, x_4, x_5, x_247);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_250, x_250, x_7, x_23);
lean_dec(x_250);
x_278 = lean_ctor_get(x_265, 1);
lean_inc(x_278);
lean_dec(x_265);
x_1 = x_7;
x_2 = x_277;
x_3 = x_278;
x_4 = x_275;
x_6 = x_276;
goto _start;
}
else
{
uint8_t x_280; 
lean_dec(x_265);
lean_dec(x_250);
lean_dec(x_23);
lean_dec(x_5);
x_280 = !lean_is_exclusive(x_274);
if (x_280 == 0)
{
return x_274;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_274, 0);
x_282 = lean_ctor_get(x_274, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_274);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_284 = lean_ctor_get(x_26, 1);
lean_inc(x_284);
lean_dec(x_26);
x_285 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_286 = lean_array_get(x_285, x_17, x_7);
x_287 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_27);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_array_get_size(x_17);
x_290 = lean_unsigned_to_nat(1u);
x_291 = lean_nat_sub(x_289, x_290);
lean_dec(x_289);
x_292 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__3___rarg(x_17, x_288, x_7, x_291);
lean_dec(x_288);
lean_dec(x_17);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; uint8_t x_296; 
lean_dec(x_284);
x_293 = lean_ctor_get(x_286, 0);
lean_inc(x_293);
x_294 = lean_box(3);
x_295 = l_Lean_Meta_DiscrTree_Key_beq(x_293, x_294);
lean_dec(x_293);
x_296 = l_coeDecidableEq(x_295);
if (x_296 == 0)
{
lean_dec(x_286);
lean_dec(x_23);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
else
{
lean_object* x_297; 
lean_free_object(x_25);
x_297 = lean_ctor_get(x_286, 1);
lean_inc(x_297);
lean_dec(x_286);
x_1 = x_7;
x_2 = x_23;
x_3 = x_297;
x_6 = x_247;
goto _start;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_303; 
lean_free_object(x_25);
x_299 = lean_ctor_get(x_292, 0);
lean_inc(x_299);
lean_dec(x_292);
x_300 = lean_ctor_get(x_286, 0);
lean_inc(x_300);
x_301 = lean_box(3);
x_302 = l_Lean_Meta_DiscrTree_Key_beq(x_300, x_301);
lean_dec(x_300);
x_303 = l_coeDecidableEq(x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_286);
x_304 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_284, x_284, x_7, x_23);
lean_dec(x_284);
x_305 = lean_ctor_get(x_299, 1);
lean_inc(x_305);
lean_dec(x_299);
x_1 = x_7;
x_2 = x_304;
x_3 = x_305;
x_6 = x_247;
goto _start;
}
else
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_286, 1);
lean_inc(x_307);
lean_dec(x_286);
lean_inc(x_5);
lean_inc(x_23);
x_308 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_307, x_4, x_5, x_247);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_284, x_284, x_7, x_23);
lean_dec(x_284);
x_312 = lean_ctor_get(x_299, 1);
lean_inc(x_312);
lean_dec(x_299);
x_1 = x_7;
x_2 = x_311;
x_3 = x_312;
x_4 = x_309;
x_6 = x_310;
goto _start;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_299);
lean_dec(x_284);
lean_dec(x_23);
lean_dec(x_5);
x_314 = lean_ctor_get(x_308, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_308, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_316 = x_308;
} else {
 lean_dec_ref(x_308);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_318 = lean_ctor_get(x_25, 1);
lean_inc(x_318);
lean_dec(x_25);
x_319 = lean_ctor_get(x_26, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_320 = x_26;
} else {
 lean_dec_ref(x_26);
 x_320 = lean_box(0);
}
x_321 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_322 = lean_array_get(x_321, x_17, x_7);
x_323 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
if (lean_is_scalar(x_320)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_320;
}
lean_ctor_set(x_324, 0, x_27);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_array_get_size(x_17);
x_326 = lean_unsigned_to_nat(1u);
x_327 = lean_nat_sub(x_325, x_326);
lean_dec(x_325);
x_328 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__3___rarg(x_17, x_324, x_7, x_327);
lean_dec(x_324);
lean_dec(x_17);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; uint8_t x_332; 
lean_dec(x_319);
x_329 = lean_ctor_get(x_322, 0);
lean_inc(x_329);
x_330 = lean_box(3);
x_331 = l_Lean_Meta_DiscrTree_Key_beq(x_329, x_330);
lean_dec(x_329);
x_332 = l_coeDecidableEq(x_331);
if (x_332 == 0)
{
lean_object* x_333; 
lean_dec(x_322);
lean_dec(x_23);
lean_dec(x_5);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_4);
lean_ctor_set(x_333, 1, x_318);
return x_333;
}
else
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_322, 1);
lean_inc(x_334);
lean_dec(x_322);
x_1 = x_7;
x_2 = x_23;
x_3 = x_334;
x_6 = x_318;
goto _start;
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; uint8_t x_340; 
x_336 = lean_ctor_get(x_328, 0);
lean_inc(x_336);
lean_dec(x_328);
x_337 = lean_ctor_get(x_322, 0);
lean_inc(x_337);
x_338 = lean_box(3);
x_339 = l_Lean_Meta_DiscrTree_Key_beq(x_337, x_338);
lean_dec(x_337);
x_340 = l_coeDecidableEq(x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_322);
x_341 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_319, x_319, x_7, x_23);
lean_dec(x_319);
x_342 = lean_ctor_get(x_336, 1);
lean_inc(x_342);
lean_dec(x_336);
x_1 = x_7;
x_2 = x_341;
x_3 = x_342;
x_6 = x_318;
goto _start;
}
else
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_ctor_get(x_322, 1);
lean_inc(x_344);
lean_dec(x_322);
lean_inc(x_5);
lean_inc(x_23);
x_345 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_344, x_4, x_5, x_318);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_319, x_319, x_7, x_23);
lean_dec(x_319);
x_349 = lean_ctor_get(x_336, 1);
lean_inc(x_349);
lean_dec(x_336);
x_1 = x_7;
x_2 = x_348;
x_3 = x_349;
x_4 = x_346;
x_6 = x_347;
goto _start;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_336);
lean_dec(x_319);
lean_dec(x_23);
lean_dec(x_5);
x_351 = lean_ctor_get(x_345, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_345, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_353 = x_345;
} else {
 lean_dec_ref(x_345);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
}
}
}
}
case 3:
{
lean_object* x_355; lean_object* x_356; 
lean_dec(x_26);
x_355 = lean_ctor_get(x_25, 1);
lean_inc(x_355);
lean_dec(x_25);
x_356 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__4___rarg(x_17, x_23, x_17, x_7, x_4, x_5, x_355);
lean_dec(x_17);
return x_356;
}
default: 
{
uint8_t x_357; 
x_357 = !lean_is_exclusive(x_25);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; 
x_358 = lean_ctor_get(x_25, 1);
x_359 = lean_ctor_get(x_25, 0);
lean_dec(x_359);
x_360 = !lean_is_exclusive(x_26);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_361 = lean_ctor_get(x_26, 1);
x_362 = lean_ctor_get(x_26, 0);
lean_dec(x_362);
x_363 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_364 = lean_array_get(x_363, x_17, x_7);
x_365 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
lean_ctor_set(x_26, 1, x_365);
x_366 = lean_array_get_size(x_17);
x_367 = lean_unsigned_to_nat(1u);
x_368 = lean_nat_sub(x_366, x_367);
lean_dec(x_366);
x_369 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__5___rarg(x_17, x_26, x_7, x_368);
lean_dec(x_26);
lean_dec(x_17);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint8_t x_373; 
lean_dec(x_361);
x_370 = lean_ctor_get(x_364, 0);
lean_inc(x_370);
x_371 = lean_box(3);
x_372 = l_Lean_Meta_DiscrTree_Key_beq(x_370, x_371);
lean_dec(x_370);
x_373 = l_coeDecidableEq(x_372);
if (x_373 == 0)
{
lean_dec(x_364);
lean_dec(x_23);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
else
{
lean_object* x_374; 
lean_free_object(x_25);
x_374 = lean_ctor_get(x_364, 1);
lean_inc(x_374);
lean_dec(x_364);
x_1 = x_7;
x_2 = x_23;
x_3 = x_374;
x_6 = x_358;
goto _start;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; uint8_t x_380; 
lean_free_object(x_25);
x_376 = lean_ctor_get(x_369, 0);
lean_inc(x_376);
lean_dec(x_369);
x_377 = lean_ctor_get(x_364, 0);
lean_inc(x_377);
x_378 = lean_box(3);
x_379 = l_Lean_Meta_DiscrTree_Key_beq(x_377, x_378);
lean_dec(x_377);
x_380 = l_coeDecidableEq(x_379);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; 
lean_dec(x_364);
x_381 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_361, x_361, x_7, x_23);
lean_dec(x_361);
x_382 = lean_ctor_get(x_376, 1);
lean_inc(x_382);
lean_dec(x_376);
x_1 = x_7;
x_2 = x_381;
x_3 = x_382;
x_6 = x_358;
goto _start;
}
else
{
lean_object* x_384; lean_object* x_385; 
x_384 = lean_ctor_get(x_364, 1);
lean_inc(x_384);
lean_dec(x_364);
lean_inc(x_5);
lean_inc(x_23);
x_385 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_384, x_4, x_5, x_358);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_361, x_361, x_7, x_23);
lean_dec(x_361);
x_389 = lean_ctor_get(x_376, 1);
lean_inc(x_389);
lean_dec(x_376);
x_1 = x_7;
x_2 = x_388;
x_3 = x_389;
x_4 = x_386;
x_6 = x_387;
goto _start;
}
else
{
uint8_t x_391; 
lean_dec(x_376);
lean_dec(x_361);
lean_dec(x_23);
lean_dec(x_5);
x_391 = !lean_is_exclusive(x_385);
if (x_391 == 0)
{
return x_385;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_385, 0);
x_393 = lean_ctor_get(x_385, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_385);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
return x_394;
}
}
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_395 = lean_ctor_get(x_26, 1);
lean_inc(x_395);
lean_dec(x_26);
x_396 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_397 = lean_array_get(x_396, x_17, x_7);
x_398 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_27);
lean_ctor_set(x_399, 1, x_398);
x_400 = lean_array_get_size(x_17);
x_401 = lean_unsigned_to_nat(1u);
x_402 = lean_nat_sub(x_400, x_401);
lean_dec(x_400);
x_403 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__5___rarg(x_17, x_399, x_7, x_402);
lean_dec(x_399);
lean_dec(x_17);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; uint8_t x_406; uint8_t x_407; 
lean_dec(x_395);
x_404 = lean_ctor_get(x_397, 0);
lean_inc(x_404);
x_405 = lean_box(3);
x_406 = l_Lean_Meta_DiscrTree_Key_beq(x_404, x_405);
lean_dec(x_404);
x_407 = l_coeDecidableEq(x_406);
if (x_407 == 0)
{
lean_dec(x_397);
lean_dec(x_23);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
else
{
lean_object* x_408; 
lean_free_object(x_25);
x_408 = lean_ctor_get(x_397, 1);
lean_inc(x_408);
lean_dec(x_397);
x_1 = x_7;
x_2 = x_23;
x_3 = x_408;
x_6 = x_358;
goto _start;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; uint8_t x_414; 
lean_free_object(x_25);
x_410 = lean_ctor_get(x_403, 0);
lean_inc(x_410);
lean_dec(x_403);
x_411 = lean_ctor_get(x_397, 0);
lean_inc(x_411);
x_412 = lean_box(3);
x_413 = l_Lean_Meta_DiscrTree_Key_beq(x_411, x_412);
lean_dec(x_411);
x_414 = l_coeDecidableEq(x_413);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; 
lean_dec(x_397);
x_415 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_395, x_395, x_7, x_23);
lean_dec(x_395);
x_416 = lean_ctor_get(x_410, 1);
lean_inc(x_416);
lean_dec(x_410);
x_1 = x_7;
x_2 = x_415;
x_3 = x_416;
x_6 = x_358;
goto _start;
}
else
{
lean_object* x_418; lean_object* x_419; 
x_418 = lean_ctor_get(x_397, 1);
lean_inc(x_418);
lean_dec(x_397);
lean_inc(x_5);
lean_inc(x_23);
x_419 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_418, x_4, x_5, x_358);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_395, x_395, x_7, x_23);
lean_dec(x_395);
x_423 = lean_ctor_get(x_410, 1);
lean_inc(x_423);
lean_dec(x_410);
x_1 = x_7;
x_2 = x_422;
x_3 = x_423;
x_4 = x_420;
x_6 = x_421;
goto _start;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_410);
lean_dec(x_395);
lean_dec(x_23);
lean_dec(x_5);
x_425 = lean_ctor_get(x_419, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_419, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_427 = x_419;
} else {
 lean_dec_ref(x_419);
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
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_429 = lean_ctor_get(x_25, 1);
lean_inc(x_429);
lean_dec(x_25);
x_430 = lean_ctor_get(x_26, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_431 = x_26;
} else {
 lean_dec_ref(x_26);
 x_431 = lean_box(0);
}
x_432 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2;
x_433 = lean_array_get(x_432, x_17, x_7);
x_434 = l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1;
if (lean_is_scalar(x_431)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_431;
}
lean_ctor_set(x_435, 0, x_27);
lean_ctor_set(x_435, 1, x_434);
x_436 = lean_array_get_size(x_17);
x_437 = lean_unsigned_to_nat(1u);
x_438 = lean_nat_sub(x_436, x_437);
lean_dec(x_436);
x_439 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__5___rarg(x_17, x_435, x_7, x_438);
lean_dec(x_435);
lean_dec(x_17);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; uint8_t x_442; uint8_t x_443; 
lean_dec(x_430);
x_440 = lean_ctor_get(x_433, 0);
lean_inc(x_440);
x_441 = lean_box(3);
x_442 = l_Lean_Meta_DiscrTree_Key_beq(x_440, x_441);
lean_dec(x_440);
x_443 = l_coeDecidableEq(x_442);
if (x_443 == 0)
{
lean_object* x_444; 
lean_dec(x_433);
lean_dec(x_23);
lean_dec(x_5);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_4);
lean_ctor_set(x_444, 1, x_429);
return x_444;
}
else
{
lean_object* x_445; 
x_445 = lean_ctor_get(x_433, 1);
lean_inc(x_445);
lean_dec(x_433);
x_1 = x_7;
x_2 = x_23;
x_3 = x_445;
x_6 = x_429;
goto _start;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; uint8_t x_451; 
x_447 = lean_ctor_get(x_439, 0);
lean_inc(x_447);
lean_dec(x_439);
x_448 = lean_ctor_get(x_433, 0);
lean_inc(x_448);
x_449 = lean_box(3);
x_450 = l_Lean_Meta_DiscrTree_Key_beq(x_448, x_449);
lean_dec(x_448);
x_451 = l_coeDecidableEq(x_450);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; 
lean_dec(x_433);
x_452 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_430, x_430, x_7, x_23);
lean_dec(x_430);
x_453 = lean_ctor_get(x_447, 1);
lean_inc(x_453);
lean_dec(x_447);
x_1 = x_7;
x_2 = x_452;
x_3 = x_453;
x_6 = x_429;
goto _start;
}
else
{
lean_object* x_455; lean_object* x_456; 
x_455 = lean_ctor_get(x_433, 1);
lean_inc(x_455);
lean_dec(x_433);
lean_inc(x_5);
lean_inc(x_23);
x_456 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_7, x_23, x_455, x_4, x_5, x_429);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_430, x_430, x_7, x_23);
lean_dec(x_430);
x_460 = lean_ctor_get(x_447, 1);
lean_inc(x_460);
lean_dec(x_447);
x_1 = x_7;
x_2 = x_459;
x_3 = x_460;
x_4 = x_457;
x_6 = x_458;
goto _start;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_447);
lean_dec(x_430);
lean_dec(x_23);
lean_dec(x_5);
x_462 = lean_ctor_get(x_456, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_456, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_464 = x_456;
} else {
 lean_dec_ref(x_456);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(1, 2, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_463);
return x_465;
}
}
}
}
}
}
}
else
{
uint8_t x_466; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
x_466 = !lean_is_exclusive(x_25);
if (x_466 == 0)
{
return x_25;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_25, 0);
x_468 = lean_ctor_get(x_25, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_25);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
}
else
{
lean_object* x_470; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_2);
x_470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_470, 0, x_4);
lean_ctor_set(x_470, 1, x_6);
return x_470;
}
}
else
{
lean_object* x_471; lean_object* x_472; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_2);
x_471 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_16, x_16, x_7, x_4);
lean_dec(x_16);
x_472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_6);
return x_472;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___rarg), 6, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l_Lean_Meta_DiscrTree_Key_beq(x_5, x_9);
lean_dec(x_9);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_DiscrTree_Key_beq(x_3, x_11);
lean_dec(x_11);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = x_2 >> x_5;
x_1 = x_17;
x_2 = x_18;
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
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(x_21, x_22, lean_box(0), x_23, x_3);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Meta_DiscrTree_Key_arity(x_13);
lean_dec(x_13);
x_16 = l_Array_empty___closed__1;
lean_inc(x_5);
x_17 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_15, x_16, x_14, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_3 = x_12;
x_4 = x_18;
x_6 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
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
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
lean_dec(x_10);
lean_inc(x_5);
x_26 = l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(x_25, x_4, x_5, x_6);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_3 = x_12;
x_4 = x_27;
x_6 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
default: 
{
x_3 = x_12;
goto _start;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = l_Lean_Meta_DiscrTree_Key_arity(x_11);
lean_dec(x_11);
x_16 = l_Array_empty___closed__1;
lean_inc(x_6);
x_17 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_15, x_16, x_14, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_13;
x_5 = x_18;
x_7 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(x_5, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(x_8, x_9, x_8, x_10, x_2, x_3, x_4);
return x_11;
}
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = 2;
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 6, x_8);
x_9 = 0;
lean_inc(x_3);
x_10 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(x_2, x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 3)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_13);
x_24 = l_Array_empty___closed__1;
x_25 = l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_24, x_3, x_12);
lean_dec(x_1);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_box(0);
x_16 = x_26;
goto block_23;
}
block_23:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_16);
lean_inc(x_1);
x_17 = l___private_Init_Lean_Meta_DiscrTree_16__getStarResult___rarg(x_1);
x_18 = l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_3);
if (lean_is_scalar(x_13)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_13;
}
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_21, x_15, x_20, x_17, x_3, x_12);
return x_22;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_6, 0);
x_32 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_33 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_34 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_35 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_36 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
x_37 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 5);
lean_inc(x_31);
lean_dec(x_6);
x_38 = 2;
x_39 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_32);
lean_ctor_set_uint8(x_39, sizeof(void*)*1 + 1, x_33);
lean_ctor_set_uint8(x_39, sizeof(void*)*1 + 2, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*1 + 3, x_35);
lean_ctor_set_uint8(x_39, sizeof(void*)*1 + 4, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*1 + 5, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1 + 6, x_38);
lean_ctor_set(x_3, 0, x_39);
x_40 = 0;
lean_inc(x_3);
x_41 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(x_2, x_40, x_3, x_4);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
if (lean_obj_tag(x_45) == 3)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
lean_dec(x_44);
x_55 = l_Array_empty___closed__1;
x_56 = l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_55, x_3, x_43);
lean_dec(x_1);
return x_56;
}
else
{
lean_object* x_57; 
x_57 = lean_box(0);
x_47 = x_57;
goto block_54;
}
block_54:
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_47);
lean_inc(x_1);
x_48 = l___private_Init_Lean_Meta_DiscrTree_16__getStarResult___rarg(x_1);
x_49 = l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_45);
lean_dec(x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_3);
if (lean_is_scalar(x_44)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_44;
}
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_43);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_44);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_52, x_46, x_51, x_48, x_3, x_43);
return x_53;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_3);
lean_dec(x_1);
x_58 = lean_ctor_get(x_41, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_60 = x_41;
} else {
 lean_dec_ref(x_41);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_62 = lean_ctor_get(x_3, 0);
x_63 = lean_ctor_get(x_3, 1);
x_64 = lean_ctor_get(x_3, 2);
x_65 = lean_ctor_get(x_3, 3);
x_66 = lean_ctor_get(x_3, 4);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_3);
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_62, sizeof(void*)*1);
x_69 = lean_ctor_get_uint8(x_62, sizeof(void*)*1 + 1);
x_70 = lean_ctor_get_uint8(x_62, sizeof(void*)*1 + 2);
x_71 = lean_ctor_get_uint8(x_62, sizeof(void*)*1 + 3);
x_72 = lean_ctor_get_uint8(x_62, sizeof(void*)*1 + 4);
x_73 = lean_ctor_get_uint8(x_62, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_74 = x_62;
} else {
 lean_dec_ref(x_62);
 x_74 = lean_box(0);
}
x_75 = 2;
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 1, 7);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_68);
lean_ctor_set_uint8(x_76, sizeof(void*)*1 + 1, x_69);
lean_ctor_set_uint8(x_76, sizeof(void*)*1 + 2, x_70);
lean_ctor_set_uint8(x_76, sizeof(void*)*1 + 3, x_71);
lean_ctor_set_uint8(x_76, sizeof(void*)*1 + 4, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*1 + 5, x_73);
lean_ctor_set_uint8(x_76, sizeof(void*)*1 + 6, x_75);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_63);
lean_ctor_set(x_77, 2, x_64);
lean_ctor_set(x_77, 3, x_65);
lean_ctor_set(x_77, 4, x_66);
x_78 = 0;
lean_inc(x_77);
x_79 = l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs(x_2, x_78, x_77, x_4);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
if (lean_obj_tag(x_83) == 3)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_84);
lean_dec(x_82);
x_93 = l_Array_empty___closed__1;
x_94 = l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_93, x_77, x_81);
lean_dec(x_1);
return x_94;
}
else
{
lean_object* x_95; 
x_95 = lean_box(0);
x_85 = x_95;
goto block_92;
}
block_92:
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_85);
lean_inc(x_1);
x_86 = l___private_Init_Lean_Meta_DiscrTree_16__getStarResult___rarg(x_1);
x_87 = l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_83);
lean_dec(x_83);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
lean_dec(x_84);
lean_dec(x_77);
if (lean_is_scalar(x_82)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_82;
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_81);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_82);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_unsigned_to_nat(0u);
x_91 = l___private_Init_Lean_Meta_DiscrTree_17__getUnifyAux___main___rarg(x_90, x_84, x_89, x_86, x_77, x_81);
return x_91;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_77);
lean_dec(x_1);
x_96 = lean_ctor_get(x_79, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_79, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_98 = x_79;
} else {
 lean_dec_ref(x_79);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getUnify___rarg), 4, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__2___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Meta_DiscrTree_getUnify___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__7___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_foldlMAux___main___at_Lean_Meta_DiscrTree_getUnify___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getUnify___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Init_Lean_Meta_FunInfo(lean_object*);
lean_object* initialize_Init_Lean_Meta_InferType(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_DiscrTree(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_FunInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_InferType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_DiscrTree_Key_hasLess = _init_l_Lean_Meta_DiscrTree_Key_hasLess();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_hasLess);
l_Lean_Meta_DiscrTree_Key_format___closed__1 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__1);
l_Lean_Meta_DiscrTree_Key_format___closed__2 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__2);
l_Lean_Meta_DiscrTree_Key_format___closed__3 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__3);
l_Lean_Meta_DiscrTree_Key_format___closed__4 = _init_l_Lean_Meta_DiscrTree_Key_format___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_format___closed__4);
l_Lean_Meta_DiscrTree_Key_hasFormat___closed__1 = _init_l_Lean_Meta_DiscrTree_Key_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_hasFormat___closed__1);
l_Lean_Meta_DiscrTree_Key_hasFormat = _init_l_Lean_Meta_DiscrTree_Key_hasFormat();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Key_hasFormat);
l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1 = _init_l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_inhabited___closed__1);
l_Lean_Meta_DiscrTree_empty___closed__1 = _init_l_Lean_Meta_DiscrTree_empty___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_empty___closed__1);
l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__1 = _init_l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__1);
l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__2 = _init_l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId___closed__2);
l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId = _init_l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_1__tmpMVarId);
l___private_Init_Lean_Meta_DiscrTree_2__tmpStar___closed__1 = _init_l___private_Init_Lean_Meta_DiscrTree_2__tmpStar___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_2__tmpStar___closed__1);
l___private_Init_Lean_Meta_DiscrTree_2__tmpStar = _init_l___private_Init_Lean_Meta_DiscrTree_2__tmpStar();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_2__tmpStar);
l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__1 = _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__1);
l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__2 = _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__2);
l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__3 = _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__3);
l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__4 = _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__4();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__4);
l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__5 = _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__5();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__5);
l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__6 = _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__6();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__6);
l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__7 = _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__7();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__7);
l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__8 = _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__8();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__8);
l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__9 = _init_l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__9();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_6__shouldAddAsStar___closed__9);
l___private_Init_Lean_Meta_DiscrTree_8__initCapacity = _init_l___private_Init_Lean_Meta_DiscrTree_8__initCapacity();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_8__initCapacity);
l_Lean_Meta_DiscrTree_mkPath___closed__1 = _init_l_Lean_Meta_DiscrTree_mkPath___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_mkPath___closed__1);
l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__1 = _init_l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__1);
l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2 = _init_l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__2);
l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__3 = _init_l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at___private_Init_Lean_Meta_DiscrTree_11__insertAux___main___spec__2___rarg___closed__3);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__1);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__2);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__3);
l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4 = _init_l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___rarg___closed__4);
l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__1 = _init_l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__1();
lean_mark_persistent(l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__1);
l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2 = _init_l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2();
lean_mark_persistent(l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2);
l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__1 = _init_l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__1);
l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__2 = _init_l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__2);
l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__3 = _init_l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___main___rarg___closed__3);
l_Lean_Meta_DiscrTree_format___rarg___closed__1 = _init_l_Lean_Meta_DiscrTree_format___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_format___rarg___closed__1);
l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1 = _init_l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__1);
l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__2 = _init_l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_DiscrTree_12__getKeyArgs___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
