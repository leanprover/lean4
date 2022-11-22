// Lean compiler output
// Module: Lean.Meta.UnificationHint
// Imports: Init Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.Meta.DiscrTree Lean.Meta.SynthInstance
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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_UnificationHints_add___spec__28(uint8_t, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__15;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object*);
lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__27(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3(uint8_t, lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_Format_join(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__23(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__7;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2723_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956_(lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash___rarg(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__15(uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__7;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__2;
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__14;
lean_object* l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__3;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__10;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__9;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__11;
static lean_object* l_Lean_Meta_addUnificationHint___lambda__1___closed__2;
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__20;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_discrTree___default;
lean_object* l_Lean_withTraceNode___at_Lean_Meta_processPostponed___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_object*, uint8_t);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__3;
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__6(uint8_t);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__4;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_UnificationHints_add___spec__10(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__7;
lean_object* l_Lean_Meta_getPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7(uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__12;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__16;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(uint8_t, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_hash___rarg___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__10;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___closed__2;
static lean_object* l_Lean_Meta_UnificationHints_discrTree___default___closed__1;
static lean_object* l_Lean_Meta_addUnificationHint___lambda__1___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2723____closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2;
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedUnificationHints;
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
extern lean_object* l_Lean_Expr_instHashableExpr;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_findField_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1;
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__2;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__20(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___closed__1;
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__16(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11;
static lean_object* l_Lean_Meta_instInhabitedUnificationHints___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry___closed__2;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_UnificationHints_add___spec__28___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__9;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__21(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__7;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__5;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedUnificationHints___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__17(uint8_t, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__3;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__9;
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__6;
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__19(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3;
static lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__11;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1;
static lean_object* l_Lean_Meta_instInhabitedUnificationHints___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__13(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__4;
static lean_object* l_Lean_Meta_instInhabitedUnificationHints___closed__2;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__3;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__1;
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___closed__2;
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
lean_object* l_Lean_exceptBoolEmoji___rarg(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__5;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedUnificationHints___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__22(uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__2;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__2;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__2;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Meta_instToFormatUnificationHints___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__7;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__19;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__6___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__25(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__6___boxed(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4;
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__4;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__2;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__1;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(uint8_t, uint8_t);
lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__6;
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__9;
lean_object* l_Lean_ScopedEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__26(uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1(uint8_t, lean_object*);
static lean_object* l_Lean_Meta_addUnificationHint___lambda__1___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__8;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__5;
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_format___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__5;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__1;
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__8;
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__18;
static lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1;
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__18(uint8_t, lean_object*, size_t, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt___rarg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2;
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__3;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_unificationHintExtension;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__6;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__13;
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__5;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__24(uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHintEntry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHintEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedUnificationHintEntry___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_UnificationHints_discrTree___default___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_DiscrTree_empty(lean_box(0), x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_UnificationHints_discrTree___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_UnificationHints_discrTree___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_hash___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__5;
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" => ", 4);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__3;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__4;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
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
x_10 = l_Lean_Meta_DiscrTree_Key_format___rarg(x_8);
x_11 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(x_1, x_9);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
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
x_30 = l_Lean_Meta_DiscrTree_Key_format___rarg(x_28);
x_31 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(x_1, x_29);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Meta_instToFormatUnificationHints___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = 1;
x_7 = l_Lean_Name_toString(x_5, x_6);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
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
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_2);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = l_Std_Format_joinSep___at_Lean_Meta_instToFormatUnificationHints___spec__5(x_4, x_2);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[]", 2);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__4;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__6;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__7;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__2;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_3 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__5;
x_4 = l_Std_Format_joinSep___at_Lean_Meta_instToFormatUnificationHints___spec__5(x_1, x_3);
x_5 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__9;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__8;
x_10 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 0;
x_12 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("node", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(uint8_t x_1, lean_object* x_2) {
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
x_8 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3(x_1, x_6, x_7);
x_9 = l_Std_Format_join(x_8);
if (x_5 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_10 = lean_array_to_list(lean_box(0), x_3);
x_11 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(x_10);
x_12 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__6;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
x_19 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
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
x_28 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__7;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
x_30 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__6(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__6___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_Meta_DiscrTree_Key_format___rarg(x_3);
x_8 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(x_1, x_4);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
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
static lean_object* _init_l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_3 = lean_box(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__1;
x_6 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__6___rarg(x_2, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 1;
x_3 = l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__6___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__6(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1(x_5, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_6, x_10);
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
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_4, x_12);
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
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_21 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_1, x_7, x_18, x_2, x_10, x_11);
x_5 = lean_box(0);
x_6 = x_20;
x_7 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_19 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_4, x_18);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_22 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_20);
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
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_27);
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
x_39 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_1, x_36, x_37, x_38, x_5, x_6);
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
x_44 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_1, x_41, x_42, x_43, x_5, x_6);
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
x_52 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_64 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_61);
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
x_76 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_1, x_72, x_74, x_75, x_5, x_6);
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
x_85 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8(x_1, x_2, x_84, x_5, x_6);
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
x_93 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
x_94 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7(x_1, x_4, x_91, x_92, lean_box(0), x_84, x_93);
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
x_99 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8(x_1, x_97, x_98, x_5, x_6);
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
x_107 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
x_108 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7(x_1, x_4, x_105, x_106, lean_box(0), x_98, x_107);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_1, x_6, x_9, x_10, x_3, x_4);
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
x_19 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_1, x_14, x_17, x_18, x_3, x_4);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_UnificationHints_add___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_contains___at_Lean_findField_x3f___spec__1(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_2);
return x_4;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_nat_add(x_8, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
lean_inc(x_7);
x_13 = lean_array_get(x_7, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_9);
x_17 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_15, x_14);
lean_dec(x_14);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
x_18 = lean_array_get_size(x_6);
x_19 = lean_nat_dec_lt(x_12, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_array_fget(x_6, x_12);
x_21 = lean_box(0);
x_22 = lean_array_fset(x_6, x_12, x_21);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_3, x_27, x_24);
lean_dec(x_27);
lean_ctor_set(x_20, 1, x_28);
lean_ctor_set(x_20, 0, x_5);
x_29 = lean_array_fset(x_22, x_12, x_20);
lean_dec(x_12);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_4, x_31);
x_33 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_3, x_32, x_30);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_fset(x_22, x_12, x_34);
lean_dec(x_12);
return x_35;
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
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_14);
x_37 = lean_nat_dec_eq(x_12, x_8);
if (x_37 == 0)
{
lean_dec(x_8);
x_8 = x_12;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_4, x_39);
x_41 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_2, x_3, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_5);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_8, x_39);
lean_dec(x_8);
x_44 = l_Array_insertAt_x21___rarg(x_6, x_43, x_42);
lean_dec(x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
x_10 = lean_array_get(x_7, x_6, x_9);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_12, x_11);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_7);
x_15 = lean_array_get_size(x_6);
x_16 = lean_nat_dec_lt(x_9, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_array_fget(x_6, x_9);
x_18 = lean_box(0);
x_19 = lean_array_fset(x_6, x_9, x_18);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
x_25 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_3, x_24, x_21);
lean_dec(x_24);
lean_ctor_set(x_17, 1, x_25);
lean_ctor_set(x_17, 0, x_5);
x_26 = lean_array_fset(x_19, x_9, x_17);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_4, x_28);
x_30 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_3, x_29, x_27);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_fset(x_19, x_9, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_inc(x_7);
x_33 = l_Array_back___rarg(x_7, x_6);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_34, x_11);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Meta_DiscrTree_Key_lt___rarg(x_11, x_34);
lean_dec(x_34);
lean_dec(x_11);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_7);
x_37 = lean_array_get_size(x_6);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_37, x_38);
x_40 = lean_nat_dec_lt(x_39, x_37);
lean_dec(x_37);
if (x_40 == 0)
{
lean_dec(x_39);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_array_fget(x_6, x_39);
x_42 = lean_box(0);
x_43 = lean_array_fset(x_6, x_39, x_42);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = lean_nat_add(x_4, x_38);
x_48 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_3, x_47, x_45);
lean_dec(x_47);
lean_ctor_set(x_41, 1, x_48);
lean_ctor_set(x_41, 0, x_5);
x_49 = lean_array_fset(x_43, x_39, x_41);
lean_dec(x_39);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_nat_add(x_4, x_38);
x_52 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_3, x_51, x_50);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_5);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_fset(x_43, x_39, x_53);
lean_dec(x_39);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_array_get_size(x_6);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_sub(x_55, x_56);
lean_dec(x_55);
x_58 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_7);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_4, x_59);
x_61 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_2, x_3, x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_5);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_array_push(x_6, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_4, x_64);
x_66 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_2, x_3, x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_5);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Array_insertAt_x21___rarg(x_6, x_9, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_7);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_4, x_69);
x_71 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_2, x_3, x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_5);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_push(x_6, x_72);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_UnificationHints_add___spec__10(x_7, x_3);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_fget(x_2, x_4);
x_13 = l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1;
lean_ctor_set(x_5, 1, x_13);
lean_ctor_set(x_5, 0, x_13);
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_5);
x_15 = l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(x_1, x_2, x_3, x_4, x_12, x_8, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
return x_16;
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
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_UnificationHints_add___spec__10(x_17, x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_array_fget(x_2, x_4);
x_24 = l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(x_1, x_2, x_3, x_4, x_23, x_18, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__15(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_21 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__14(x_1, x_7, x_18, x_2, x_10, x_11);
x_5 = lean_box(0);
x_6 = x_20;
x_7 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__16(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_19 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_4, x_18);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__14(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_22 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_20);
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
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_27);
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
x_39 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__14(x_1, x_36, x_37, x_38, x_5, x_6);
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
x_44 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__14(x_1, x_41, x_42, x_43, x_5, x_6);
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
x_52 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_64 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_61);
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
x_76 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__14(x_1, x_72, x_74, x_75, x_5, x_6);
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
x_85 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__16(x_1, x_2, x_84, x_5, x_6);
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
x_93 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
x_94 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__15(x_1, x_4, x_91, x_92, lean_box(0), x_84, x_93);
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
x_99 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__16(x_1, x_97, x_98, x_5, x_6);
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
x_107 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
x_108 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__15(x_1, x_4, x_105, x_106, lean_box(0), x_98, x_107);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__13(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__14(x_1, x_6, x_9, x_10, x_3, x_4);
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
x_19 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__14(x_1, x_14, x_17, x_18, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__19(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_6, x_10);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__18(uint8_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_4, x_12);
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
x_24 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__19(x_1, x_21, x_22, lean_box(0), x_23, x_4);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__17(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Key_hash___rarg(x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__18(x_1, x_4, x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__22(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_21 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__21(x_1, x_7, x_18, x_2, x_10, x_11);
x_5 = lean_box(0);
x_6 = x_20;
x_7 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__23(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_19 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_4, x_18);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__21(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_22 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_20);
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
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_27);
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
x_39 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__21(x_1, x_36, x_37, x_38, x_5, x_6);
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
x_44 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__21(x_1, x_41, x_42, x_43, x_5, x_6);
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
x_52 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_64 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_61);
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
x_76 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__21(x_1, x_72, x_74, x_75, x_5, x_6);
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
x_85 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__23(x_1, x_2, x_84, x_5, x_6);
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
x_93 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
x_94 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__22(x_1, x_4, x_91, x_92, lean_box(0), x_84, x_93);
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
x_99 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__23(x_1, x_97, x_98, x_5, x_6);
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
x_107 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
x_108 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__22(x_1, x_4, x_105, x_106, lean_box(0), x_98, x_107);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__20(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__21(x_1, x_6, x_9, x_10, x_3, x_4);
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
x_19 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__21(x_1, x_14, x_17, x_18, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__26(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_21 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__25(x_1, x_7, x_18, x_2, x_10, x_11);
x_5 = lean_box(0);
x_6 = x_20;
x_7 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__27(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_19 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_4, x_18);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__25(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_22 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_20);
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
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_27);
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
x_39 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__25(x_1, x_36, x_37, x_38, x_5, x_6);
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
x_44 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__25(x_1, x_41, x_42, x_43, x_5, x_6);
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
x_52 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_64 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_106____rarg(x_5, x_61);
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
x_76 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__25(x_1, x_72, x_74, x_75, x_5, x_6);
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
x_85 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__27(x_1, x_2, x_84, x_5, x_6);
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
x_93 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
x_94 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__26(x_1, x_4, x_91, x_92, lean_box(0), x_84, x_93);
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
x_99 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__27(x_1, x_97, x_98, x_5, x_6);
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
x_107 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
x_108 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__26(x_1, x_4, x_105, x_106, lean_box(0), x_98, x_107);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__24(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__25(x_1, x_6, x_9, x_10, x_3, x_4);
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
x_19 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__25(x_1, x_14, x_17, x_18, x_3, x_4);
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_UnificationHints_add___spec__28(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_box(0), x_1);
x_4 = lean_panic_fn(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.DiscrTree", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.DiscrTree.insertCore", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid key sequence", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1;
x_2 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(358u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Init_Util_0__outOfBounds___rarg(x_8);
lean_inc(x_11);
lean_inc(x_2);
x_12 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(x_1, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_3, x_4, x_13);
lean_dec(x_3);
x_15 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(x_1, x_2, x_11, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_3, x_4, x_17, x_16);
lean_dec(x_3);
x_19 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__13(x_1, x_2, x_11, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_20 = lean_array_fget(x_3, x_7);
lean_inc(x_20);
lean_inc(x_2);
x_21 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__17(x_1, x_2, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes(x_1, lean_box(0), x_3, x_4, x_22);
lean_dec(x_3);
x_24 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__20(x_1, x_2, x_20, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_unsigned_to_nat(1u);
x_27 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_3, x_4, x_26, x_25);
lean_dec(x_3);
x_28 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__24(x_1, x_2, x_20, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4;
x_30 = l_panic___at_Lean_Meta_UnificationHints_add___spec__28(x_1, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = 1;
x_6 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(x_5, x_1, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__15(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__16(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__14(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__13(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__19(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__18(x_5, x_2, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__17(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__22(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__23(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__21(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__20(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__26(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__27(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__25(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__24(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_UnificationHints_add___spec__28___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_panic___at_Lean_Meta_UnificationHints_add___spec__28(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unificationHintExtension", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_UnificationHints_add), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__4;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__5;
x_3 = l_Lean_Meta_UnificationHints_discrTree___default___closed__1;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__6;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__7;
x_3 = l_Lean_registerSimpleScopedEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid unification hint constraint, unexpected term", 52);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2;
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_indentExpr(x_1);
x_6 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__4;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_13 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_push(x_1, x_2);
x_6 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(x_3, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid unification hint constraint, unexpected dependency", 58);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = l_Lean_Expr_hasLooseBVars(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_5);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___lambda__1(x_2, x_10, x_4, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_14 = l_Lean_indentExpr(x_1);
x_15 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = l_Lean_Expr_hasLooseBVars(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___lambda__1(x_2, x_19, x_4, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_2);
x_23 = l_Lean_indentExpr(x_1);
x_24 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
else
{
lean_object* x_29; 
x_29 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(x_1);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_2);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_array_to_list(lean_box(0), x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_29, 0, x_36);
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_array_to_list(lean_box(0), x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1;
x_3 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid unification hint, failed to unify constraint left-hand-side", 67);
return x_1;
}
}
static lean_object* _init_l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nwith right-hand-side", 21);
return x_1;
}
}
static lean_object* _init_l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_11);
x_13 = l_Lean_Meta_isExprDefEq(x_11, x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_10);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_indentExpr(x_11);
x_18 = l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_indentExpr(x_12);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_25, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_12);
lean_dec(x_11);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_dec(x_13);
x_1 = x_10;
x_6 = x_31;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid unification hint, failed to unify pattern left-hand-side", 64);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_11);
x_13 = l_Lean_Meta_isExprDefEq(x_11, x_12, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_indentExpr(x_11);
x_18 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_indentExpr(x_12);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_25, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_13, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_13, 0, x_29);
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
return x_8;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_8);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__3;
x_2 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__5;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__6;
x_4 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__9;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (x_3) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_6);
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 4);
lean_dec(x_14);
x_15 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_13, x_2);
x_16 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
lean_ctor_set(x_10, 4, x_16);
lean_ctor_set(x_10, 0, x_15);
x_17 = lean_st_ref_set(x_7, x_10, x_11);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_7, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_take(x_5, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 1);
lean_dec(x_25);
x_26 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
lean_ctor_set(x_22, 1, x_26);
x_27 = lean_st_ref_set(x_5, x_22, x_23);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 2);
x_36 = lean_ctor_get(x_22, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_37 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
x_39 = lean_st_ref_set(x_5, x_38, x_23);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = lean_ctor_get(x_10, 1);
x_46 = lean_ctor_get(x_10, 2);
x_47 = lean_ctor_get(x_10, 3);
x_48 = lean_ctor_get(x_10, 5);
x_49 = lean_ctor_get(x_10, 6);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_10);
x_50 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_44, x_2);
x_51 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_46);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_48);
lean_ctor_set(x_52, 6, x_49);
x_53 = lean_st_ref_set(x_7, x_52, x_11);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_get(x_7, x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_take(x_5, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 3);
lean_inc(x_62);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_63 = x_58;
} else {
 lean_dec_ref(x_58);
 x_63 = lean_box(0);
}
x_64 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 4, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_62);
x_66 = lean_st_ref_set(x_5, x_65, x_59);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_6);
x_71 = lean_st_ref_take(x_7, x_8);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 4);
lean_dec(x_76);
x_77 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_75, x_2);
x_78 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
lean_ctor_set(x_72, 4, x_78);
lean_ctor_set(x_72, 0, x_77);
x_79 = lean_st_ref_set(x_7, x_72, x_73);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_st_ref_get(x_7, x_80);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_st_ref_take(x_5, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_84, 1);
lean_dec(x_87);
x_88 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
lean_ctor_set(x_84, 1, x_88);
x_89 = lean_st_ref_set(x_5, x_84, x_85);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
x_92 = lean_box(0);
lean_ctor_set(x_89, 0, x_92);
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_84, 0);
x_97 = lean_ctor_get(x_84, 2);
x_98 = lean_ctor_get(x_84, 3);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_84);
x_99 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
x_100 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_100, 3, x_98);
x_101 = lean_st_ref_set(x_5, x_100, x_85);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_106 = lean_ctor_get(x_72, 0);
x_107 = lean_ctor_get(x_72, 1);
x_108 = lean_ctor_get(x_72, 2);
x_109 = lean_ctor_get(x_72, 3);
x_110 = lean_ctor_get(x_72, 5);
x_111 = lean_ctor_get(x_72, 6);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_72);
x_112 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_106, x_2);
x_113 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
x_114 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_107);
lean_ctor_set(x_114, 2, x_108);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set(x_114, 4, x_113);
lean_ctor_set(x_114, 5, x_110);
lean_ctor_set(x_114, 6, x_111);
x_115 = lean_st_ref_set(x_7, x_114, x_73);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_st_ref_get(x_7, x_116);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_st_ref_take(x_5, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 3);
lean_inc(x_124);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 x_125 = x_120;
} else {
 lean_dec_ref(x_120);
 x_125 = lean_box(0);
}
x_126 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 4, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_123);
lean_ctor_set(x_127, 3, x_124);
x_128 = lean_st_ref_set(x_5, x_127, x_121);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
x_131 = lean_box(0);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
}
default: 
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_6, 6);
lean_inc(x_133);
lean_dec(x_6);
x_134 = lean_st_ref_take(x_7, x_8);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_138 = lean_ctor_get(x_135, 0);
x_139 = lean_ctor_get(x_135, 4);
lean_dec(x_139);
x_140 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_138, x_133, x_2);
x_141 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
lean_ctor_set(x_135, 4, x_141);
lean_ctor_set(x_135, 0, x_140);
x_142 = lean_st_ref_set(x_7, x_135, x_136);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_st_ref_get(x_7, x_143);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_st_ref_take(x_5, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_147, 1);
lean_dec(x_150);
x_151 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
lean_ctor_set(x_147, 1, x_151);
x_152 = lean_st_ref_set(x_5, x_147, x_148);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_152, 0);
lean_dec(x_154);
x_155 = lean_box(0);
lean_ctor_set(x_152, 0, x_155);
return x_152;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
lean_dec(x_152);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_159 = lean_ctor_get(x_147, 0);
x_160 = lean_ctor_get(x_147, 2);
x_161 = lean_ctor_get(x_147, 3);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_147);
x_162 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
x_163 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_163, 2, x_160);
lean_ctor_set(x_163, 3, x_161);
x_164 = lean_st_ref_set(x_5, x_163, x_148);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_166 = x_164;
} else {
 lean_dec_ref(x_164);
 x_166 = lean_box(0);
}
x_167 = lean_box(0);
if (lean_is_scalar(x_166)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_166;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_165);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_169 = lean_ctor_get(x_135, 0);
x_170 = lean_ctor_get(x_135, 1);
x_171 = lean_ctor_get(x_135, 2);
x_172 = lean_ctor_get(x_135, 3);
x_173 = lean_ctor_get(x_135, 5);
x_174 = lean_ctor_get(x_135, 6);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_135);
x_175 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_169, x_133, x_2);
x_176 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
x_177 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_170);
lean_ctor_set(x_177, 2, x_171);
lean_ctor_set(x_177, 3, x_172);
lean_ctor_set(x_177, 4, x_176);
lean_ctor_set(x_177, 5, x_173);
lean_ctor_set(x_177, 6, x_174);
x_178 = lean_st_ref_set(x_7, x_177, x_136);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_st_ref_get(x_7, x_179);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_st_ref_take(x_5, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 3);
lean_inc(x_187);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 x_188 = x_183;
} else {
 lean_dec_ref(x_183);
 x_188 = lean_box(0);
}
x_189 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 4, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_185);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set(x_190, 2, x_186);
lean_ctor_set(x_190, 3, x_187);
x_191 = lean_st_ref_set(x_5, x_190, x_184);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_193 = x_191;
} else {
 lean_dec_ref(x_191);
 x_193 = lean_box(0);
}
x_194 = lean_box(0);
if (lean_is_scalar(x_193)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_193;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_192);
return x_195;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid unification hint, it must be a definition", 49);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_addUnificationHint___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_unificationHintExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_ConstantInfo_value_x3f(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = l_Lean_Meta_addUnificationHint___lambda__1___closed__2;
x_13 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_12, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
lean_inc(x_3);
x_16 = l_Lean_Meta_lambdaMetaTelescope(x_14, x_15, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_22, x_3, x_4, x_5, x_6, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_Meta_DiscrTree_mkPath(x_27, x_26, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(x_24, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_1);
x_34 = l_Lean_Meta_addUnificationHint___lambda__1___closed__3;
x_35 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1(x_34, x_33, x_2, x_3, x_4, x_5, x_6, x_32);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
return x_28;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
return x_8;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_8);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lambda__1___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_addUnificationHint___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_addUnificationHint(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_3);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_3);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_3);
lean_ctor_set_uint8(x_5, 12, x_3);
lean_ctor_set_uint8(x_5, 13, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__3;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__1;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__6;
x_4 = l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__8;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__9;
x_4 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__10;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__5;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Attribute_Builtin_ensureNoArgs(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__11;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__7;
lean_inc(x_5);
lean_inc(x_13);
x_16 = l_Lean_Meta_addUnificationHint(x_1, x_3, x_15, x_13, x_4, x_5, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_5, x_17);
lean_dec(x_5);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
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
lean_dec(x_1);
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attribute cannot be erased", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__2;
x_6 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__4;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__6;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("UnificationHint", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__10;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__12;
x_2 = lean_unsigned_to_nat(956u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unification_hint", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unification hint", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__13;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__15;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__16;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__17;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__18;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__19;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__20;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 2;
lean_ctor_set_uint8(x_9, 5, x_11);
x_12 = lean_is_expr_def_eq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get_uint8(x_9, 0);
x_22 = lean_ctor_get_uint8(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, 2);
x_24 = lean_ctor_get_uint8(x_9, 3);
x_25 = lean_ctor_get_uint8(x_9, 4);
x_26 = lean_ctor_get_uint8(x_9, 6);
x_27 = lean_ctor_get_uint8(x_9, 7);
x_28 = lean_ctor_get_uint8(x_9, 8);
x_29 = lean_ctor_get_uint8(x_9, 9);
x_30 = lean_ctor_get_uint8(x_9, 10);
x_31 = lean_ctor_get_uint8(x_9, 11);
x_32 = lean_ctor_get_uint8(x_9, 12);
x_33 = lean_ctor_get_uint8(x_9, 13);
lean_dec(x_9);
x_34 = 2;
x_35 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_35, 0, x_21);
lean_ctor_set_uint8(x_35, 1, x_22);
lean_ctor_set_uint8(x_35, 2, x_23);
lean_ctor_set_uint8(x_35, 3, x_24);
lean_ctor_set_uint8(x_35, 4, x_25);
lean_ctor_set_uint8(x_35, 5, x_34);
lean_ctor_set_uint8(x_35, 6, x_26);
lean_ctor_set_uint8(x_35, 7, x_27);
lean_ctor_set_uint8(x_35, 8, x_28);
lean_ctor_set_uint8(x_35, 9, x_29);
lean_ctor_set_uint8(x_35, 10, x_30);
lean_ctor_set_uint8(x_35, 11, x_31);
lean_ctor_set_uint8(x_35, 12, x_32);
lean_ctor_set_uint8(x_35, 13, x_33);
lean_ctor_set(x_3, 0, x_35);
x_36 = lean_is_expr_def_eq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_3, 2);
x_48 = lean_ctor_get(x_3, 3);
x_49 = lean_ctor_get(x_3, 4);
x_50 = lean_ctor_get(x_3, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_3);
x_51 = lean_ctor_get_uint8(x_45, 0);
x_52 = lean_ctor_get_uint8(x_45, 1);
x_53 = lean_ctor_get_uint8(x_45, 2);
x_54 = lean_ctor_get_uint8(x_45, 3);
x_55 = lean_ctor_get_uint8(x_45, 4);
x_56 = lean_ctor_get_uint8(x_45, 6);
x_57 = lean_ctor_get_uint8(x_45, 7);
x_58 = lean_ctor_get_uint8(x_45, 8);
x_59 = lean_ctor_get_uint8(x_45, 9);
x_60 = lean_ctor_get_uint8(x_45, 10);
x_61 = lean_ctor_get_uint8(x_45, 11);
x_62 = lean_ctor_get_uint8(x_45, 12);
x_63 = lean_ctor_get_uint8(x_45, 13);
if (lean_is_exclusive(x_45)) {
 x_64 = x_45;
} else {
 lean_dec_ref(x_45);
 x_64 = lean_box(0);
}
x_65 = 2;
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 0, 14);
} else {
 x_66 = x_64;
}
lean_ctor_set_uint8(x_66, 0, x_51);
lean_ctor_set_uint8(x_66, 1, x_52);
lean_ctor_set_uint8(x_66, 2, x_53);
lean_ctor_set_uint8(x_66, 3, x_54);
lean_ctor_set_uint8(x_66, 4, x_55);
lean_ctor_set_uint8(x_66, 5, x_65);
lean_ctor_set_uint8(x_66, 6, x_56);
lean_ctor_set_uint8(x_66, 7, x_57);
lean_ctor_set_uint8(x_66, 8, x_58);
lean_ctor_set_uint8(x_66, 9, x_59);
lean_ctor_set_uint8(x_66, 10, x_60);
lean_ctor_set_uint8(x_66, 11, x_61);
lean_ctor_set_uint8(x_66, 12, x_62);
lean_ctor_set_uint8(x_66, 13, x_63);
x_67 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_46);
lean_ctor_set(x_67, 2, x_47);
lean_ctor_set(x_67, 3, x_48);
lean_ctor_set(x_67, 4, x_49);
lean_ctor_set(x_67, 5, x_50);
x_68 = lean_is_expr_def_eq(x_1, x_2, x_67, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_11;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_2);
x_1 = x_17;
x_2 = x_21;
x_7 = x_20;
goto _start;
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_is_expr_def_eq(x_12, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2;
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
lean_inc(x_1);
{
lean_object* _tmp_1 = x_11;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_7 = x_23;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_24; 
x_14 = lean_array_uget(x_3, x_5);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_6, 1);
x_26 = lean_ctor_get(x_6, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 2);
lean_inc(x_29);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_14);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_6);
x_15 = x_31;
x_16 = x_11;
goto block_23;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_33 = lean_ctor_get(x_25, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = lean_array_fget(x_27, x_28);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_28, x_38);
lean_dec(x_28);
lean_ctor_set(x_25, 1, x_39);
x_40 = 3;
x_41 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_37, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_14);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_6);
x_15 = x_42;
x_16 = x_11;
goto block_23;
}
else
{
lean_object* x_43; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_43 = lean_infer_type(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_46 = l_Lean_Meta_trySynthInstance(x_44, x_1, x_7, x_8, x_9, x_10, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_50 = l_Lean_Meta_isExprDefEq(x_14, x_49, x_7, x_8, x_9, x_10, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
lean_ctor_set(x_6, 0, x_54);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_6);
x_15 = x_55;
x_16 = x_53;
goto block_23;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_6);
x_15 = x_57;
x_16 = x_56;
goto block_23;
}
}
else
{
uint8_t x_58; 
lean_dec(x_25);
lean_free_object(x_6);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_47);
lean_dec(x_14);
x_62 = lean_ctor_get(x_46, 1);
lean_inc(x_62);
lean_dec(x_46);
x_63 = l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
lean_ctor_set(x_6, 0, x_63);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_6);
x_15 = x_64;
x_16 = x_62;
goto block_23;
}
}
else
{
uint8_t x_65; 
lean_dec(x_25);
lean_free_object(x_6);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_46);
if (x_65 == 0)
{
return x_46;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_46, 0);
x_67 = lean_ctor_get(x_46, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_46);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_25);
lean_free_object(x_6);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_43);
if (x_69 == 0)
{
return x_43;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_43, 0);
x_71 = lean_ctor_get(x_43, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_43);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; 
lean_dec(x_25);
x_73 = lean_array_fget(x_27, x_28);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_28, x_75);
lean_dec(x_28);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_27);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_29);
x_78 = 3;
x_79 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_74, x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_14);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_77);
lean_ctor_set(x_6, 0, x_2);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_6);
x_15 = x_80;
x_16 = x_11;
goto block_23;
}
else
{
lean_object* x_81; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_81 = lean_infer_type(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_84 = l_Lean_Meta_trySynthInstance(x_82, x_1, x_7, x_8, x_9, x_10, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 1)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_88 = l_Lean_Meta_isExprDefEq(x_14, x_87, x_7, x_8, x_9, x_10, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
lean_ctor_set(x_6, 1, x_77);
lean_ctor_set(x_6, 0, x_92);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_6);
x_15 = x_93;
x_16 = x_91;
goto block_23;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_dec(x_88);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_77);
lean_ctor_set(x_6, 0, x_2);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_6);
x_15 = x_95;
x_16 = x_94;
goto block_23;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_77);
lean_free_object(x_6);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_ctor_get(x_88, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_88, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_98 = x_88;
} else {
 lean_dec_ref(x_88);
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
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_85);
lean_dec(x_14);
x_100 = lean_ctor_get(x_84, 1);
lean_inc(x_100);
lean_dec(x_84);
x_101 = l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
lean_ctor_set(x_6, 1, x_77);
lean_ctor_set(x_6, 0, x_101);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_6);
x_15 = x_102;
x_16 = x_100;
goto block_23;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_77);
lean_free_object(x_6);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_ctor_get(x_84, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_84, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_105 = x_84;
} else {
 lean_dec_ref(x_84);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_77);
lean_free_object(x_6);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_107 = lean_ctor_get(x_81, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_81, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_109 = x_81;
} else {
 lean_dec_ref(x_81);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_6, 1);
lean_inc(x_111);
lean_dec(x_6);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 2);
lean_inc(x_114);
x_115 = lean_nat_dec_lt(x_113, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_14);
lean_inc(x_2);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_2);
lean_ctor_set(x_116, 1, x_111);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_15 = x_117;
x_16 = x_11;
goto block_23;
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; 
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
 x_118 = lean_box(0);
}
x_119 = lean_array_fget(x_112, x_113);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_add(x_113, x_121);
lean_dec(x_113);
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(0, 3, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_112);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_114);
x_124 = 3;
x_125 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_120, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_14);
lean_inc(x_2);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_2);
lean_ctor_set(x_126, 1, x_123);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_15 = x_127;
x_16 = x_11;
goto block_23;
}
else
{
lean_object* x_128; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_128 = lean_infer_type(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_131 = l_Lean_Meta_trySynthInstance(x_129, x_1, x_7, x_8, x_9, x_10, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 1)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_135 = l_Lean_Meta_isExprDefEq(x_14, x_134, x_7, x_8, x_9, x_10, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_123);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_15 = x_141;
x_16 = x_138;
goto block_23;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
lean_dec(x_135);
lean_inc(x_2);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_2);
lean_ctor_set(x_143, 1, x_123);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_15 = x_144;
x_16 = x_142;
goto block_23;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_123);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_ctor_get(x_135, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_135, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_147 = x_135;
} else {
 lean_dec_ref(x_135);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_132);
lean_dec(x_14);
x_149 = lean_ctor_get(x_131, 1);
lean_inc(x_149);
lean_dec(x_131);
x_150 = l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_123);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_15 = x_152;
x_16 = x_149;
goto block_23;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_123);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_ctor_get(x_131, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_131, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_155 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_123);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_157 = lean_ctor_get(x_128, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_128, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_159 = x_128;
} else {
 lean_dec_ref(x_128);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
}
block_23:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_19;
x_11 = x_16;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_toSubarray___rarg(x_1, x_11, x_10);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_get_size(x_3);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3(x_2, x_2, x_3, x_15, x_16, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___closed__1;
x_22 = lean_box(0);
x_23 = lean_apply_6(x_21, x_22, x_5, x_6, x_7, x_8, x_20);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_14 = l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2(x_13, x_11, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2(x_3, x_2, x_4, x_12, x_6, x_7, x_8, x_9, x_17);
lean_dec(x_4);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" succeeded, applying constraints", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = l_Lean_Meta_saveState___rarg(x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_take(x_7, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_38; lean_object* x_39; lean_object* x_78; 
x_23 = lean_ctor_get(x_18, 5);
lean_dec(x_23);
x_24 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1;
lean_ctor_set(x_18, 5, x_24);
x_25 = lean_st_ref_set(x_7, x_17, x_19);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_3);
x_78 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_ConstantInfo_levelParams(x_79);
x_82 = lean_box(0);
x_83 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_81, x_82, x_6, x_7, x_8, x_9, x_80);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_9);
lean_inc(x_8);
x_86 = l_Lean_Core_instantiateValueLevelParams(x_79, x_84, x_8, x_9, x_85);
lean_dec(x_79);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_128; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_box(0);
lean_inc(x_6);
x_90 = l_Lean_Meta_lambdaMetaTelescope(x_87, x_89, x_6, x_7, x_8, x_9, x_88);
lean_dec(x_87);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_128 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_96);
if (lean_obj_tag(x_128) == 0)
{
lean_dec(x_128);
lean_dec(x_2);
lean_dec(x_1);
x_97 = x_89;
x_98 = x_93;
goto block_127;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_129 = lean_ctor_get(x_6, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_6, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_6, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_6, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_6, 4);
lean_inc(x_134);
x_135 = lean_ctor_get(x_6, 5);
lean_inc(x_135);
x_136 = !lean_is_exclusive(x_129);
if (x_136 == 0)
{
uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = 0;
lean_ctor_set_uint8(x_129, 8, x_137);
x_138 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_138, 0, x_129);
lean_ctor_set(x_138, 1, x_131);
lean_ctor_set(x_138, 2, x_132);
lean_ctor_set(x_138, 3, x_133);
lean_ctor_set(x_138, 4, x_134);
lean_ctor_set(x_138, 5, x_135);
x_139 = lean_ctor_get(x_130, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_138);
x_141 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_140, x_1, x_138, x_7, x_8, x_9, x_93);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_130);
lean_dec(x_2);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_97 = x_89;
x_98 = x_144;
goto block_127;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_146 = lean_ctor_get(x_139, 1);
lean_inc(x_146);
lean_dec(x_139);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_147 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_146, x_2, x_138, x_7, x_8, x_9, x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_130);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_97 = x_89;
x_98 = x_150;
goto block_127;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_130);
x_97 = x_152;
x_98 = x_151;
goto block_127;
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_130);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
x_153 = lean_ctor_get(x_147, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_147, 1);
lean_inc(x_154);
lean_dec(x_147);
x_30 = x_153;
x_31 = x_154;
goto block_37;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_130);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = lean_ctor_get(x_141, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_141, 1);
lean_inc(x_156);
lean_dec(x_141);
x_30 = x_155;
x_31 = x_156;
goto block_37;
}
}
else
{
uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_157 = lean_ctor_get_uint8(x_129, 0);
x_158 = lean_ctor_get_uint8(x_129, 1);
x_159 = lean_ctor_get_uint8(x_129, 2);
x_160 = lean_ctor_get_uint8(x_129, 3);
x_161 = lean_ctor_get_uint8(x_129, 4);
x_162 = lean_ctor_get_uint8(x_129, 5);
x_163 = lean_ctor_get_uint8(x_129, 6);
x_164 = lean_ctor_get_uint8(x_129, 7);
x_165 = lean_ctor_get_uint8(x_129, 9);
x_166 = lean_ctor_get_uint8(x_129, 10);
x_167 = lean_ctor_get_uint8(x_129, 11);
x_168 = lean_ctor_get_uint8(x_129, 12);
x_169 = lean_ctor_get_uint8(x_129, 13);
lean_dec(x_129);
x_170 = 0;
x_171 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_171, 0, x_157);
lean_ctor_set_uint8(x_171, 1, x_158);
lean_ctor_set_uint8(x_171, 2, x_159);
lean_ctor_set_uint8(x_171, 3, x_160);
lean_ctor_set_uint8(x_171, 4, x_161);
lean_ctor_set_uint8(x_171, 5, x_162);
lean_ctor_set_uint8(x_171, 6, x_163);
lean_ctor_set_uint8(x_171, 7, x_164);
lean_ctor_set_uint8(x_171, 8, x_170);
lean_ctor_set_uint8(x_171, 9, x_165);
lean_ctor_set_uint8(x_171, 10, x_166);
lean_ctor_set_uint8(x_171, 11, x_167);
lean_ctor_set_uint8(x_171, 12, x_168);
lean_ctor_set_uint8(x_171, 13, x_169);
x_172 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_131);
lean_ctor_set(x_172, 2, x_132);
lean_ctor_set(x_172, 3, x_133);
lean_ctor_set(x_172, 4, x_134);
lean_ctor_set(x_172, 5, x_135);
x_173 = lean_ctor_get(x_130, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_172);
x_175 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_174, x_1, x_172, x_7, x_8, x_9, x_93);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_unbox(x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_130);
lean_dec(x_2);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
x_97 = x_89;
x_98 = x_178;
goto block_127;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
lean_dec(x_175);
x_180 = lean_ctor_get(x_173, 1);
lean_inc(x_180);
lean_dec(x_173);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_181 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_180, x_2, x_172, x_7, x_8, x_9, x_179);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; uint8_t x_183; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_unbox(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec(x_130);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec(x_181);
x_97 = x_89;
x_98 = x_184;
goto block_127;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_181, 1);
lean_inc(x_185);
lean_dec(x_181);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_130);
x_97 = x_186;
x_98 = x_185;
goto block_127;
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_130);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
x_187 = lean_ctor_get(x_181, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_181, 1);
lean_inc(x_188);
lean_dec(x_181);
x_30 = x_187;
x_31 = x_188;
goto block_37;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_130);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_189 = lean_ctor_get(x_175, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_175, 1);
lean_inc(x_190);
lean_dec(x_175);
x_30 = x_189;
x_31 = x_190;
goto block_37;
}
}
}
block_127:
{
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_99; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_4);
lean_dec(x_3);
x_99 = 0;
x_38 = x_99;
x_39 = x_98;
goto block_77;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
lean_dec(x_97);
lean_inc(x_4);
x_101 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_98);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_4);
lean_dec(x_3);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_106 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_100, x_89, x_95, x_94, x_105, x_6, x_7, x_8, x_9, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_unbox(x_107);
lean_dec(x_107);
x_38 = x_109;
x_39 = x_108;
goto block_77;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_28);
x_110 = lean_ctor_get(x_106, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_30 = x_110;
x_31 = x_111;
goto block_37;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_112 = lean_ctor_get(x_101, 1);
lean_inc(x_112);
lean_dec(x_101);
x_113 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_113, 0, x_3);
x_114 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
x_117 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_117, x_6, x_7, x_8, x_9, x_112);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_121 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_100, x_89, x_95, x_94, x_119, x_6, x_7, x_8, x_9, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_unbox(x_122);
lean_dec(x_122);
x_38 = x_124;
x_39 = x_123;
goto block_77;
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_28);
x_125 = lean_ctor_get(x_121, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_dec(x_121);
x_30 = x_125;
x_31 = x_126;
goto block_37;
}
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = lean_ctor_get(x_86, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_86, 1);
lean_inc(x_192);
lean_dec(x_86);
x_30 = x_191;
x_31 = x_192;
goto block_37;
}
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_ctor_get(x_78, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_78, 1);
lean_inc(x_194);
lean_dec(x_78);
x_30 = x_193;
x_31 = x_194;
goto block_37;
}
block_37:
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
block_77:
{
if (x_38 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_28);
x_40 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_39);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = 0;
x_44 = lean_box(x_43);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
uint8_t x_49; lean_object* x_50; 
x_49 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_50 = l_Lean_Meta_processPostponed(x_5, x_49, x_6, x_7, x_8, x_9, x_39);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_28);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_53);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_box(x_49);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_box(x_49);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_12);
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
lean_dec(x_50);
x_62 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_PersistentArray_append___rarg(x_28, x_63);
x_66 = l_Lean_Meta_setPostponed(x_65, x_6, x_7, x_8, x_9, x_64);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = 1;
x_70 = lean_box(x_69);
lean_ctor_set(x_66, 0, x_70);
return x_66;
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = 1;
x_73 = lean_box(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_28);
x_75 = lean_ctor_get(x_50, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_50, 1);
lean_inc(x_76);
lean_dec(x_50);
x_30 = x_75;
x_31 = x_76;
goto block_37;
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_214; lean_object* x_215; lean_object* x_246; 
x_195 = lean_ctor_get(x_18, 0);
x_196 = lean_ctor_get(x_18, 1);
x_197 = lean_ctor_get(x_18, 2);
x_198 = lean_ctor_get(x_18, 3);
x_199 = lean_ctor_get(x_18, 4);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_18);
x_200 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1;
x_201 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_201, 0, x_195);
lean_ctor_set(x_201, 1, x_196);
lean_ctor_set(x_201, 2, x_197);
lean_ctor_set(x_201, 3, x_198);
lean_ctor_set(x_201, 4, x_199);
lean_ctor_set(x_201, 5, x_200);
lean_ctor_set(x_17, 1, x_201);
x_202 = lean_st_ref_set(x_7, x_17, x_19);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_203);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
lean_inc(x_3);
x_246 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_206);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lean_ConstantInfo_levelParams(x_247);
x_250 = lean_box(0);
x_251 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_249, x_250, x_6, x_7, x_8, x_9, x_248);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_9);
lean_inc(x_8);
x_254 = l_Lean_Core_instantiateValueLevelParams(x_247, x_252, x_8, x_9, x_253);
lean_dec(x_247);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_296; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_box(0);
lean_inc(x_6);
x_258 = l_Lean_Meta_lambdaMetaTelescope(x_255, x_257, x_6, x_7, x_8, x_9, x_256);
lean_dec(x_255);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec(x_258);
x_262 = lean_ctor_get(x_259, 0);
lean_inc(x_262);
lean_dec(x_259);
x_263 = lean_ctor_get(x_260, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_260, 1);
lean_inc(x_264);
lean_dec(x_260);
x_296 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_264);
if (lean_obj_tag(x_296) == 0)
{
lean_dec(x_296);
lean_dec(x_2);
lean_dec(x_1);
x_265 = x_257;
x_266 = x_261;
goto block_295;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; uint8_t x_305; uint8_t x_306; uint8_t x_307; uint8_t x_308; uint8_t x_309; uint8_t x_310; uint8_t x_311; uint8_t x_312; uint8_t x_313; uint8_t x_314; uint8_t x_315; uint8_t x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_297 = lean_ctor_get(x_6, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 0);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_ctor_get(x_6, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_6, 2);
lean_inc(x_300);
x_301 = lean_ctor_get(x_6, 3);
lean_inc(x_301);
x_302 = lean_ctor_get(x_6, 4);
lean_inc(x_302);
x_303 = lean_ctor_get(x_6, 5);
lean_inc(x_303);
x_304 = lean_ctor_get_uint8(x_297, 0);
x_305 = lean_ctor_get_uint8(x_297, 1);
x_306 = lean_ctor_get_uint8(x_297, 2);
x_307 = lean_ctor_get_uint8(x_297, 3);
x_308 = lean_ctor_get_uint8(x_297, 4);
x_309 = lean_ctor_get_uint8(x_297, 5);
x_310 = lean_ctor_get_uint8(x_297, 6);
x_311 = lean_ctor_get_uint8(x_297, 7);
x_312 = lean_ctor_get_uint8(x_297, 9);
x_313 = lean_ctor_get_uint8(x_297, 10);
x_314 = lean_ctor_get_uint8(x_297, 11);
x_315 = lean_ctor_get_uint8(x_297, 12);
x_316 = lean_ctor_get_uint8(x_297, 13);
if (lean_is_exclusive(x_297)) {
 x_317 = x_297;
} else {
 lean_dec_ref(x_297);
 x_317 = lean_box(0);
}
x_318 = 0;
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(0, 0, 14);
} else {
 x_319 = x_317;
}
lean_ctor_set_uint8(x_319, 0, x_304);
lean_ctor_set_uint8(x_319, 1, x_305);
lean_ctor_set_uint8(x_319, 2, x_306);
lean_ctor_set_uint8(x_319, 3, x_307);
lean_ctor_set_uint8(x_319, 4, x_308);
lean_ctor_set_uint8(x_319, 5, x_309);
lean_ctor_set_uint8(x_319, 6, x_310);
lean_ctor_set_uint8(x_319, 7, x_311);
lean_ctor_set_uint8(x_319, 8, x_318);
lean_ctor_set_uint8(x_319, 9, x_312);
lean_ctor_set_uint8(x_319, 10, x_313);
lean_ctor_set_uint8(x_319, 11, x_314);
lean_ctor_set_uint8(x_319, 12, x_315);
lean_ctor_set_uint8(x_319, 13, x_316);
x_320 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_299);
lean_ctor_set(x_320, 2, x_300);
lean_ctor_set(x_320, 3, x_301);
lean_ctor_set(x_320, 4, x_302);
lean_ctor_set(x_320, 5, x_303);
x_321 = lean_ctor_get(x_298, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_320);
x_323 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_322, x_1, x_320, x_7, x_8, x_9, x_261);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; uint8_t x_325; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_unbox(x_324);
lean_dec(x_324);
if (x_325 == 0)
{
lean_object* x_326; 
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_298);
lean_dec(x_2);
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
lean_dec(x_323);
x_265 = x_257;
x_266 = x_326;
goto block_295;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_dec(x_323);
x_328 = lean_ctor_get(x_321, 1);
lean_inc(x_328);
lean_dec(x_321);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_329 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_328, x_2, x_320, x_7, x_8, x_9, x_327);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; uint8_t x_331; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_unbox(x_330);
lean_dec(x_330);
if (x_331 == 0)
{
lean_object* x_332; 
lean_dec(x_298);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_265 = x_257;
x_266 = x_332;
goto block_295;
}
else
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_329, 1);
lean_inc(x_333);
lean_dec(x_329);
x_334 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_334, 0, x_298);
x_265 = x_334;
x_266 = x_333;
goto block_295;
}
}
else
{
lean_object* x_335; lean_object* x_336; 
lean_dec(x_298);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_205);
lean_dec(x_4);
lean_dec(x_3);
x_335 = lean_ctor_get(x_329, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_329, 1);
lean_inc(x_336);
lean_dec(x_329);
x_207 = x_335;
x_208 = x_336;
goto block_213;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_298);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_205);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_337 = lean_ctor_get(x_323, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_323, 1);
lean_inc(x_338);
lean_dec(x_323);
x_207 = x_337;
x_208 = x_338;
goto block_213;
}
}
block_295:
{
if (lean_obj_tag(x_265) == 0)
{
uint8_t x_267; 
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_4);
lean_dec(x_3);
x_267 = 0;
x_214 = x_267;
x_215 = x_266;
goto block_245;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_268 = lean_ctor_get(x_265, 0);
lean_inc(x_268);
lean_dec(x_265);
lean_inc(x_4);
x_269 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_266);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_unbox(x_270);
lean_dec(x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_4);
lean_dec(x_3);
x_272 = lean_ctor_get(x_269, 1);
lean_inc(x_272);
lean_dec(x_269);
x_273 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_274 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_268, x_257, x_263, x_262, x_273, x_6, x_7, x_8, x_9, x_272);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = lean_unbox(x_275);
lean_dec(x_275);
x_214 = x_277;
x_215 = x_276;
goto block_245;
}
else
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_205);
x_278 = lean_ctor_get(x_274, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_274, 1);
lean_inc(x_279);
lean_dec(x_274);
x_207 = x_278;
x_208 = x_279;
goto block_213;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_280 = lean_ctor_get(x_269, 1);
lean_inc(x_280);
lean_dec(x_269);
x_281 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_281, 0, x_3);
x_282 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_283 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_281);
x_284 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
x_285 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
x_286 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_285, x_6, x_7, x_8, x_9, x_280);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_289 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_268, x_257, x_263, x_262, x_287, x_6, x_7, x_8, x_9, x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
x_292 = lean_unbox(x_290);
lean_dec(x_290);
x_214 = x_292;
x_215 = x_291;
goto block_245;
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_205);
x_293 = lean_ctor_get(x_289, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_289, 1);
lean_inc(x_294);
lean_dec(x_289);
x_207 = x_293;
x_208 = x_294;
goto block_213;
}
}
}
}
}
else
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_205);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_339 = lean_ctor_get(x_254, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_254, 1);
lean_inc(x_340);
lean_dec(x_254);
x_207 = x_339;
x_208 = x_340;
goto block_213;
}
}
else
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_205);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_341 = lean_ctor_get(x_246, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_246, 1);
lean_inc(x_342);
lean_dec(x_246);
x_207 = x_341;
x_208 = x_342;
goto block_213;
}
block_213:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_208);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
 lean_ctor_set_tag(x_212, 1);
}
lean_ctor_set(x_212, 0, x_207);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
block_245:
{
if (x_214 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_205);
x_216 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_215);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_218 = x_216;
} else {
 lean_dec_ref(x_216);
 x_218 = lean_box(0);
}
x_219 = 0;
x_220 = lean_box(x_219);
if (lean_is_scalar(x_218)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_218;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_217);
return x_221;
}
else
{
uint8_t x_222; lean_object* x_223; 
x_222 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_223 = l_Lean_Meta_processPostponed(x_5, x_222, x_6, x_7, x_8, x_9, x_215);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; uint8_t x_225; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_unbox(x_224);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_205);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec(x_223);
x_227 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_226);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
x_230 = lean_box(x_222);
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_228);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_12);
x_232 = lean_ctor_get(x_223, 1);
lean_inc(x_232);
lean_dec(x_223);
x_233 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_232);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = l_Lean_PersistentArray_append___rarg(x_205, x_234);
x_237 = l_Lean_Meta_setPostponed(x_236, x_6, x_7, x_8, x_9, x_235);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
x_240 = 1;
x_241 = lean_box(x_240);
if (lean_is_scalar(x_239)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_239;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_238);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_205);
x_243 = lean_ctor_get(x_223, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_223, 1);
lean_inc(x_244);
lean_dec(x_223);
x_207 = x_243;
x_208 = x_244;
goto block_213;
}
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_367; lean_object* x_368; lean_object* x_399; 
x_343 = lean_ctor_get(x_17, 0);
x_344 = lean_ctor_get(x_17, 2);
x_345 = lean_ctor_get(x_17, 3);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_17);
x_346 = lean_ctor_get(x_18, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_18, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_18, 2);
lean_inc(x_348);
x_349 = lean_ctor_get(x_18, 3);
lean_inc(x_349);
x_350 = lean_ctor_get(x_18, 4);
lean_inc(x_350);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 x_351 = x_18;
} else {
 lean_dec_ref(x_18);
 x_351 = lean_box(0);
}
x_352 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1;
if (lean_is_scalar(x_351)) {
 x_353 = lean_alloc_ctor(0, 6, 0);
} else {
 x_353 = x_351;
}
lean_ctor_set(x_353, 0, x_346);
lean_ctor_set(x_353, 1, x_347);
lean_ctor_set(x_353, 2, x_348);
lean_ctor_set(x_353, 3, x_349);
lean_ctor_set(x_353, 4, x_350);
lean_ctor_set(x_353, 5, x_352);
x_354 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_354, 0, x_343);
lean_ctor_set(x_354, 1, x_353);
lean_ctor_set(x_354, 2, x_344);
lean_ctor_set(x_354, 3, x_345);
x_355 = lean_st_ref_set(x_7, x_354, x_19);
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
lean_dec(x_355);
x_357 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_356);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
lean_inc(x_3);
x_399 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_359);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
lean_dec(x_399);
x_402 = l_Lean_ConstantInfo_levelParams(x_400);
x_403 = lean_box(0);
x_404 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_402, x_403, x_6, x_7, x_8, x_9, x_401);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
lean_inc(x_9);
lean_inc(x_8);
x_407 = l_Lean_Core_instantiateValueLevelParams(x_400, x_405, x_8, x_9, x_406);
lean_dec(x_400);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_449; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_box(0);
lean_inc(x_6);
x_411 = l_Lean_Meta_lambdaMetaTelescope(x_408, x_410, x_6, x_7, x_8, x_9, x_409);
lean_dec(x_408);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_411, 1);
lean_inc(x_414);
lean_dec(x_411);
x_415 = lean_ctor_get(x_412, 0);
lean_inc(x_415);
lean_dec(x_412);
x_416 = lean_ctor_get(x_413, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_413, 1);
lean_inc(x_417);
lean_dec(x_413);
x_449 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_417);
if (lean_obj_tag(x_449) == 0)
{
lean_dec(x_449);
lean_dec(x_2);
lean_dec(x_1);
x_418 = x_410;
x_419 = x_414;
goto block_448;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; uint8_t x_458; uint8_t x_459; uint8_t x_460; uint8_t x_461; uint8_t x_462; uint8_t x_463; uint8_t x_464; uint8_t x_465; uint8_t x_466; uint8_t x_467; uint8_t x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_450 = lean_ctor_get(x_6, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 0);
lean_inc(x_451);
lean_dec(x_449);
x_452 = lean_ctor_get(x_6, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_6, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_6, 3);
lean_inc(x_454);
x_455 = lean_ctor_get(x_6, 4);
lean_inc(x_455);
x_456 = lean_ctor_get(x_6, 5);
lean_inc(x_456);
x_457 = lean_ctor_get_uint8(x_450, 0);
x_458 = lean_ctor_get_uint8(x_450, 1);
x_459 = lean_ctor_get_uint8(x_450, 2);
x_460 = lean_ctor_get_uint8(x_450, 3);
x_461 = lean_ctor_get_uint8(x_450, 4);
x_462 = lean_ctor_get_uint8(x_450, 5);
x_463 = lean_ctor_get_uint8(x_450, 6);
x_464 = lean_ctor_get_uint8(x_450, 7);
x_465 = lean_ctor_get_uint8(x_450, 9);
x_466 = lean_ctor_get_uint8(x_450, 10);
x_467 = lean_ctor_get_uint8(x_450, 11);
x_468 = lean_ctor_get_uint8(x_450, 12);
x_469 = lean_ctor_get_uint8(x_450, 13);
if (lean_is_exclusive(x_450)) {
 x_470 = x_450;
} else {
 lean_dec_ref(x_450);
 x_470 = lean_box(0);
}
x_471 = 0;
if (lean_is_scalar(x_470)) {
 x_472 = lean_alloc_ctor(0, 0, 14);
} else {
 x_472 = x_470;
}
lean_ctor_set_uint8(x_472, 0, x_457);
lean_ctor_set_uint8(x_472, 1, x_458);
lean_ctor_set_uint8(x_472, 2, x_459);
lean_ctor_set_uint8(x_472, 3, x_460);
lean_ctor_set_uint8(x_472, 4, x_461);
lean_ctor_set_uint8(x_472, 5, x_462);
lean_ctor_set_uint8(x_472, 6, x_463);
lean_ctor_set_uint8(x_472, 7, x_464);
lean_ctor_set_uint8(x_472, 8, x_471);
lean_ctor_set_uint8(x_472, 9, x_465);
lean_ctor_set_uint8(x_472, 10, x_466);
lean_ctor_set_uint8(x_472, 11, x_467);
lean_ctor_set_uint8(x_472, 12, x_468);
lean_ctor_set_uint8(x_472, 13, x_469);
x_473 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_452);
lean_ctor_set(x_473, 2, x_453);
lean_ctor_set(x_473, 3, x_454);
lean_ctor_set(x_473, 4, x_455);
lean_ctor_set(x_473, 5, x_456);
x_474 = lean_ctor_get(x_451, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_473);
x_476 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_475, x_1, x_473, x_7, x_8, x_9, x_414);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; uint8_t x_478; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_unbox(x_477);
lean_dec(x_477);
if (x_478 == 0)
{
lean_object* x_479; 
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_451);
lean_dec(x_2);
x_479 = lean_ctor_get(x_476, 1);
lean_inc(x_479);
lean_dec(x_476);
x_418 = x_410;
x_419 = x_479;
goto block_448;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_476, 1);
lean_inc(x_480);
lean_dec(x_476);
x_481 = lean_ctor_get(x_474, 1);
lean_inc(x_481);
lean_dec(x_474);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_482 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_481, x_2, x_473, x_7, x_8, x_9, x_480);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; uint8_t x_484; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_unbox(x_483);
lean_dec(x_483);
if (x_484 == 0)
{
lean_object* x_485; 
lean_dec(x_451);
x_485 = lean_ctor_get(x_482, 1);
lean_inc(x_485);
lean_dec(x_482);
x_418 = x_410;
x_419 = x_485;
goto block_448;
}
else
{
lean_object* x_486; lean_object* x_487; 
x_486 = lean_ctor_get(x_482, 1);
lean_inc(x_486);
lean_dec(x_482);
x_487 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_487, 0, x_451);
x_418 = x_487;
x_419 = x_486;
goto block_448;
}
}
else
{
lean_object* x_488; lean_object* x_489; 
lean_dec(x_451);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_358);
lean_dec(x_4);
lean_dec(x_3);
x_488 = lean_ctor_get(x_482, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_482, 1);
lean_inc(x_489);
lean_dec(x_482);
x_360 = x_488;
x_361 = x_489;
goto block_366;
}
}
}
else
{
lean_object* x_490; lean_object* x_491; 
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_451);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_358);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_490 = lean_ctor_get(x_476, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_476, 1);
lean_inc(x_491);
lean_dec(x_476);
x_360 = x_490;
x_361 = x_491;
goto block_366;
}
}
block_448:
{
if (lean_obj_tag(x_418) == 0)
{
uint8_t x_420; 
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_4);
lean_dec(x_3);
x_420 = 0;
x_367 = x_420;
x_368 = x_419;
goto block_398;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_421 = lean_ctor_get(x_418, 0);
lean_inc(x_421);
lean_dec(x_418);
lean_inc(x_4);
x_422 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_419);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_unbox(x_423);
lean_dec(x_423);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_4);
lean_dec(x_3);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
lean_dec(x_422);
x_426 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_427 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_421, x_410, x_416, x_415, x_426, x_6, x_7, x_8, x_9, x_425);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; uint8_t x_430; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = lean_unbox(x_428);
lean_dec(x_428);
x_367 = x_430;
x_368 = x_429;
goto block_398;
}
else
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_358);
x_431 = lean_ctor_get(x_427, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_427, 1);
lean_inc(x_432);
lean_dec(x_427);
x_360 = x_431;
x_361 = x_432;
goto block_366;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_433 = lean_ctor_get(x_422, 1);
lean_inc(x_433);
lean_dec(x_422);
x_434 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_434, 0, x_3);
x_435 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_436 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_434);
x_437 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
x_438 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
x_439 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_438, x_6, x_7, x_8, x_9, x_433);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_442 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_421, x_410, x_416, x_415, x_440, x_6, x_7, x_8, x_9, x_441);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; uint8_t x_445; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = lean_unbox(x_443);
lean_dec(x_443);
x_367 = x_445;
x_368 = x_444;
goto block_398;
}
else
{
lean_object* x_446; lean_object* x_447; 
lean_dec(x_358);
x_446 = lean_ctor_get(x_442, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_442, 1);
lean_inc(x_447);
lean_dec(x_442);
x_360 = x_446;
x_361 = x_447;
goto block_366;
}
}
}
}
}
else
{
lean_object* x_492; lean_object* x_493; 
lean_dec(x_358);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_492 = lean_ctor_get(x_407, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_407, 1);
lean_inc(x_493);
lean_dec(x_407);
x_360 = x_492;
x_361 = x_493;
goto block_366;
}
}
else
{
lean_object* x_494; lean_object* x_495; 
lean_dec(x_358);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_494 = lean_ctor_get(x_399, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_399, 1);
lean_inc(x_495);
lean_dec(x_399);
x_360 = x_494;
x_361 = x_495;
goto block_366;
}
block_366:
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_362 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_361);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_364 = x_362;
} else {
 lean_dec_ref(x_362);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_364;
 lean_ctor_set_tag(x_365, 1);
}
lean_ctor_set(x_365, 0, x_360);
lean_ctor_set(x_365, 1, x_363);
return x_365;
}
block_398:
{
if (x_367 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_358);
x_369 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_368);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_371 = x_369;
} else {
 lean_dec_ref(x_369);
 x_371 = lean_box(0);
}
x_372 = 0;
x_373 = lean_box(x_372);
if (lean_is_scalar(x_371)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_371;
}
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_370);
return x_374;
}
else
{
uint8_t x_375; lean_object* x_376; 
x_375 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_376 = l_Lean_Meta_processPostponed(x_5, x_375, x_6, x_7, x_8, x_9, x_368);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; uint8_t x_378; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_unbox(x_377);
lean_dec(x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_358);
x_379 = lean_ctor_get(x_376, 1);
lean_inc(x_379);
lean_dec(x_376);
x_380 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_379);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_382 = x_380;
} else {
 lean_dec_ref(x_380);
 x_382 = lean_box(0);
}
x_383 = lean_box(x_375);
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_381);
return x_384;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_12);
x_385 = lean_ctor_get(x_376, 1);
lean_inc(x_385);
lean_dec(x_376);
x_386 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_385);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = l_Lean_PersistentArray_append___rarg(x_358, x_387);
x_390 = l_Lean_Meta_setPostponed(x_389, x_6, x_7, x_8, x_9, x_388);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_392 = x_390;
} else {
 lean_dec_ref(x_390);
 x_392 = lean_box(0);
}
x_393 = 1;
x_394 = lean_box(x_393);
if (lean_is_scalar(x_392)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_392;
}
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_391);
return x_395;
}
}
else
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_358);
x_396 = lean_ctor_get(x_376, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_376, 1);
lean_inc(x_397);
lean_dec(x_376);
x_360 = x_396;
x_361 = x_397;
goto block_366;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" hint ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" at ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" =?= ", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_10 = l_Lean_exceptBoolEmoji___rarg(x_4);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
x_12 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_2);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_3);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints_tryCandidate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("isDefEq", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints_tryCandidate___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hint", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__2;
x_2 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__1;
x_3 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___boxed), 9, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___boxed), 10, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_10);
lean_closure_set(x_13, 4, x_12);
x_14 = l_Lean_withTraceNode___at_Lean_Meta_processPostponed___spec__1(x_10, x_9, x_13, x_11, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_15 = lean_array_uget(x_4, x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_Meta_tryUnificationHints_tryCandidate(x_1, x_2, x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = 1;
x_21 = lean_usize_add(x_6, x_20);
lean_inc(x_3);
{
size_t _tmp_5 = x_21;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_11 = x_19;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2;
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__1() {
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
static lean_object* _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_tryUnificationHints___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_instInhabitedUnificationHints;
x_14 = l_Lean_Meta_addUnificationHint___lambda__1___closed__3;
x_15 = l_Lean_ScopedEnvExtension_getState___rarg(x_13, x_14, x_12);
lean_dec(x_12);
x_16 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Lean_Meta_DiscrTree_getMatch___rarg(x_16, x_15, x_1, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_18);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Lean_Meta_tryUnificationHints___lambda__2___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1(x_1, x_2, x_23, x_18, x_21, x_22, x_23, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_Meta_tryUnificationHints___lambda__2___closed__2;
x_29 = lean_box(0);
x_30 = lean_apply_6(x_28, x_29, x_4, x_5, x_6, x_7, x_27);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_33);
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = l_Lean_Expr_isMVar(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Meta_tryUnificationHints___lambda__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Meta_tryUnificationHints___lambda__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_tryUnificationHints___lambda__4(x_1, x_2, x_13, x_3, x_4, x_5, x_6, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
lean_inc(x_1);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_2);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_2);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
x_24 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_8, x_23, x_3, x_4, x_5, x_6, x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_tryUnificationHints___lambda__4(x_1, x_2, x_25, x_3, x_4, x_5, x_6, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_tryUnificationHints___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_tryUnificationHints___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2723____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__12;
x_2 = lean_unsigned_to_nat(2723u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2723_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2723____closed__1;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_UnificationHint(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1 = _init_l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1);
l_Lean_Meta_instInhabitedUnificationHintEntry___closed__2 = _init_l_Lean_Meta_instInhabitedUnificationHintEntry___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHintEntry___closed__2);
l_Lean_Meta_instInhabitedUnificationHintEntry = _init_l_Lean_Meta_instInhabitedUnificationHintEntry();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHintEntry);
l_Lean_Meta_UnificationHints_discrTree___default___closed__1 = _init_l_Lean_Meta_UnificationHints_discrTree___default___closed__1();
lean_mark_persistent(l_Lean_Meta_UnificationHints_discrTree___default___closed__1);
l_Lean_Meta_UnificationHints_discrTree___default = _init_l_Lean_Meta_UnificationHints_discrTree___default();
lean_mark_persistent(l_Lean_Meta_UnificationHints_discrTree___default);
l_Lean_Meta_instInhabitedUnificationHints___closed__1 = _init_l_Lean_Meta_instInhabitedUnificationHints___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints___closed__1);
l_Lean_Meta_instInhabitedUnificationHints___closed__2 = _init_l_Lean_Meta_instInhabitedUnificationHints___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints___closed__2);
l_Lean_Meta_instInhabitedUnificationHints___closed__3 = _init_l_Lean_Meta_instInhabitedUnificationHints___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints___closed__3);
l_Lean_Meta_instInhabitedUnificationHints___closed__4 = _init_l_Lean_Meta_instInhabitedUnificationHints___closed__4();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints___closed__4);
l_Lean_Meta_instInhabitedUnificationHints___closed__5 = _init_l_Lean_Meta_instInhabitedUnificationHints___closed__5();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints___closed__5);
l_Lean_Meta_instInhabitedUnificationHints = _init_l_Lean_Meta_instInhabitedUnificationHints();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints);
l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__1 = _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__1);
l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2 = _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2);
l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__3 = _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__3();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__3);
l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__4 = _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__4();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__4);
l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5 = _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5);
l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6 = _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6);
l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__7 = _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__7();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__7);
l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8 = _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8);
l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__1 = _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__1();
lean_mark_persistent(l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__1);
l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__2 = _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__2();
lean_mark_persistent(l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__2);
l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__3 = _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__3();
lean_mark_persistent(l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__3);
l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__4 = _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__4();
lean_mark_persistent(l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__4);
l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__5 = _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__5();
lean_mark_persistent(l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__5);
l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__6 = _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__6();
lean_mark_persistent(l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__6);
l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__7 = _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__7();
lean_mark_persistent(l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__7);
l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__8 = _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__8();
lean_mark_persistent(l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__8);
l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__9 = _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__9();
lean_mark_persistent(l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__9);
l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__10 = _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__10();
lean_mark_persistent(l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__10);
l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11 = _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11();
lean_mark_persistent(l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11);
l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__1 = _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__1);
l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2 = _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2);
l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__3 = _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__3);
l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4 = _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4);
l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__5 = _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__5();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__5);
l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__6 = _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__6();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__6);
l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__7 = _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__7();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__7);
l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__1 = _init_l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__1);
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197____closed__7);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_197_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_unificationHintExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_unificationHintExtension);
lean_dec_ref(res);
}l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__4 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__4();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__4);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__5 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__5();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__5);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__2 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__2();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__2);
l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__1 = _init_l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__1();
lean_mark_persistent(l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__1);
l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__2 = _init_l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__2();
lean_mark_persistent(l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__2);
l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__3 = _init_l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__3();
lean_mark_persistent(l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__3);
l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4 = _init_l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4();
lean_mark_persistent(l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__2 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__2();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__2);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__3 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__3();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__3);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__4 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__4();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__4);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__5 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__5();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__5);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__6 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__6();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__6);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__7 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__7();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__7);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__8 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__8();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__8);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__9 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__9();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__9);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10);
l_Lean_Meta_addUnificationHint___lambda__1___closed__1 = _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_addUnificationHint___lambda__1___closed__1);
l_Lean_Meta_addUnificationHint___lambda__1___closed__2 = _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_addUnificationHint___lambda__1___closed__2);
l_Lean_Meta_addUnificationHint___lambda__1___closed__3 = _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_addUnificationHint___lambda__1___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__1___closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____lambda__2___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__13);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__14 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__14();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__14);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__15 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__15();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__15);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__16 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__16();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__16);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__17 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__17();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__17);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__18 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__18();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__18);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__19 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__19();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__19);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__20 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__20();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956____closed__20);
res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_956_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1 = _init_l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1);
l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2 = _init_l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2);
l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___closed__1 = _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___closed__1);
l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1 = _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1();
lean_mark_persistent(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1);
l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2 = _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2();
lean_mark_persistent(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2);
l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3 = _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3();
lean_mark_persistent(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3);
l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__1 = _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__1);
l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__2 = _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__2);
l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__3 = _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__3);
l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__4 = _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__4);
l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__5 = _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__5);
l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6 = _init_l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6);
l_Lean_Meta_tryUnificationHints_tryCandidate___closed__1 = _init_l_Lean_Meta_tryUnificationHints_tryCandidate___closed__1();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints_tryCandidate___closed__1);
l_Lean_Meta_tryUnificationHints_tryCandidate___closed__2 = _init_l_Lean_Meta_tryUnificationHints_tryCandidate___closed__2();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints_tryCandidate___closed__2);
l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3 = _init_l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2);
l_Lean_Meta_tryUnificationHints___lambda__2___closed__1 = _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints___lambda__2___closed__1);
l_Lean_Meta_tryUnificationHints___lambda__2___closed__2 = _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints___lambda__2___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2723____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2723____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2723____closed__1);
res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2723_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
