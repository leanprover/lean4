// Lean compiler output
// Module: Lean.Meta.UnificationHint
// Imports: Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.Meta.Basic Lean.Meta.DiscrTree Lean.Meta.SynthInstance
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__6;
lean_object* l_Lean_Meta_DiscrTree_Key_format(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__6;
lean_object* l_Lean_withTraceNode___at_Lean_Meta_processPostponed___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4;
static lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__2;
static lean_object* l_Lean_Meta_addUnificationHint___lambda__1___closed__2;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__2;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__3;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__6;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2;
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___closed__1;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__1;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___closed__1;
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_UnificationHints_add___spec__13(lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__3;
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_exceptBoolEmoji___rarg(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints(lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3;
lean_object* l_Std_Format_join(lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__1;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112_(lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__8;
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__5;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__13;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__5;
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__3;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__17;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__5;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__4;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__7;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__18;
static lean_object* l_Lean_Meta_addUnificationHint___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry___closed__2;
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__10;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___lambda__1(lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__1;
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__4;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1(lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__1;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__2;
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__2;
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__12;
static lean_object* l_Lean_Meta_instInhabitedUnificationHints___closed__2;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__9;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__1;
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1;
uint8_t l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__3;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1;
static lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___closed__5;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__7;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__8;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__10;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedUnificationHints___closed__1;
static lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___closed__4;
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unificationHintExtension;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__19;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Meta_instToFormatUnificationHints___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3(lean_object*, lean_object*);
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__2;
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2279_(lean_object*);
lean_object* l_instMonadControlTOfPure___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__7;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1;
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__9;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__3;
static lean_object* l_panic___at_Lean_Meta_UnificationHints_add___spec__13___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__14;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__7;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__3;
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__5;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__7___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___boxed(lean_object*);
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___closed__3;
static uint64_t l_Lean_Meta_tryUnificationHints_isDefEqPattern___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedUnificationHints;
lean_object* l_id___rarg___boxed(lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__2;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__4;
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__6;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1;
static lean_object* l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___closed__1;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_ScopedEnvExtension_addCore___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addUnificationHint___lambda__1___closed__3;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__4;
lean_object* l_List_reverse___rarg(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry;
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints___boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2;
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__8;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__11;
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__10;
lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2279____closed__1;
lean_object* l_Lean_throwError___at_Lean_Attribute_Builtin_ensureNoArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_UnificationHints_add___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertIdx_loop___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__5;
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__7;
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
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
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" => ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
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
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = l_Lean_Meta_DiscrTree_Key_format(x_8);
x_11 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_10);
x_12 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(x_9);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_23);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = l_Lean_Meta_DiscrTree_Key_format(x_26);
x_29 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(x_27);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = 0;
x_40 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_box(1);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_42);
{
lean_object* _tmp_0 = x_25;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_1);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
x_49 = l_Lean_Meta_DiscrTree_Key_format(x_46);
x_50 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(5, 2, 0);
} else {
 x_51 = x_48;
 lean_ctor_set_tag(x_51, 5);
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(x_47);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = 0;
x_61 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_box(1);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_2);
x_1 = x_45;
x_2 = x_64;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = 1;
x_8 = l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___closed__1;
x_9 = l_Lean_Name_toString(x_5, x_7, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_2 = x_11;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_1);
x_16 = 1;
x_17 = l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___closed__1;
x_18 = l_Lean_Name_toString(x_13, x_16, x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_2 = x_20;
x_3 = x_14;
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
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = 1;
x_7 = l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___closed__1;
x_8 = l_Lean_Name_toString(x_5, x_6, x_7);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = 1;
x_12 = l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___closed__1;
x_13 = l_Lean_Name_toString(x_10, x_11, x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6(x_2, x_14, x_4);
return x_15;
}
}
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
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
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
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
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__5;
lean_inc(x_1);
x_4 = l_Std_Format_joinSep___at_Lean_Meta_instToFormatUnificationHints___spec__5(x_1, x_3);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__9;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_8);
x_9 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__8;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_dec(x_1);
x_15 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__9;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__8;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = 0;
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("node", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
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
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Array_isEmpty___rarg(x_3);
x_6 = lean_array_to_list(x_4);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3(x_6, x_7);
x_9 = l_Std_Format_join(x_8);
if (x_5 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_array_to_list(x_3);
x_11 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(x_10);
x_12 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__6;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_12);
x_13 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
x_18 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = 0;
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_3);
x_27 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__7;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_27);
x_28 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
x_30 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = 0;
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = l_Array_isEmpty___rarg(x_37);
x_40 = lean_array_to_list(x_38);
x_41 = lean_box(0);
x_42 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3(x_40, x_41);
x_43 = l_Std_Format_join(x_42);
if (x_39 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_44 = lean_array_to_list(x_37);
x_45 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(x_44);
x_46 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__6;
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4;
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2;
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
x_53 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
x_58 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = 0;
x_60 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_37);
x_62 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__7;
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_43);
x_64 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
x_69 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = 0;
x_71 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_70);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_Meta_DiscrTree_Key_format(x_2);
x_7 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(x_3);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = 0;
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_unbox(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_box(1);
lean_inc(x_4);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_box(0);
lean_inc(x_4);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
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
static lean_object* _init_l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__2;
x_3 = l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__1;
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_instToFormatUnificationHints(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, 1, x_1);
lean_ctor_set_uint8(x_6, 2, x_1);
lean_ctor_set_uint8(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, 5, x_2);
lean_ctor_set_uint8(x_6, 6, x_2);
lean_ctor_set_uint8(x_6, 7, x_1);
lean_ctor_set_uint8(x_6, 8, x_2);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_4);
lean_ctor_set_uint8(x_6, 11, x_2);
lean_ctor_set_uint8(x_6, 12, x_1);
lean_ctor_set_uint8(x_6, 13, x_2);
lean_ctor_set_uint8(x_6, 14, x_5);
lean_ctor_set_uint8(x_6, 15, x_2);
lean_ctor_set_uint8(x_6, 16, x_2);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1;
x_2 = l_Lean_Meta_Config_toConfigWithKey(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_5, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
x_8 = lean_usize_land(x_2, x_7);
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
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_3, x_17);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_21 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_28 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_63 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
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
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
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
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_UnificationHints_add___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_array_push(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_name_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fset(x_1, x_3, x_2);
lean_dec(x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_nat_add(x_7, x_8);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = lean_array_fget(x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 0);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_8);
x_18 = l_Lean_Meta_DiscrTree_Key_lt(x_16, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_13, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_box(0);
x_22 = lean_array_fset(x_5, x_13, x_21);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 0);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_27, x_24);
lean_dec(x_27);
lean_ctor_set(x_14, 1, x_28);
lean_ctor_set(x_14, 0, x_4);
x_29 = lean_array_fset(x_22, x_13, x_14);
lean_dec(x_13);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_3, x_31);
x_33 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_32, x_30);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_fset(x_22, x_13, x_34);
lean_dec(x_13);
return x_35;
}
}
}
else
{
lean_dec(x_14);
x_8 = x_13;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_14);
x_37 = lean_nat_dec_eq(x_13, x_7);
if (x_37 == 0)
{
lean_dec(x_7);
x_7 = x_13;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
lean_dec(x_8);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_3, x_39);
x_41 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_7, x_39);
lean_dec(x_7);
x_44 = lean_array_get_size(x_5);
x_45 = lean_array_push(x_5, x_42);
x_46 = l_Array_insertIdx_loop___rarg(x_43, x_45, x_44);
lean_dec(x_43);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_fget(x_5, x_8);
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_11);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
if (x_15 == 0)
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_box(0);
x_17 = lean_array_fset(x_5, x_8, x_16);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_22, x_19);
lean_dec(x_22);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_4);
x_24 = lean_array_fset(x_17, x_8, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_27, x_25);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_fset(x_17, x_8, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_10);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_7, x_31);
x_33 = lean_array_fget(x_5, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = l_Lean_Meta_DiscrTree_Key_lt(x_34, x_11);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_34);
lean_dec(x_34);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = lean_nat_dec_lt(x_32, x_7);
lean_dec(x_7);
if (x_37 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_box(0);
x_39 = lean_array_fset(x_5, x_32, x_38);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_33, 1);
x_42 = lean_ctor_get(x_33, 0);
lean_dec(x_42);
x_43 = lean_nat_add(x_3, x_31);
x_44 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_43, x_41);
lean_dec(x_43);
lean_ctor_set(x_33, 1, x_44);
lean_ctor_set(x_33, 0, x_4);
x_45 = lean_array_fset(x_39, x_32, x_33);
lean_dec(x_32);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_nat_add(x_3, x_31);
x_48 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_47, x_46);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_4);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_fset(x_39, x_32, x_49);
lean_dec(x_32);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_33);
lean_dec(x_7);
x_51 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_32, lean_box(0), lean_box(0));
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
x_52 = lean_nat_add(x_3, x_31);
x_53 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_push(x_5, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_12);
lean_dec(x_10);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_3, x_56);
x_58 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_push(x_5, x_59);
x_61 = l_Array_insertIdx_loop___rarg(x_8, x_60, x_7);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_7);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_3, x_62);
x_64 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_4);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_push(x_5, x_65);
return x_66;
}
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_UnificationHints_add___spec__10(x_6, x_2, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_fget(x_1, x_3);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__2;
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(x_1, x_2, x_3, x_12, x_7, x_14);
lean_dec(x_14);
lean_ctor_set(x_4, 1, x_15);
return x_4;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_array_get_size(x_1);
x_19 = lean_nat_dec_lt(x_3, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_UnificationHints_add___spec__10(x_16, x_2, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_array_fget(x_1, x_3);
x_24 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__2;
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(x_1, x_2, x_3, x_23, x_17, x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_UnificationHints_add___spec__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_UnificationHints_add___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Meta_UnificationHints_add___spec__13___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.DiscrTree", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.insertCore", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid key sequence", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1;
x_2 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(481u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_9 = l_outOfBounds___rarg(x_8);
lean_inc(x_1);
x_10 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_11);
x_13 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(x_1, x_9, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_2, x_3, x_15, x_14);
x_17 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(x_1, x_9, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_2, x_6);
lean_inc(x_1);
x_19 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(x_1, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_20);
x_22 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(x_1, x_18, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_2, x_3, x_24, x_23);
x_26 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(x_1, x_18, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4;
x_28 = l_panic___at_Lean_Meta_UnificationHints_add___spec__13(x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unificationHintExtension", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_UnificationHints_add), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__4;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__6;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__7;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__8;
x_3 = l_Lean_registerSimpleScopedEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
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
x_1 = lean_mk_string_unchecked("invalid unification hint constraint, unexpected term", 52, 52);
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
x_1 = lean_mk_string_unchecked("", 0, 0);
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
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_9 = lean_alloc_ctor(7, 2, 0);
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
x_1 = lean_mk_string_unchecked("invalid unification hint constraint, unexpected dependency", 58, 58);
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
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_18 = lean_alloc_ctor(7, 2, 0);
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
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_27 = lean_alloc_ctor(7, 2, 0);
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
x_35 = lean_array_to_list(x_2);
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
x_38 = lean_array_to_list(x_2);
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
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1;
x_3 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid unification hint, failed to unify constraint left-hand-side", 67, 67);
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
x_1 = lean_mk_string_unchecked("\nwith right-hand-side", 21, 21);
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Lean_Meta_isExprDefEq(x_12, x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_indentExpr(x_12);
x_19 = l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__2;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_19);
x_20 = l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_indentExpr(x_13);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_25, x_2, x_3, x_4, x_5, x_17);
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
lean_dec(x_13);
lean_dec(x_12);
lean_free_object(x_1);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_1 = x_11;
x_6 = x_31;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_12);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_40);
lean_inc(x_39);
x_41 = l_Lean_Meta_isExprDefEq(x_39, x_40, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_38);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_indentExpr(x_39);
x_46 = l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__2;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_indentExpr(x_40);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_53, x_2, x_3, x_4, x_5, x_44);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; 
lean_dec(x_40);
lean_dec(x_39);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_dec(x_41);
x_1 = x_38;
x_6 = x_59;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_ctor_get(x_41, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_41, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_63 = x_41;
} else {
 lean_dec_ref(x_41);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid unification hint, failed to unify pattern left-hand-side", 64, 64);
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
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_indentExpr(x_12);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_25 = lean_alloc_ctor(7, 2, 0);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 6);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_st_ref_take(x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 4);
lean_dec(x_15);
x_16 = l_Lean_ScopedEnvExtension_addCore___rarg(x_14, x_1, x_2, x_3, x_9);
x_17 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1;
lean_ctor_set(x_11, 4, x_17);
lean_ctor_set(x_11, 0, x_16);
x_18 = lean_st_ref_set(x_7, x_11, x_12);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_5, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_dec(x_24);
x_25 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
lean_ctor_set(x_21, 1, x_25);
x_26 = lean_st_ref_set(x_5, x_21, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 2);
x_35 = lean_ctor_get(x_21, 3);
x_36 = lean_ctor_get(x_21, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_37 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_36);
x_39 = lean_st_ref_set(x_5, x_38, x_22);
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
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
x_46 = lean_ctor_get(x_11, 2);
x_47 = lean_ctor_get(x_11, 3);
x_48 = lean_ctor_get(x_11, 5);
x_49 = lean_ctor_get(x_11, 6);
x_50 = lean_ctor_get(x_11, 7);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_51 = l_Lean_ScopedEnvExtension_addCore___rarg(x_44, x_1, x_2, x_3, x_9);
x_52 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1;
x_53 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_48);
lean_ctor_set(x_53, 6, x_49);
lean_ctor_set(x_53, 7, x_50);
x_54 = lean_st_ref_set(x_7, x_53, x_12);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_5, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 4);
lean_inc(x_62);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 x_63 = x_57;
} else {
 lean_dec_ref(x_57);
 x_63 = lean_box(0);
}
x_64 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 5, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_61);
lean_ctor_set(x_65, 4, x_62);
x_66 = lean_st_ref_set(x_5, x_65, x_58);
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
}
static lean_object* _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid unification hint, it must be a definition", 49, 49);
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
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
x_12 = l_Lean_ConstantInfo_value_x3f(x_9, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_Lean_Meta_addUnificationHint___lambda__1___closed__2;
x_14 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
lean_inc(x_3);
x_17 = l_Lean_Meta_lambdaMetaTelescope(x_15, x_16, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_19);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_25, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint64(x_30, sizeof(void*)*1);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_3, 6);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_41 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_42 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 4, x_37);
lean_ctor_set(x_42, 5, x_38);
lean_ctor_set(x_42, 6, x_39);
lean_ctor_set_uint64(x_42, sizeof(void*)*7, x_32);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 8, x_33);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 9, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 10, x_41);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_43 = l_Lean_Meta_DiscrTree_mkPath(x_29, x_11, x_42, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(x_27, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 0, x_44);
x_48 = l_Lean_Meta_addUnificationHint___lambda__1___closed__3;
x_49 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1(x_48, x_19, x_2, x_3, x_4, x_5, x_6, x_47);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_44);
lean_free_object(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_46);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_27);
lean_free_object(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_43);
if (x_54 == 0)
{
return x_43;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_19, 1);
lean_inc(x_58);
lean_dec(x_19);
x_59 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_1);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_60, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint64_t x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get_uint64(x_65, sizeof(void*)*1);
x_68 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_69 = lean_ctor_get(x_3, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_3, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_3, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_3, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_3, 6);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_76 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_77 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_77, 2, x_70);
lean_ctor_set(x_77, 3, x_71);
lean_ctor_set(x_77, 4, x_72);
lean_ctor_set(x_77, 5, x_73);
lean_ctor_set(x_77, 6, x_74);
lean_ctor_set_uint64(x_77, sizeof(void*)*7, x_67);
lean_ctor_set_uint8(x_77, sizeof(void*)*7 + 8, x_68);
lean_ctor_set_uint8(x_77, sizeof(void*)*7 + 9, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*7 + 10, x_76);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_78 = l_Lean_Meta_DiscrTree_mkPath(x_64, x_11, x_77, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_81 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(x_62, x_3, x_4, x_5, x_6, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_1);
x_84 = l_Lean_Meta_addUnificationHint___lambda__1___closed__3;
x_85 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1(x_84, x_83, x_2, x_3, x_4, x_5, x_6, x_82);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_79);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_90 = lean_ctor_get(x_78, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_78, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_92 = x_78;
} else {
 lean_dec_ref(x_78);
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
}
else
{
uint8_t x_94; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_8);
if (x_94 == 0)
{
return x_8;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_8, 0);
x_96 = lean_ctor_get(x_8, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_8);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lambda__1___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = 0;
x_11 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = 2;
x_6 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, 1, x_1);
lean_ctor_set_uint8(x_6, 2, x_1);
lean_ctor_set_uint8(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, 5, x_2);
lean_ctor_set_uint8(x_6, 6, x_2);
lean_ctor_set_uint8(x_6, 7, x_1);
lean_ctor_set_uint8(x_6, 8, x_2);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_4);
lean_ctor_set_uint8(x_6, 11, x_2);
lean_ctor_set_uint8(x_6, 12, x_2);
lean_ctor_set_uint8(x_6, 13, x_2);
lean_ctor_set_uint8(x_6, 14, x_5);
lean_ctor_set_uint8(x_6, 15, x_2);
lean_ctor_set_uint8(x_6, 16, x_2);
return x_6;
}
}
static uint64_t _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__3;
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__1;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__2;
x_5 = 0;
x_6 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__6;
x_7 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_2);
lean_ctor_set(x_9, 5, x_8);
lean_ctor_set(x_9, 6, x_2);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 8, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 9, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 10, x_5);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__8;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__5;
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__9;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = l_Lean_Attribute_Builtin_ensureNoArgs(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__10;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__7;
lean_inc(x_11);
x_14 = l_Lean_Meta_addUnificationHint(x_1, x_3, x_13, x_11, x_4, x_5, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_11, x_15);
lean_dec(x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attribute cannot be erased", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__2;
x_6 = l_Lean_throwError___at_Lean_Attribute_Builtin_ensureNoArgs___spec__2(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__4;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__6;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UnificationHint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__10;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__12;
x_2 = lean_unsigned_to_nat(809u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unification_hint", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unification hint", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__13;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__15;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__16;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__17;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__18;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__19;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__20;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static uint64_t _init_l_Lean_Meta_tryUnificationHints_isDefEqPattern___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
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
uint64_t x_11; uint8_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_12 = 2;
lean_ctor_set_uint8(x_9, 9, x_12);
x_13 = 2;
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_shift_left(x_14, x_13);
x_16 = l_Lean_Meta_tryUnificationHints_isDefEqPattern___closed__1;
x_17 = lean_uint64_lor(x_15, x_16);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_17);
x_18 = lean_is_expr_def_eq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint64_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; lean_object* x_51; 
x_27 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_28 = lean_ctor_get_uint8(x_9, 0);
x_29 = lean_ctor_get_uint8(x_9, 1);
x_30 = lean_ctor_get_uint8(x_9, 2);
x_31 = lean_ctor_get_uint8(x_9, 3);
x_32 = lean_ctor_get_uint8(x_9, 4);
x_33 = lean_ctor_get_uint8(x_9, 5);
x_34 = lean_ctor_get_uint8(x_9, 6);
x_35 = lean_ctor_get_uint8(x_9, 7);
x_36 = lean_ctor_get_uint8(x_9, 8);
x_37 = lean_ctor_get_uint8(x_9, 10);
x_38 = lean_ctor_get_uint8(x_9, 11);
x_39 = lean_ctor_get_uint8(x_9, 12);
x_40 = lean_ctor_get_uint8(x_9, 13);
x_41 = lean_ctor_get_uint8(x_9, 14);
x_42 = lean_ctor_get_uint8(x_9, 15);
x_43 = lean_ctor_get_uint8(x_9, 16);
lean_dec(x_9);
x_44 = 2;
x_45 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_45, 0, x_28);
lean_ctor_set_uint8(x_45, 1, x_29);
lean_ctor_set_uint8(x_45, 2, x_30);
lean_ctor_set_uint8(x_45, 3, x_31);
lean_ctor_set_uint8(x_45, 4, x_32);
lean_ctor_set_uint8(x_45, 5, x_33);
lean_ctor_set_uint8(x_45, 6, x_34);
lean_ctor_set_uint8(x_45, 7, x_35);
lean_ctor_set_uint8(x_45, 8, x_36);
lean_ctor_set_uint8(x_45, 9, x_44);
lean_ctor_set_uint8(x_45, 10, x_37);
lean_ctor_set_uint8(x_45, 11, x_38);
lean_ctor_set_uint8(x_45, 12, x_39);
lean_ctor_set_uint8(x_45, 13, x_40);
lean_ctor_set_uint8(x_45, 14, x_41);
lean_ctor_set_uint8(x_45, 15, x_42);
lean_ctor_set_uint8(x_45, 16, x_43);
x_46 = 2;
x_47 = lean_uint64_shift_right(x_27, x_46);
x_48 = lean_uint64_shift_left(x_47, x_46);
x_49 = l_Lean_Meta_tryUnificationHints_isDefEqPattern___closed__1;
x_50 = lean_uint64_lor(x_48, x_49);
lean_ctor_set(x_3, 0, x_45);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_50);
x_51 = lean_is_expr_def_eq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_58 = x_51;
} else {
 lean_dec_ref(x_51);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
lean_object* x_60; uint64_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; lean_object* x_95; lean_object* x_96; 
x_60 = lean_ctor_get(x_3, 0);
x_61 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_63 = lean_ctor_get(x_3, 1);
x_64 = lean_ctor_get(x_3, 2);
x_65 = lean_ctor_get(x_3, 3);
x_66 = lean_ctor_get(x_3, 4);
x_67 = lean_ctor_get(x_3, 5);
x_68 = lean_ctor_get(x_3, 6);
x_69 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_70 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_60);
lean_dec(x_3);
x_71 = lean_ctor_get_uint8(x_60, 0);
x_72 = lean_ctor_get_uint8(x_60, 1);
x_73 = lean_ctor_get_uint8(x_60, 2);
x_74 = lean_ctor_get_uint8(x_60, 3);
x_75 = lean_ctor_get_uint8(x_60, 4);
x_76 = lean_ctor_get_uint8(x_60, 5);
x_77 = lean_ctor_get_uint8(x_60, 6);
x_78 = lean_ctor_get_uint8(x_60, 7);
x_79 = lean_ctor_get_uint8(x_60, 8);
x_80 = lean_ctor_get_uint8(x_60, 10);
x_81 = lean_ctor_get_uint8(x_60, 11);
x_82 = lean_ctor_get_uint8(x_60, 12);
x_83 = lean_ctor_get_uint8(x_60, 13);
x_84 = lean_ctor_get_uint8(x_60, 14);
x_85 = lean_ctor_get_uint8(x_60, 15);
x_86 = lean_ctor_get_uint8(x_60, 16);
if (lean_is_exclusive(x_60)) {
 x_87 = x_60;
} else {
 lean_dec_ref(x_60);
 x_87 = lean_box(0);
}
x_88 = 2;
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 0, 17);
} else {
 x_89 = x_87;
}
lean_ctor_set_uint8(x_89, 0, x_71);
lean_ctor_set_uint8(x_89, 1, x_72);
lean_ctor_set_uint8(x_89, 2, x_73);
lean_ctor_set_uint8(x_89, 3, x_74);
lean_ctor_set_uint8(x_89, 4, x_75);
lean_ctor_set_uint8(x_89, 5, x_76);
lean_ctor_set_uint8(x_89, 6, x_77);
lean_ctor_set_uint8(x_89, 7, x_78);
lean_ctor_set_uint8(x_89, 8, x_79);
lean_ctor_set_uint8(x_89, 9, x_88);
lean_ctor_set_uint8(x_89, 10, x_80);
lean_ctor_set_uint8(x_89, 11, x_81);
lean_ctor_set_uint8(x_89, 12, x_82);
lean_ctor_set_uint8(x_89, 13, x_83);
lean_ctor_set_uint8(x_89, 14, x_84);
lean_ctor_set_uint8(x_89, 15, x_85);
lean_ctor_set_uint8(x_89, 16, x_86);
x_90 = 2;
x_91 = lean_uint64_shift_right(x_61, x_90);
x_92 = lean_uint64_shift_left(x_91, x_90);
x_93 = l_Lean_Meta_tryUnificationHints_isDefEqPattern___closed__1;
x_94 = lean_uint64_lor(x_92, x_93);
x_95 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_63);
lean_ctor_set(x_95, 2, x_64);
lean_ctor_set(x_95, 3, x_65);
lean_ctor_set(x_95, 4, x_66);
lean_ctor_set(x_95, 5, x_67);
lean_ctor_set(x_95, 6, x_68);
lean_ctor_set_uint64(x_95, sizeof(void*)*7, x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 8, x_62);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 9, x_69);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 10, x_70);
x_96 = lean_is_expr_def_eq(x_1, x_2, x_95, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_103 = x_96;
} else {
 lean_dec_ref(x_96);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
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
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1() {
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
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = lean_is_expr_def_eq(x_16, x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2;
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
lean_inc(x_3);
{
lean_object* _tmp_4 = x_15;
lean_object* _tmp_5 = x_3;
lean_object* _tmp_6 = lean_box(0);
lean_object* _tmp_11 = x_27;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_26; 
x_16 = lean_array_uget(x_5, x_7);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_8, 1);
x_28 = lean_ctor_get(x_8, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_16);
lean_inc(x_3);
lean_ctor_set(x_8, 0, x_3);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_8);
x_17 = x_33;
x_18 = x_13;
goto block_25;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_35 = lean_ctor_get(x_27, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_27, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_array_fget(x_29, x_30);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_30, x_40);
lean_dec(x_30);
lean_ctor_set(x_27, 1, x_41);
x_42 = 3;
x_43 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_39, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_16);
lean_inc(x_3);
lean_ctor_set(x_8, 0, x_3);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_8);
x_17 = x_44;
x_18 = x_13;
goto block_25;
}
else
{
lean_object* x_45; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_16);
x_45 = lean_infer_type(x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_48 = l_Lean_Meta_trySynthInstance(x_46, x_1, x_9, x_10, x_11, x_12, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_53 = l_Lean_Meta_isExprDefEq(x_16, x_52, x_9, x_10, x_11, x_12, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
lean_ctor_set(x_8, 0, x_57);
lean_ctor_set_tag(x_49, 0);
lean_ctor_set(x_49, 0, x_8);
x_17 = x_49;
x_18 = x_56;
goto block_25;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
lean_inc(x_3);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_49, 0, x_8);
x_17 = x_49;
x_18 = x_58;
goto block_25;
}
}
else
{
uint8_t x_59; 
lean_free_object(x_49);
lean_dec(x_27);
lean_free_object(x_8);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_53);
if (x_59 == 0)
{
return x_53;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_53, 0);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_53);
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
x_63 = lean_ctor_get(x_49, 0);
lean_inc(x_63);
lean_dec(x_49);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_64 = l_Lean_Meta_isExprDefEq(x_16, x_63, x_9, x_10, x_11, x_12, x_50);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
lean_ctor_set(x_8, 0, x_68);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_8);
x_17 = x_69;
x_18 = x_67;
goto block_25;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
lean_inc(x_3);
lean_ctor_set(x_8, 0, x_3);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_8);
x_17 = x_71;
x_18 = x_70;
goto block_25;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_27);
lean_free_object(x_8);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_72 = lean_ctor_get(x_64, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_64, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_74 = x_64;
} else {
 lean_dec_ref(x_64);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_49);
lean_dec(x_16);
x_76 = lean_ctor_get(x_48, 1);
lean_inc(x_76);
lean_dec(x_48);
x_77 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
lean_ctor_set(x_8, 0, x_77);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_8);
x_17 = x_78;
x_18 = x_76;
goto block_25;
}
}
else
{
uint8_t x_79; 
lean_dec(x_27);
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_48);
if (x_79 == 0)
{
return x_48;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_48, 0);
x_81 = lean_ctor_get(x_48, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_48);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_27);
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_45);
if (x_83 == 0)
{
return x_45;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_45, 0);
x_85 = lean_ctor_get(x_45, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_45);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
lean_dec(x_27);
x_87 = lean_array_fget(x_29, x_30);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_30, x_89);
lean_dec(x_30);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_29);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_31);
x_92 = 3;
x_93 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_88, x_92);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_16);
lean_inc(x_3);
lean_ctor_set(x_8, 1, x_91);
lean_ctor_set(x_8, 0, x_3);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_8);
x_17 = x_94;
x_18 = x_13;
goto block_25;
}
else
{
lean_object* x_95; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_16);
x_95 = lean_infer_type(x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_98 = l_Lean_Meta_trySynthInstance(x_96, x_1, x_9, x_10, x_11, x_12, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 1)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_103 = l_Lean_Meta_isExprDefEq(x_16, x_101, x_9, x_10, x_11, x_12, x_100);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
lean_ctor_set(x_8, 1, x_91);
lean_ctor_set(x_8, 0, x_107);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(0, 1, 0);
} else {
 x_108 = x_102;
 lean_ctor_set_tag(x_108, 0);
}
lean_ctor_set(x_108, 0, x_8);
x_17 = x_108;
x_18 = x_106;
goto block_25;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_103, 1);
lean_inc(x_109);
lean_dec(x_103);
lean_inc(x_3);
lean_ctor_set(x_8, 1, x_91);
lean_ctor_set(x_8, 0, x_3);
if (lean_is_scalar(x_102)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_102;
}
lean_ctor_set(x_110, 0, x_8);
x_17 = x_110;
x_18 = x_109;
goto block_25;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_102);
lean_dec(x_91);
lean_free_object(x_8);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_111 = lean_ctor_get(x_103, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_103, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_113 = x_103;
} else {
 lean_dec_ref(x_103);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_99);
lean_dec(x_16);
x_115 = lean_ctor_get(x_98, 1);
lean_inc(x_115);
lean_dec(x_98);
x_116 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
lean_ctor_set(x_8, 1, x_91);
lean_ctor_set(x_8, 0, x_116);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_8);
x_17 = x_117;
x_18 = x_115;
goto block_25;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_91);
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_118 = lean_ctor_get(x_98, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_98, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_120 = x_98;
} else {
 lean_dec_ref(x_98);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_91);
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_122 = lean_ctor_get(x_95, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_95, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_124 = x_95;
} else {
 lean_dec_ref(x_95);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_126 = lean_ctor_get(x_8, 1);
lean_inc(x_126);
lean_dec(x_8);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 2);
lean_inc(x_129);
x_130 = lean_nat_dec_lt(x_128, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_16);
lean_inc(x_3);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_3);
lean_ctor_set(x_131, 1, x_126);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_17 = x_132;
x_18 = x_13;
goto block_25;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_140; 
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 x_133 = x_126;
} else {
 lean_dec_ref(x_126);
 x_133 = lean_box(0);
}
x_134 = lean_array_fget(x_127, x_128);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_add(x_128, x_136);
lean_dec(x_128);
if (lean_is_scalar(x_133)) {
 x_138 = lean_alloc_ctor(0, 3, 0);
} else {
 x_138 = x_133;
}
lean_ctor_set(x_138, 0, x_127);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_129);
x_139 = 3;
x_140 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_135, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_16);
lean_inc(x_3);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_3);
lean_ctor_set(x_141, 1, x_138);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_17 = x_142;
x_18 = x_13;
goto block_25;
}
else
{
lean_object* x_143; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_16);
x_143 = lean_infer_type(x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_146 = l_Lean_Meta_trySynthInstance(x_144, x_1, x_9, x_10, x_11, x_12, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 1)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_151 = l_Lean_Meta_isExprDefEq(x_16, x_149, x_9, x_10, x_11, x_12, x_148);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_138);
if (lean_is_scalar(x_150)) {
 x_157 = lean_alloc_ctor(0, 1, 0);
} else {
 x_157 = x_150;
 lean_ctor_set_tag(x_157, 0);
}
lean_ctor_set(x_157, 0, x_156);
x_17 = x_157;
x_18 = x_154;
goto block_25;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_151, 1);
lean_inc(x_158);
lean_dec(x_151);
lean_inc(x_3);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_3);
lean_ctor_set(x_159, 1, x_138);
if (lean_is_scalar(x_150)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_150;
}
lean_ctor_set(x_160, 0, x_159);
x_17 = x_160;
x_18 = x_158;
goto block_25;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_150);
lean_dec(x_138);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_161 = lean_ctor_get(x_151, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_151, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_163 = x_151;
} else {
 lean_dec_ref(x_151);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_147);
lean_dec(x_16);
x_165 = lean_ctor_get(x_146, 1);
lean_inc(x_165);
lean_dec(x_146);
x_166 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_138);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_17 = x_168;
x_18 = x_165;
goto block_25;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_138);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_169 = lean_ctor_get(x_146, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_146, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_171 = x_146;
} else {
 lean_dec_ref(x_146);
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
lean_dec(x_138);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_173 = lean_ctor_get(x_143, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_143, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_175 = x_143;
} else {
 lean_dec_ref(x_143);
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
}
}
block_25:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = 1;
x_23 = lean_usize_add(x_7, x_22);
x_7 = x_23;
x_8 = x_21;
x_13 = x_18;
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
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_toSubarray___rarg(x_1, x_12, x_11);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_size(x_3);
x_16 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3(x_2, x_3, x_2, x_4, x_3, x_15, x_16, x_14, x_6, x_7, x_8, x_9, x_10);
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
x_23 = lean_apply_6(x_21, x_22, x_6, x_7, x_8, x_9, x_20);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_box(0);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
lean_inc(x_11);
x_15 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2(x_11, x_12, x_14, x_11, x_11, x_14, lean_box(0), x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2(x_3, x_2, x_4, x_12, x_13, x_6, x_7, x_8, x_9, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" succeeded, applying constraints", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = l_Lean_Meta_saveState___rarg(x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_41; lean_object* x_42; lean_object* x_81; 
x_21 = lean_ctor_get(x_16, 4);
lean_dec(x_21);
x_22 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
lean_ctor_set(x_16, 4, x_22);
x_23 = lean_st_ref_set(x_7, x_15, x_17);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
lean_inc(x_3);
x_81 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_ConstantInfo_levelParams(x_82);
x_85 = lean_box(0);
x_86 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_84, x_85, x_6, x_7, x_8, x_9, x_83);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Core_instantiateValueLevelParams(x_82, x_87, x_8, x_9, x_88);
lean_dec(x_82);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_148; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_box(0);
lean_inc(x_6);
x_93 = l_Lean_Meta_lambdaMetaTelescope(x_90, x_92, x_6, x_7, x_8, x_9, x_91);
lean_dec(x_90);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_100 = x_95;
} else {
 lean_dec_ref(x_95);
 x_100 = lean_box(0);
}
x_148 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_99);
if (lean_obj_tag(x_148) == 0)
{
lean_dec(x_148);
lean_dec(x_2);
lean_dec(x_1);
x_101 = x_92;
x_102 = x_96;
goto block_147;
}
else
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_6, 0);
lean_inc(x_149);
x_150 = !lean_is_exclusive(x_148);
if (x_150 == 0)
{
lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_151 = lean_ctor_get(x_148, 0);
x_152 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_153 = lean_ctor_get(x_6, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_6, 2);
lean_inc(x_154);
x_155 = lean_ctor_get(x_6, 3);
lean_inc(x_155);
x_156 = lean_ctor_get(x_6, 4);
lean_inc(x_156);
x_157 = lean_ctor_get(x_6, 5);
lean_inc(x_157);
x_158 = lean_ctor_get(x_6, 6);
lean_inc(x_158);
x_159 = !lean_is_exclusive(x_149);
if (x_159 == 0)
{
uint8_t x_160; uint8_t x_161; uint8_t x_162; uint64_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_160 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_161 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_162 = 0;
lean_ctor_set_uint8(x_149, 5, x_162);
x_163 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_149);
x_164 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_164, 0, x_149);
lean_ctor_set(x_164, 1, x_153);
lean_ctor_set(x_164, 2, x_154);
lean_ctor_set(x_164, 3, x_155);
lean_ctor_set(x_164, 4, x_156);
lean_ctor_set(x_164, 5, x_157);
lean_ctor_set(x_164, 6, x_158);
lean_ctor_set_uint64(x_164, sizeof(void*)*7, x_163);
lean_ctor_set_uint8(x_164, sizeof(void*)*7 + 8, x_152);
lean_ctor_set_uint8(x_164, sizeof(void*)*7 + 9, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*7 + 10, x_161);
x_165 = lean_ctor_get(x_151, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_164);
x_167 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_166, x_1, x_164, x_7, x_8, x_9, x_96);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_unbox(x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; 
lean_dec(x_165);
lean_dec(x_164);
lean_free_object(x_148);
lean_dec(x_151);
lean_dec(x_2);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_101 = x_92;
x_102 = x_170;
goto block_147;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_167, 1);
lean_inc(x_171);
lean_dec(x_167);
x_172 = lean_ctor_get(x_165, 1);
lean_inc(x_172);
lean_dec(x_165);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_173 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_172, x_2, x_164, x_7, x_8, x_9, x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; 
lean_free_object(x_148);
lean_dec(x_151);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec(x_173);
x_101 = x_92;
x_102 = x_176;
goto block_147;
}
else
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_173, 1);
lean_inc(x_177);
lean_dec(x_173);
x_101 = x_148;
x_102 = x_177;
goto block_147;
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_free_object(x_148);
lean_dec(x_151);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
x_178 = lean_ctor_get(x_173, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_173, 1);
lean_inc(x_179);
lean_dec(x_173);
x_29 = x_178;
x_30 = x_179;
goto block_40;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_165);
lean_dec(x_164);
lean_free_object(x_148);
lean_dec(x_151);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = lean_ctor_get(x_167, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_167, 1);
lean_inc(x_181);
lean_dec(x_167);
x_29 = x_180;
x_30 = x_181;
goto block_40;
}
}
else
{
uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; lean_object* x_201; uint64_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_182 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_183 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_184 = lean_ctor_get_uint8(x_149, 0);
x_185 = lean_ctor_get_uint8(x_149, 1);
x_186 = lean_ctor_get_uint8(x_149, 2);
x_187 = lean_ctor_get_uint8(x_149, 3);
x_188 = lean_ctor_get_uint8(x_149, 4);
x_189 = lean_ctor_get_uint8(x_149, 6);
x_190 = lean_ctor_get_uint8(x_149, 7);
x_191 = lean_ctor_get_uint8(x_149, 8);
x_192 = lean_ctor_get_uint8(x_149, 9);
x_193 = lean_ctor_get_uint8(x_149, 10);
x_194 = lean_ctor_get_uint8(x_149, 11);
x_195 = lean_ctor_get_uint8(x_149, 12);
x_196 = lean_ctor_get_uint8(x_149, 13);
x_197 = lean_ctor_get_uint8(x_149, 14);
x_198 = lean_ctor_get_uint8(x_149, 15);
x_199 = lean_ctor_get_uint8(x_149, 16);
lean_dec(x_149);
x_200 = 0;
x_201 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_201, 0, x_184);
lean_ctor_set_uint8(x_201, 1, x_185);
lean_ctor_set_uint8(x_201, 2, x_186);
lean_ctor_set_uint8(x_201, 3, x_187);
lean_ctor_set_uint8(x_201, 4, x_188);
lean_ctor_set_uint8(x_201, 5, x_200);
lean_ctor_set_uint8(x_201, 6, x_189);
lean_ctor_set_uint8(x_201, 7, x_190);
lean_ctor_set_uint8(x_201, 8, x_191);
lean_ctor_set_uint8(x_201, 9, x_192);
lean_ctor_set_uint8(x_201, 10, x_193);
lean_ctor_set_uint8(x_201, 11, x_194);
lean_ctor_set_uint8(x_201, 12, x_195);
lean_ctor_set_uint8(x_201, 13, x_196);
lean_ctor_set_uint8(x_201, 14, x_197);
lean_ctor_set_uint8(x_201, 15, x_198);
lean_ctor_set_uint8(x_201, 16, x_199);
x_202 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_201);
x_203 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_153);
lean_ctor_set(x_203, 2, x_154);
lean_ctor_set(x_203, 3, x_155);
lean_ctor_set(x_203, 4, x_156);
lean_ctor_set(x_203, 5, x_157);
lean_ctor_set(x_203, 6, x_158);
lean_ctor_set_uint64(x_203, sizeof(void*)*7, x_202);
lean_ctor_set_uint8(x_203, sizeof(void*)*7 + 8, x_152);
lean_ctor_set_uint8(x_203, sizeof(void*)*7 + 9, x_182);
lean_ctor_set_uint8(x_203, sizeof(void*)*7 + 10, x_183);
x_204 = lean_ctor_get(x_151, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_203);
x_206 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_205, x_1, x_203, x_7, x_8, x_9, x_96);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_unbox(x_207);
lean_dec(x_207);
if (x_208 == 0)
{
lean_object* x_209; 
lean_dec(x_204);
lean_dec(x_203);
lean_free_object(x_148);
lean_dec(x_151);
lean_dec(x_2);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
x_101 = x_92;
x_102 = x_209;
goto block_147;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
lean_dec(x_206);
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
lean_dec(x_204);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_212 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_211, x_2, x_203, x_7, x_8, x_9, x_210);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_unbox(x_213);
lean_dec(x_213);
if (x_214 == 0)
{
lean_object* x_215; 
lean_free_object(x_148);
lean_dec(x_151);
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_dec(x_212);
x_101 = x_92;
x_102 = x_215;
goto block_147;
}
else
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_dec(x_212);
x_101 = x_148;
x_102 = x_216;
goto block_147;
}
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_free_object(x_148);
lean_dec(x_151);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
x_217 = lean_ctor_get(x_212, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_212, 1);
lean_inc(x_218);
lean_dec(x_212);
x_29 = x_217;
x_30 = x_218;
goto block_40;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_204);
lean_dec(x_203);
lean_free_object(x_148);
lean_dec(x_151);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_219 = lean_ctor_get(x_206, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_206, 1);
lean_inc(x_220);
lean_dec(x_206);
x_29 = x_219;
x_30 = x_220;
goto block_40;
}
}
}
else
{
lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; uint64_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_221 = lean_ctor_get(x_148, 0);
lean_inc(x_221);
lean_dec(x_148);
x_222 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_223 = lean_ctor_get(x_6, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_6, 2);
lean_inc(x_224);
x_225 = lean_ctor_get(x_6, 3);
lean_inc(x_225);
x_226 = lean_ctor_get(x_6, 4);
lean_inc(x_226);
x_227 = lean_ctor_get(x_6, 5);
lean_inc(x_227);
x_228 = lean_ctor_get(x_6, 6);
lean_inc(x_228);
x_229 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_230 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_231 = lean_ctor_get_uint8(x_149, 0);
x_232 = lean_ctor_get_uint8(x_149, 1);
x_233 = lean_ctor_get_uint8(x_149, 2);
x_234 = lean_ctor_get_uint8(x_149, 3);
x_235 = lean_ctor_get_uint8(x_149, 4);
x_236 = lean_ctor_get_uint8(x_149, 6);
x_237 = lean_ctor_get_uint8(x_149, 7);
x_238 = lean_ctor_get_uint8(x_149, 8);
x_239 = lean_ctor_get_uint8(x_149, 9);
x_240 = lean_ctor_get_uint8(x_149, 10);
x_241 = lean_ctor_get_uint8(x_149, 11);
x_242 = lean_ctor_get_uint8(x_149, 12);
x_243 = lean_ctor_get_uint8(x_149, 13);
x_244 = lean_ctor_get_uint8(x_149, 14);
x_245 = lean_ctor_get_uint8(x_149, 15);
x_246 = lean_ctor_get_uint8(x_149, 16);
if (lean_is_exclusive(x_149)) {
 x_247 = x_149;
} else {
 lean_dec_ref(x_149);
 x_247 = lean_box(0);
}
x_248 = 0;
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(0, 0, 17);
} else {
 x_249 = x_247;
}
lean_ctor_set_uint8(x_249, 0, x_231);
lean_ctor_set_uint8(x_249, 1, x_232);
lean_ctor_set_uint8(x_249, 2, x_233);
lean_ctor_set_uint8(x_249, 3, x_234);
lean_ctor_set_uint8(x_249, 4, x_235);
lean_ctor_set_uint8(x_249, 5, x_248);
lean_ctor_set_uint8(x_249, 6, x_236);
lean_ctor_set_uint8(x_249, 7, x_237);
lean_ctor_set_uint8(x_249, 8, x_238);
lean_ctor_set_uint8(x_249, 9, x_239);
lean_ctor_set_uint8(x_249, 10, x_240);
lean_ctor_set_uint8(x_249, 11, x_241);
lean_ctor_set_uint8(x_249, 12, x_242);
lean_ctor_set_uint8(x_249, 13, x_243);
lean_ctor_set_uint8(x_249, 14, x_244);
lean_ctor_set_uint8(x_249, 15, x_245);
lean_ctor_set_uint8(x_249, 16, x_246);
x_250 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_249);
x_251 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_223);
lean_ctor_set(x_251, 2, x_224);
lean_ctor_set(x_251, 3, x_225);
lean_ctor_set(x_251, 4, x_226);
lean_ctor_set(x_251, 5, x_227);
lean_ctor_set(x_251, 6, x_228);
lean_ctor_set_uint64(x_251, sizeof(void*)*7, x_250);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 8, x_222);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 9, x_229);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 10, x_230);
x_252 = lean_ctor_get(x_221, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_251);
x_254 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_253, x_1, x_251, x_7, x_8, x_9, x_96);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_unbox(x_255);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_221);
lean_dec(x_2);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
x_101 = x_92;
x_102 = x_257;
goto block_147;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_254, 1);
lean_inc(x_258);
lean_dec(x_254);
x_259 = lean_ctor_get(x_252, 1);
lean_inc(x_259);
lean_dec(x_252);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_260 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_259, x_2, x_251, x_7, x_8, x_9, x_258);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_unbox(x_261);
lean_dec(x_261);
if (x_262 == 0)
{
lean_object* x_263; 
lean_dec(x_221);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_dec(x_260);
x_101 = x_92;
x_102 = x_263;
goto block_147;
}
else
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_260, 1);
lean_inc(x_264);
lean_dec(x_260);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_221);
x_101 = x_265;
x_102 = x_264;
goto block_147;
}
}
else
{
lean_object* x_266; lean_object* x_267; 
lean_dec(x_221);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
x_266 = lean_ctor_get(x_260, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_260, 1);
lean_inc(x_267);
lean_dec(x_260);
x_29 = x_266;
x_30 = x_267;
goto block_40;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_221);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_268 = lean_ctor_get(x_254, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_254, 1);
lean_inc(x_269);
lean_dec(x_254);
x_29 = x_268;
x_30 = x_269;
goto block_40;
}
}
}
block_147:
{
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_103; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_3);
x_103 = 0;
x_41 = x_103;
x_42 = x_102;
goto block_80;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_101, 0);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_4);
x_105 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_102);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_100);
lean_dec(x_4);
lean_dec(x_3);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_110 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_104, x_92, x_98, x_97, x_109, x_6, x_7, x_8, x_9, x_108);
lean_dec(x_97);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_unbox(x_111);
lean_dec(x_111);
x_41 = x_113;
x_42 = x_112;
goto block_80;
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_26);
x_114 = lean_ctor_get(x_110, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_29 = x_114;
x_30 = x_115;
goto block_40;
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_105);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_117 = lean_ctor_get(x_105, 1);
x_118 = lean_ctor_get(x_105, 0);
lean_dec(x_118);
x_119 = l_Lean_MessageData_ofName(x_3);
x_120 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
lean_ctor_set_tag(x_105, 7);
lean_ctor_set(x_105, 1, x_119);
lean_ctor_set(x_105, 0, x_120);
x_121 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
if (lean_is_scalar(x_100)) {
 x_122 = lean_alloc_ctor(7, 2, 0);
} else {
 x_122 = x_100;
 lean_ctor_set_tag(x_122, 7);
}
lean_ctor_set(x_122, 0, x_105);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_122, x_6, x_7, x_8, x_9, x_117);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_126 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_104, x_92, x_98, x_97, x_124, x_6, x_7, x_8, x_9, x_125);
lean_dec(x_124);
lean_dec(x_97);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_unbox(x_127);
lean_dec(x_127);
x_41 = x_129;
x_42 = x_128;
goto block_80;
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_26);
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_dec(x_126);
x_29 = x_130;
x_30 = x_131;
goto block_40;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_132 = lean_ctor_get(x_105, 1);
lean_inc(x_132);
lean_dec(x_105);
x_133 = l_Lean_MessageData_ofName(x_3);
x_134 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
if (lean_is_scalar(x_100)) {
 x_137 = lean_alloc_ctor(7, 2, 0);
} else {
 x_137 = x_100;
 lean_ctor_set_tag(x_137, 7);
}
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_137, x_6, x_7, x_8, x_9, x_132);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_141 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_104, x_92, x_98, x_97, x_139, x_6, x_7, x_8, x_9, x_140);
lean_dec(x_139);
lean_dec(x_97);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_unbox(x_142);
lean_dec(x_142);
x_41 = x_144;
x_42 = x_143;
goto block_80;
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_26);
x_145 = lean_ctor_get(x_141, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_dec(x_141);
x_29 = x_145;
x_30 = x_146;
goto block_40;
}
}
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = lean_ctor_get(x_89, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_89, 1);
lean_inc(x_271);
lean_dec(x_89);
x_29 = x_270;
x_30 = x_271;
goto block_40;
}
}
else
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_272 = lean_ctor_get(x_81, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_81, 1);
lean_inc(x_273);
lean_dec(x_81);
x_29 = x_272;
x_30 = x_273;
goto block_40;
}
block_40:
{
uint8_t x_31; 
x_31 = l_Lean_Exception_isInterrupt(x_29);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_Exception_isRuntime(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_28);
x_33 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_29);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_28)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_28;
 lean_ctor_set_tag(x_38, 1);
}
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_30);
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_28)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_28;
 lean_ctor_set_tag(x_39, 1);
}
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_30);
return x_39;
}
}
block_80:
{
if (x_41 == 0)
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_28);
lean_dec(x_26);
x_43 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = 0;
x_47 = lean_box(x_46);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = 0;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; lean_object* x_53; 
x_52 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_53 = l_Lean_Meta_processPostponed(x_5, x_52, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_28);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_26);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_56);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = lean_box(x_52);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_box(x_52);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_12);
x_64 = lean_ctor_get(x_53, 1);
lean_inc(x_64);
lean_dec(x_53);
x_65 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_PersistentArray_append___rarg(x_26, x_66);
lean_dec(x_66);
x_69 = l_Lean_Meta_setPostponed(x_68, x_6, x_7, x_8, x_9, x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = 1;
x_73 = lean_box(x_72);
lean_ctor_set(x_69, 0, x_73);
return x_69;
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = 1;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_26);
x_78 = lean_ctor_get(x_53, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_53, 1);
lean_inc(x_79);
lean_dec(x_53);
x_29 = x_78;
x_30 = x_79;
goto block_40;
}
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_298; lean_object* x_299; lean_object* x_330; 
x_274 = lean_ctor_get(x_16, 0);
x_275 = lean_ctor_get(x_16, 1);
x_276 = lean_ctor_get(x_16, 2);
x_277 = lean_ctor_get(x_16, 3);
x_278 = lean_ctor_get(x_16, 5);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_16);
x_279 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
x_280 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_280, 0, x_274);
lean_ctor_set(x_280, 1, x_275);
lean_ctor_set(x_280, 2, x_276);
lean_ctor_set(x_280, 3, x_277);
lean_ctor_set(x_280, 4, x_279);
lean_ctor_set(x_280, 5, x_278);
lean_ctor_set(x_15, 1, x_280);
x_281 = lean_st_ref_set(x_7, x_15, x_17);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec(x_281);
x_283 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_282);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_286 = x_283;
} else {
 lean_dec_ref(x_283);
 x_286 = lean_box(0);
}
lean_inc(x_3);
x_330 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_285);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = l_Lean_ConstantInfo_levelParams(x_331);
x_334 = lean_box(0);
x_335 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_333, x_334, x_6, x_7, x_8, x_9, x_332);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = l_Lean_Core_instantiateValueLevelParams(x_331, x_336, x_8, x_9, x_337);
lean_dec(x_331);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_382; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_box(0);
lean_inc(x_6);
x_342 = l_Lean_Meta_lambdaMetaTelescope(x_339, x_341, x_6, x_7, x_8, x_9, x_340);
lean_dec(x_339);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_342, 1);
lean_inc(x_345);
lean_dec(x_342);
x_346 = lean_ctor_get(x_343, 0);
lean_inc(x_346);
lean_dec(x_343);
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_344, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_349 = x_344;
} else {
 lean_dec_ref(x_344);
 x_349 = lean_box(0);
}
x_382 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_348);
if (lean_obj_tag(x_382) == 0)
{
lean_dec(x_382);
lean_dec(x_2);
lean_dec(x_1);
x_350 = x_341;
x_351 = x_345;
goto block_381;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; uint8_t x_394; uint8_t x_395; uint8_t x_396; uint8_t x_397; uint8_t x_398; uint8_t x_399; uint8_t x_400; uint8_t x_401; uint8_t x_402; uint8_t x_403; uint8_t x_404; uint8_t x_405; uint8_t x_406; uint8_t x_407; uint8_t x_408; uint8_t x_409; uint8_t x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; uint64_t x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_383 = lean_ctor_get(x_6, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 0);
lean_inc(x_384);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 x_385 = x_382;
} else {
 lean_dec_ref(x_382);
 x_385 = lean_box(0);
}
x_386 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_387 = lean_ctor_get(x_6, 1);
lean_inc(x_387);
x_388 = lean_ctor_get(x_6, 2);
lean_inc(x_388);
x_389 = lean_ctor_get(x_6, 3);
lean_inc(x_389);
x_390 = lean_ctor_get(x_6, 4);
lean_inc(x_390);
x_391 = lean_ctor_get(x_6, 5);
lean_inc(x_391);
x_392 = lean_ctor_get(x_6, 6);
lean_inc(x_392);
x_393 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_394 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_395 = lean_ctor_get_uint8(x_383, 0);
x_396 = lean_ctor_get_uint8(x_383, 1);
x_397 = lean_ctor_get_uint8(x_383, 2);
x_398 = lean_ctor_get_uint8(x_383, 3);
x_399 = lean_ctor_get_uint8(x_383, 4);
x_400 = lean_ctor_get_uint8(x_383, 6);
x_401 = lean_ctor_get_uint8(x_383, 7);
x_402 = lean_ctor_get_uint8(x_383, 8);
x_403 = lean_ctor_get_uint8(x_383, 9);
x_404 = lean_ctor_get_uint8(x_383, 10);
x_405 = lean_ctor_get_uint8(x_383, 11);
x_406 = lean_ctor_get_uint8(x_383, 12);
x_407 = lean_ctor_get_uint8(x_383, 13);
x_408 = lean_ctor_get_uint8(x_383, 14);
x_409 = lean_ctor_get_uint8(x_383, 15);
x_410 = lean_ctor_get_uint8(x_383, 16);
if (lean_is_exclusive(x_383)) {
 x_411 = x_383;
} else {
 lean_dec_ref(x_383);
 x_411 = lean_box(0);
}
x_412 = 0;
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(0, 0, 17);
} else {
 x_413 = x_411;
}
lean_ctor_set_uint8(x_413, 0, x_395);
lean_ctor_set_uint8(x_413, 1, x_396);
lean_ctor_set_uint8(x_413, 2, x_397);
lean_ctor_set_uint8(x_413, 3, x_398);
lean_ctor_set_uint8(x_413, 4, x_399);
lean_ctor_set_uint8(x_413, 5, x_412);
lean_ctor_set_uint8(x_413, 6, x_400);
lean_ctor_set_uint8(x_413, 7, x_401);
lean_ctor_set_uint8(x_413, 8, x_402);
lean_ctor_set_uint8(x_413, 9, x_403);
lean_ctor_set_uint8(x_413, 10, x_404);
lean_ctor_set_uint8(x_413, 11, x_405);
lean_ctor_set_uint8(x_413, 12, x_406);
lean_ctor_set_uint8(x_413, 13, x_407);
lean_ctor_set_uint8(x_413, 14, x_408);
lean_ctor_set_uint8(x_413, 15, x_409);
lean_ctor_set_uint8(x_413, 16, x_410);
x_414 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_413);
x_415 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_387);
lean_ctor_set(x_415, 2, x_388);
lean_ctor_set(x_415, 3, x_389);
lean_ctor_set(x_415, 4, x_390);
lean_ctor_set(x_415, 5, x_391);
lean_ctor_set(x_415, 6, x_392);
lean_ctor_set_uint64(x_415, sizeof(void*)*7, x_414);
lean_ctor_set_uint8(x_415, sizeof(void*)*7 + 8, x_386);
lean_ctor_set_uint8(x_415, sizeof(void*)*7 + 9, x_393);
lean_ctor_set_uint8(x_415, sizeof(void*)*7 + 10, x_394);
x_416 = lean_ctor_get(x_384, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_415);
x_418 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_417, x_1, x_415, x_7, x_8, x_9, x_345);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; uint8_t x_420; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_unbox(x_419);
lean_dec(x_419);
if (x_420 == 0)
{
lean_object* x_421; 
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_2);
x_421 = lean_ctor_get(x_418, 1);
lean_inc(x_421);
lean_dec(x_418);
x_350 = x_341;
x_351 = x_421;
goto block_381;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_418, 1);
lean_inc(x_422);
lean_dec(x_418);
x_423 = lean_ctor_get(x_416, 1);
lean_inc(x_423);
lean_dec(x_416);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_424 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_423, x_2, x_415, x_7, x_8, x_9, x_422);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; uint8_t x_426; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_unbox(x_425);
lean_dec(x_425);
if (x_426 == 0)
{
lean_object* x_427; 
lean_dec(x_385);
lean_dec(x_384);
x_427 = lean_ctor_get(x_424, 1);
lean_inc(x_427);
lean_dec(x_424);
x_350 = x_341;
x_351 = x_427;
goto block_381;
}
else
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_424, 1);
lean_inc(x_428);
lean_dec(x_424);
if (lean_is_scalar(x_385)) {
 x_429 = lean_alloc_ctor(1, 1, 0);
} else {
 x_429 = x_385;
}
lean_ctor_set(x_429, 0, x_384);
x_350 = x_429;
x_351 = x_428;
goto block_381;
}
}
else
{
lean_object* x_430; lean_object* x_431; 
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_284);
lean_dec(x_4);
lean_dec(x_3);
x_430 = lean_ctor_get(x_424, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_424, 1);
lean_inc(x_431);
lean_dec(x_424);
x_287 = x_430;
x_288 = x_431;
goto block_297;
}
}
}
else
{
lean_object* x_432; lean_object* x_433; 
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_284);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_432 = lean_ctor_get(x_418, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_418, 1);
lean_inc(x_433);
lean_dec(x_418);
x_287 = x_432;
x_288 = x_433;
goto block_297;
}
}
block_381:
{
if (lean_obj_tag(x_350) == 0)
{
uint8_t x_352; 
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_4);
lean_dec(x_3);
x_352 = 0;
x_298 = x_352;
x_299 = x_351;
goto block_329;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_353 = lean_ctor_get(x_350, 0);
lean_inc(x_353);
lean_dec(x_350);
lean_inc(x_4);
x_354 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_351);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_unbox(x_355);
lean_dec(x_355);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_349);
lean_dec(x_4);
lean_dec(x_3);
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
lean_dec(x_354);
x_358 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_359 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_353, x_341, x_347, x_346, x_358, x_6, x_7, x_8, x_9, x_357);
lean_dec(x_346);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = lean_unbox(x_360);
lean_dec(x_360);
x_298 = x_362;
x_299 = x_361;
goto block_329;
}
else
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_284);
x_363 = lean_ctor_get(x_359, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_359, 1);
lean_inc(x_364);
lean_dec(x_359);
x_287 = x_363;
x_288 = x_364;
goto block_297;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_365 = lean_ctor_get(x_354, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_366 = x_354;
} else {
 lean_dec_ref(x_354);
 x_366 = lean_box(0);
}
x_367 = l_Lean_MessageData_ofName(x_3);
x_368 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
if (lean_is_scalar(x_366)) {
 x_369 = lean_alloc_ctor(7, 2, 0);
} else {
 x_369 = x_366;
 lean_ctor_set_tag(x_369, 7);
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_367);
x_370 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
if (lean_is_scalar(x_349)) {
 x_371 = lean_alloc_ctor(7, 2, 0);
} else {
 x_371 = x_349;
 lean_ctor_set_tag(x_371, 7);
}
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
x_372 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_371, x_6, x_7, x_8, x_9, x_365);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_375 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_353, x_341, x_347, x_346, x_373, x_6, x_7, x_8, x_9, x_374);
lean_dec(x_373);
lean_dec(x_346);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_378 = lean_unbox(x_376);
lean_dec(x_376);
x_298 = x_378;
x_299 = x_377;
goto block_329;
}
else
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_284);
x_379 = lean_ctor_get(x_375, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_375, 1);
lean_inc(x_380);
lean_dec(x_375);
x_287 = x_379;
x_288 = x_380;
goto block_297;
}
}
}
}
}
else
{
lean_object* x_434; lean_object* x_435; 
lean_dec(x_284);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_434 = lean_ctor_get(x_338, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_338, 1);
lean_inc(x_435);
lean_dec(x_338);
x_287 = x_434;
x_288 = x_435;
goto block_297;
}
}
else
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_284);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_436 = lean_ctor_get(x_330, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_330, 1);
lean_inc(x_437);
lean_dec(x_330);
x_287 = x_436;
x_288 = x_437;
goto block_297;
}
block_297:
{
uint8_t x_289; 
x_289 = l_Lean_Exception_isInterrupt(x_287);
if (x_289 == 0)
{
uint8_t x_290; 
x_290 = l_Lean_Exception_isRuntime(x_287);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_286);
x_291 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_288);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_293 = x_291;
} else {
 lean_dec_ref(x_291);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
 lean_ctor_set_tag(x_294, 1);
}
lean_ctor_set(x_294, 0, x_287);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
else
{
lean_object* x_295; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_286)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_286;
 lean_ctor_set_tag(x_295, 1);
}
lean_ctor_set(x_295, 0, x_287);
lean_ctor_set(x_295, 1, x_288);
return x_295;
}
}
else
{
lean_object* x_296; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_286)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_286;
 lean_ctor_set_tag(x_296, 1);
}
lean_ctor_set(x_296, 0, x_287);
lean_ctor_set(x_296, 1, x_288);
return x_296;
}
}
block_329:
{
if (x_298 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_286);
lean_dec(x_284);
x_300 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_299);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_302 = x_300;
} else {
 lean_dec_ref(x_300);
 x_302 = lean_box(0);
}
x_303 = 0;
x_304 = lean_box(x_303);
if (lean_is_scalar(x_302)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_302;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_301);
return x_305;
}
else
{
uint8_t x_306; lean_object* x_307; 
x_306 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_307 = l_Lean_Meta_processPostponed(x_5, x_306, x_6, x_7, x_8, x_9, x_299);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; uint8_t x_309; 
lean_dec(x_286);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_unbox(x_308);
lean_dec(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_284);
x_310 = lean_ctor_get(x_307, 1);
lean_inc(x_310);
lean_dec(x_307);
x_311 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_310);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_313 = x_311;
} else {
 lean_dec_ref(x_311);
 x_313 = lean_box(0);
}
x_314 = lean_box(x_306);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_312);
return x_315;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_12);
x_316 = lean_ctor_get(x_307, 1);
lean_inc(x_316);
lean_dec(x_307);
x_317 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_316);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = l_Lean_PersistentArray_append___rarg(x_284, x_318);
lean_dec(x_318);
x_321 = l_Lean_Meta_setPostponed(x_320, x_6, x_7, x_8, x_9, x_319);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_323 = x_321;
} else {
 lean_dec_ref(x_321);
 x_323 = lean_box(0);
}
x_324 = 1;
x_325 = lean_box(x_324);
if (lean_is_scalar(x_323)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_323;
}
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_322);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; 
lean_dec(x_284);
x_327 = lean_ctor_get(x_307, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_307, 1);
lean_inc(x_328);
lean_dec(x_307);
x_287 = x_327;
x_288 = x_328;
goto block_297;
}
}
}
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_468; lean_object* x_469; lean_object* x_500; 
x_438 = lean_ctor_get(x_15, 0);
x_439 = lean_ctor_get(x_15, 2);
x_440 = lean_ctor_get(x_15, 3);
x_441 = lean_ctor_get(x_15, 4);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_15);
x_442 = lean_ctor_get(x_16, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_16, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_16, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_16, 3);
lean_inc(x_445);
x_446 = lean_ctor_get(x_16, 5);
lean_inc(x_446);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 x_447 = x_16;
} else {
 lean_dec_ref(x_16);
 x_447 = lean_box(0);
}
x_448 = l_Lean_Meta_instInhabitedUnificationHints___closed__2;
if (lean_is_scalar(x_447)) {
 x_449 = lean_alloc_ctor(0, 6, 0);
} else {
 x_449 = x_447;
}
lean_ctor_set(x_449, 0, x_442);
lean_ctor_set(x_449, 1, x_443);
lean_ctor_set(x_449, 2, x_444);
lean_ctor_set(x_449, 3, x_445);
lean_ctor_set(x_449, 4, x_448);
lean_ctor_set(x_449, 5, x_446);
x_450 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_450, 0, x_438);
lean_ctor_set(x_450, 1, x_449);
lean_ctor_set(x_450, 2, x_439);
lean_ctor_set(x_450, 3, x_440);
lean_ctor_set(x_450, 4, x_441);
x_451 = lean_st_ref_set(x_7, x_450, x_17);
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec(x_451);
x_453 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_452);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_456 = x_453;
} else {
 lean_dec_ref(x_453);
 x_456 = lean_box(0);
}
lean_inc(x_3);
x_500 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_455);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = l_Lean_ConstantInfo_levelParams(x_501);
x_504 = lean_box(0);
x_505 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_503, x_504, x_6, x_7, x_8, x_9, x_502);
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = l_Lean_Core_instantiateValueLevelParams(x_501, x_506, x_8, x_9, x_507);
lean_dec(x_501);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_552; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_box(0);
lean_inc(x_6);
x_512 = l_Lean_Meta_lambdaMetaTelescope(x_509, x_511, x_6, x_7, x_8, x_9, x_510);
lean_dec(x_509);
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_513, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_512, 1);
lean_inc(x_515);
lean_dec(x_512);
x_516 = lean_ctor_get(x_513, 0);
lean_inc(x_516);
lean_dec(x_513);
x_517 = lean_ctor_get(x_514, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_514, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 x_519 = x_514;
} else {
 lean_dec_ref(x_514);
 x_519 = lean_box(0);
}
x_552 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_518);
if (lean_obj_tag(x_552) == 0)
{
lean_dec(x_552);
lean_dec(x_2);
lean_dec(x_1);
x_520 = x_511;
x_521 = x_515;
goto block_551;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; uint8_t x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; uint8_t x_563; uint8_t x_564; uint8_t x_565; uint8_t x_566; uint8_t x_567; uint8_t x_568; uint8_t x_569; uint8_t x_570; uint8_t x_571; uint8_t x_572; uint8_t x_573; uint8_t x_574; uint8_t x_575; uint8_t x_576; uint8_t x_577; uint8_t x_578; uint8_t x_579; uint8_t x_580; lean_object* x_581; uint8_t x_582; lean_object* x_583; uint64_t x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_553 = lean_ctor_get(x_6, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 0);
lean_inc(x_554);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 x_555 = x_552;
} else {
 lean_dec_ref(x_552);
 x_555 = lean_box(0);
}
x_556 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_557 = lean_ctor_get(x_6, 1);
lean_inc(x_557);
x_558 = lean_ctor_get(x_6, 2);
lean_inc(x_558);
x_559 = lean_ctor_get(x_6, 3);
lean_inc(x_559);
x_560 = lean_ctor_get(x_6, 4);
lean_inc(x_560);
x_561 = lean_ctor_get(x_6, 5);
lean_inc(x_561);
x_562 = lean_ctor_get(x_6, 6);
lean_inc(x_562);
x_563 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_564 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_565 = lean_ctor_get_uint8(x_553, 0);
x_566 = lean_ctor_get_uint8(x_553, 1);
x_567 = lean_ctor_get_uint8(x_553, 2);
x_568 = lean_ctor_get_uint8(x_553, 3);
x_569 = lean_ctor_get_uint8(x_553, 4);
x_570 = lean_ctor_get_uint8(x_553, 6);
x_571 = lean_ctor_get_uint8(x_553, 7);
x_572 = lean_ctor_get_uint8(x_553, 8);
x_573 = lean_ctor_get_uint8(x_553, 9);
x_574 = lean_ctor_get_uint8(x_553, 10);
x_575 = lean_ctor_get_uint8(x_553, 11);
x_576 = lean_ctor_get_uint8(x_553, 12);
x_577 = lean_ctor_get_uint8(x_553, 13);
x_578 = lean_ctor_get_uint8(x_553, 14);
x_579 = lean_ctor_get_uint8(x_553, 15);
x_580 = lean_ctor_get_uint8(x_553, 16);
if (lean_is_exclusive(x_553)) {
 x_581 = x_553;
} else {
 lean_dec_ref(x_553);
 x_581 = lean_box(0);
}
x_582 = 0;
if (lean_is_scalar(x_581)) {
 x_583 = lean_alloc_ctor(0, 0, 17);
} else {
 x_583 = x_581;
}
lean_ctor_set_uint8(x_583, 0, x_565);
lean_ctor_set_uint8(x_583, 1, x_566);
lean_ctor_set_uint8(x_583, 2, x_567);
lean_ctor_set_uint8(x_583, 3, x_568);
lean_ctor_set_uint8(x_583, 4, x_569);
lean_ctor_set_uint8(x_583, 5, x_582);
lean_ctor_set_uint8(x_583, 6, x_570);
lean_ctor_set_uint8(x_583, 7, x_571);
lean_ctor_set_uint8(x_583, 8, x_572);
lean_ctor_set_uint8(x_583, 9, x_573);
lean_ctor_set_uint8(x_583, 10, x_574);
lean_ctor_set_uint8(x_583, 11, x_575);
lean_ctor_set_uint8(x_583, 12, x_576);
lean_ctor_set_uint8(x_583, 13, x_577);
lean_ctor_set_uint8(x_583, 14, x_578);
lean_ctor_set_uint8(x_583, 15, x_579);
lean_ctor_set_uint8(x_583, 16, x_580);
x_584 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_583);
x_585 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_557);
lean_ctor_set(x_585, 2, x_558);
lean_ctor_set(x_585, 3, x_559);
lean_ctor_set(x_585, 4, x_560);
lean_ctor_set(x_585, 5, x_561);
lean_ctor_set(x_585, 6, x_562);
lean_ctor_set_uint64(x_585, sizeof(void*)*7, x_584);
lean_ctor_set_uint8(x_585, sizeof(void*)*7 + 8, x_556);
lean_ctor_set_uint8(x_585, sizeof(void*)*7 + 9, x_563);
lean_ctor_set_uint8(x_585, sizeof(void*)*7 + 10, x_564);
x_586 = lean_ctor_get(x_554, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_585);
x_588 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_587, x_1, x_585, x_7, x_8, x_9, x_515);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; uint8_t x_590; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_unbox(x_589);
lean_dec(x_589);
if (x_590 == 0)
{
lean_object* x_591; 
lean_dec(x_586);
lean_dec(x_585);
lean_dec(x_555);
lean_dec(x_554);
lean_dec(x_2);
x_591 = lean_ctor_get(x_588, 1);
lean_inc(x_591);
lean_dec(x_588);
x_520 = x_511;
x_521 = x_591;
goto block_551;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_592 = lean_ctor_get(x_588, 1);
lean_inc(x_592);
lean_dec(x_588);
x_593 = lean_ctor_get(x_586, 1);
lean_inc(x_593);
lean_dec(x_586);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_594 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_593, x_2, x_585, x_7, x_8, x_9, x_592);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; uint8_t x_596; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
x_596 = lean_unbox(x_595);
lean_dec(x_595);
if (x_596 == 0)
{
lean_object* x_597; 
lean_dec(x_555);
lean_dec(x_554);
x_597 = lean_ctor_get(x_594, 1);
lean_inc(x_597);
lean_dec(x_594);
x_520 = x_511;
x_521 = x_597;
goto block_551;
}
else
{
lean_object* x_598; lean_object* x_599; 
x_598 = lean_ctor_get(x_594, 1);
lean_inc(x_598);
lean_dec(x_594);
if (lean_is_scalar(x_555)) {
 x_599 = lean_alloc_ctor(1, 1, 0);
} else {
 x_599 = x_555;
}
lean_ctor_set(x_599, 0, x_554);
x_520 = x_599;
x_521 = x_598;
goto block_551;
}
}
else
{
lean_object* x_600; lean_object* x_601; 
lean_dec(x_555);
lean_dec(x_554);
lean_dec(x_519);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_454);
lean_dec(x_4);
lean_dec(x_3);
x_600 = lean_ctor_get(x_594, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_594, 1);
lean_inc(x_601);
lean_dec(x_594);
x_457 = x_600;
x_458 = x_601;
goto block_467;
}
}
}
else
{
lean_object* x_602; lean_object* x_603; 
lean_dec(x_586);
lean_dec(x_585);
lean_dec(x_555);
lean_dec(x_554);
lean_dec(x_519);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_454);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_602 = lean_ctor_get(x_588, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_588, 1);
lean_inc(x_603);
lean_dec(x_588);
x_457 = x_602;
x_458 = x_603;
goto block_467;
}
}
block_551:
{
if (lean_obj_tag(x_520) == 0)
{
uint8_t x_522; 
lean_dec(x_519);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_4);
lean_dec(x_3);
x_522 = 0;
x_468 = x_522;
x_469 = x_521;
goto block_499;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; 
x_523 = lean_ctor_get(x_520, 0);
lean_inc(x_523);
lean_dec(x_520);
lean_inc(x_4);
x_524 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_521);
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_unbox(x_525);
lean_dec(x_525);
if (x_526 == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_519);
lean_dec(x_4);
lean_dec(x_3);
x_527 = lean_ctor_get(x_524, 1);
lean_inc(x_527);
lean_dec(x_524);
x_528 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_529 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_523, x_511, x_517, x_516, x_528, x_6, x_7, x_8, x_9, x_527);
lean_dec(x_516);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; uint8_t x_532; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_532 = lean_unbox(x_530);
lean_dec(x_530);
x_468 = x_532;
x_469 = x_531;
goto block_499;
}
else
{
lean_object* x_533; lean_object* x_534; 
lean_dec(x_454);
x_533 = lean_ctor_get(x_529, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_529, 1);
lean_inc(x_534);
lean_dec(x_529);
x_457 = x_533;
x_458 = x_534;
goto block_467;
}
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_535 = lean_ctor_get(x_524, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_536 = x_524;
} else {
 lean_dec_ref(x_524);
 x_536 = lean_box(0);
}
x_537 = l_Lean_MessageData_ofName(x_3);
x_538 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
if (lean_is_scalar(x_536)) {
 x_539 = lean_alloc_ctor(7, 2, 0);
} else {
 x_539 = x_536;
 lean_ctor_set_tag(x_539, 7);
}
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_537);
x_540 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
if (lean_is_scalar(x_519)) {
 x_541 = lean_alloc_ctor(7, 2, 0);
} else {
 x_541 = x_519;
 lean_ctor_set_tag(x_541, 7);
}
lean_ctor_set(x_541, 0, x_539);
lean_ctor_set(x_541, 1, x_540);
x_542 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_541, x_6, x_7, x_8, x_9, x_535);
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
lean_dec(x_542);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_545 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_523, x_511, x_517, x_516, x_543, x_6, x_7, x_8, x_9, x_544);
lean_dec(x_543);
lean_dec(x_516);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; uint8_t x_548; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
lean_dec(x_545);
x_548 = lean_unbox(x_546);
lean_dec(x_546);
x_468 = x_548;
x_469 = x_547;
goto block_499;
}
else
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_454);
x_549 = lean_ctor_get(x_545, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_545, 1);
lean_inc(x_550);
lean_dec(x_545);
x_457 = x_549;
x_458 = x_550;
goto block_467;
}
}
}
}
}
else
{
lean_object* x_604; lean_object* x_605; 
lean_dec(x_454);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_604 = lean_ctor_get(x_508, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_508, 1);
lean_inc(x_605);
lean_dec(x_508);
x_457 = x_604;
x_458 = x_605;
goto block_467;
}
}
else
{
lean_object* x_606; lean_object* x_607; 
lean_dec(x_454);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_606 = lean_ctor_get(x_500, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_500, 1);
lean_inc(x_607);
lean_dec(x_500);
x_457 = x_606;
x_458 = x_607;
goto block_467;
}
block_467:
{
uint8_t x_459; 
x_459 = l_Lean_Exception_isInterrupt(x_457);
if (x_459 == 0)
{
uint8_t x_460; 
x_460 = l_Lean_Exception_isRuntime(x_457);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_456);
x_461 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_458);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_462 = lean_ctor_get(x_461, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_463 = x_461;
} else {
 lean_dec_ref(x_461);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 2, 0);
} else {
 x_464 = x_463;
 lean_ctor_set_tag(x_464, 1);
}
lean_ctor_set(x_464, 0, x_457);
lean_ctor_set(x_464, 1, x_462);
return x_464;
}
else
{
lean_object* x_465; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_456)) {
 x_465 = lean_alloc_ctor(1, 2, 0);
} else {
 x_465 = x_456;
 lean_ctor_set_tag(x_465, 1);
}
lean_ctor_set(x_465, 0, x_457);
lean_ctor_set(x_465, 1, x_458);
return x_465;
}
}
else
{
lean_object* x_466; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_456)) {
 x_466 = lean_alloc_ctor(1, 2, 0);
} else {
 x_466 = x_456;
 lean_ctor_set_tag(x_466, 1);
}
lean_ctor_set(x_466, 0, x_457);
lean_ctor_set(x_466, 1, x_458);
return x_466;
}
}
block_499:
{
if (x_468 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; lean_object* x_474; lean_object* x_475; 
lean_dec(x_456);
lean_dec(x_454);
x_470 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_469);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_471 = lean_ctor_get(x_470, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_472 = x_470;
} else {
 lean_dec_ref(x_470);
 x_472 = lean_box(0);
}
x_473 = 0;
x_474 = lean_box(x_473);
if (lean_is_scalar(x_472)) {
 x_475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_475 = x_472;
}
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_471);
return x_475;
}
else
{
uint8_t x_476; lean_object* x_477; 
x_476 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_477 = l_Lean_Meta_processPostponed(x_5, x_476, x_6, x_7, x_8, x_9, x_469);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; uint8_t x_479; 
lean_dec(x_456);
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
x_479 = lean_unbox(x_478);
lean_dec(x_478);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_454);
x_480 = lean_ctor_get(x_477, 1);
lean_inc(x_480);
lean_dec(x_477);
x_481 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_480);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_483 = x_481;
} else {
 lean_dec_ref(x_481);
 x_483 = lean_box(0);
}
x_484 = lean_box(x_476);
if (lean_is_scalar(x_483)) {
 x_485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_485 = x_483;
}
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_482);
return x_485;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_12);
x_486 = lean_ctor_get(x_477, 1);
lean_inc(x_486);
lean_dec(x_477);
x_487 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_486);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_487, 1);
lean_inc(x_489);
lean_dec(x_487);
x_490 = l_Lean_PersistentArray_append___rarg(x_454, x_488);
lean_dec(x_488);
x_491 = l_Lean_Meta_setPostponed(x_490, x_6, x_7, x_8, x_9, x_489);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_492 = lean_ctor_get(x_491, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_493 = x_491;
} else {
 lean_dec_ref(x_491);
 x_493 = lean_box(0);
}
x_494 = 1;
x_495 = lean_box(x_494);
if (lean_is_scalar(x_493)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_493;
}
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_492);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; 
lean_dec(x_454);
x_497 = lean_ctor_get(x_477, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_477, 1);
lean_inc(x_498);
lean_dec(x_477);
x_457 = x_497;
x_458 = x_498;
goto block_467;
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
x_1 = lean_mk_string_unchecked(" hint ", 6, 6);
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
x_1 = lean_mk_string_unchecked(" at ", 4, 4);
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
x_1 = lean_mk_string_unchecked(" =\?= ", 5, 5);
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
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_MessageData_ofName(x_1);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__4;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_MessageData_ofExpr(x_2);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_ofExpr(x_3);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
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
x_1 = lean_mk_string_unchecked("isDefEq", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints_tryCandidate___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hint", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__2;
x_2 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__1;
x_3 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
x_14 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__5;
x_15 = l_Lean_withTraceNode___at_Lean_Meta_processPostponed___spec__1(x_10, x_9, x_13, x_11, x_14, x_4, x_5, x_6, x_7, x_8);
return x_15;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
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
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1() {
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_9, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
x_18 = lean_array_uget(x_7, x_9);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_Meta_tryUnificationHints_tryCandidate(x_1, x_2, x_18, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = 1;
x_24 = lean_usize_add(x_9, x_23);
lean_inc(x_6);
{
size_t _tmp_8 = x_24;
lean_object* _tmp_9 = x_6;
lean_object* _tmp_14 = x_22;
x_9 = _tmp_8;
x_10 = _tmp_9;
x_15 = _tmp_14;
}
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2;
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_tryUnificationHints___lambda__2___closed__1;
x_2 = l_ReaderT_instApplicativeOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_tryUnificationHints___lambda__2___closed__2;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_instMonadControlTOfPure___rarg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__4() {
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
static lean_object* _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__5() {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
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
x_16 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_16, sizeof(void*)*1);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 4);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 5);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 6);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_28 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set(x_28, 4, x_23);
lean_ctor_set(x_28, 5, x_24);
lean_ctor_set(x_28, 6, x_25);
lean_ctor_set_uint64(x_28, sizeof(void*)*7, x_18);
lean_ctor_set_uint8(x_28, sizeof(void*)*7 + 8, x_19);
lean_ctor_set_uint8(x_28, sizeof(void*)*7 + 9, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*7 + 10, x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_29 = l_Lean_Meta_DiscrTree_getMatch___rarg(x_15, x_1, x_28, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(0);
x_33 = lean_array_size(x_30);
x_34 = 0;
x_35 = l_Lean_Meta_tryUnificationHints___lambda__2___closed__3;
x_36 = l_Lean_Meta_tryUnificationHints___lambda__2___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1(x_1, x_2, x_35, x_30, x_32, x_36, x_30, x_33, x_34, x_36, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_Meta_tryUnificationHints___lambda__2___closed__5;
x_42 = lean_box(0);
x_43 = lean_apply_6(x_41, x_42, x_4, x_5, x_6, x_7, x_40);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_46);
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
return x_29;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_29, 0);
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_29);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
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
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Meta_getConfig(x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, 5);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = l_Lean_Meta_tryUnificationHints___lambda__3(x_1, x_2, x_21, x_4, x_5, x_6, x_7, x_20);
return x_22;
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
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
lean_inc(x_1);
x_18 = l_Lean_MessageData_ofExpr(x_1);
x_19 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_18);
lean_ctor_set(x_9, 0, x_19);
x_20 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_2);
x_22 = l_Lean_MessageData_ofExpr(x_2);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
x_25 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_8, x_24, x_3, x_4, x_5, x_6, x_16);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_tryUnificationHints___lambda__4(x_1, x_2, x_26, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_dec(x_9);
lean_inc(x_1);
x_30 = l_Lean_MessageData_ofExpr(x_1);
x_31 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_2);
x_35 = l_Lean_MessageData_ofExpr(x_2);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
x_38 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_8, x_37, x_3, x_4, x_5, x_6, x_29);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_tryUnificationHints___lambda__4(x_1, x_2, x_39, x_3, x_4, x_5, x_6, x_40);
lean_dec(x_39);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
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
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_tryUnificationHints___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_tryUnificationHints___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2279____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__12;
x_2 = lean_unsigned_to_nat(2279u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2279_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2279____closed__1;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_UnificationHint(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
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
l_Lean_Meta_instInhabitedUnificationHints___closed__1 = _init_l_Lean_Meta_instInhabitedUnificationHints___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints___closed__1);
l_Lean_Meta_instInhabitedUnificationHints___closed__2 = _init_l_Lean_Meta_instInhabitedUnificationHints___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints___closed__2);
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
l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___closed__1 = _init_l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6___closed__1);
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
l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__2 = _init_l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__2);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__2 = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__2();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__2);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config);
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__2 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__2();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__2);
l_panic___at_Lean_Meta_UnificationHints_add___spec__13___closed__1 = _init_l_panic___at_Lean_Meta_UnificationHints_add___spec__13___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_UnificationHints_add___spec__13___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112____closed__8);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112_(lean_io_mk_world());
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
l_Lean_Meta_addUnificationHint___lambda__1___closed__1 = _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_addUnificationHint___lambda__1___closed__1);
l_Lean_Meta_addUnificationHint___lambda__1___closed__2 = _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_addUnificationHint___lambda__1___closed__2);
l_Lean_Meta_addUnificationHint___lambda__1___closed__3 = _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_addUnificationHint___lambda__1___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__2();
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__1___closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____lambda__2___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__13);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__14 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__14();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__14);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__15 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__15();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__15);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__16 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__16();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__16);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__17 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__17();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__17);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__18 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__18();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__18);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__19 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__19();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__19);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__20 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__20();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809____closed__20);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_tryUnificationHints_isDefEqPattern___closed__1 = _init_l_Lean_Meta_tryUnificationHints_isDefEqPattern___closed__1();
l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1);
l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2);
l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___closed__1 = _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___closed__1);
l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1 = _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1();
lean_mark_persistent(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1);
l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2 = _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2();
lean_mark_persistent(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2);
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
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2);
l_Lean_Meta_tryUnificationHints___lambda__2___closed__1 = _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints___lambda__2___closed__1);
l_Lean_Meta_tryUnificationHints___lambda__2___closed__2 = _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints___lambda__2___closed__2);
l_Lean_Meta_tryUnificationHints___lambda__2___closed__3 = _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints___lambda__2___closed__3);
l_Lean_Meta_tryUnificationHints___lambda__2___closed__4 = _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints___lambda__2___closed__4);
l_Lean_Meta_tryUnificationHints___lambda__2___closed__5 = _init_l_Lean_Meta_tryUnificationHints___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_tryUnificationHints___lambda__2___closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2279____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2279____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2279____closed__1);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2279_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
