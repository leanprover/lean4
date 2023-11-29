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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_format(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__17;
uint8_t l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__7;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__9;
lean_object* l_Lean_withTraceNode___at_Lean_Meta_processPostponed___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__5;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4;
static lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addUnificationHint___lambda__1___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__4;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__2;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__5;
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___closed__2;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__2;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints___lambda__2___closed__1;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__1;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___closed__1;
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_UnificationHints_add___spec__13(lean_object*);
lean_object* l_Lean_instBEqLocalInstance___boxed(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__3;
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_exceptBoolEmoji___rarg(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__10;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__1;
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
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__1;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__11;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__7;
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__8;
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__5;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__6;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__18;
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedUnificationHints___closed__3;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
static lean_object* l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1;
lean_object* l_instHashableArray___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__15;
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__3;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__5;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__5;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__8;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__4;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__7;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__20;
static lean_object* l_Lean_Meta_addUnificationHint___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_UnificationHints_add___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__6;
static lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry___closed__2;
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__10;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__1;
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1(lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__1;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__3;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__2;
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__1;
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__19;
static lean_object* l_Lean_Meta_instInhabitedUnificationHints___closed__2;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__16;
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_UnificationHints_add___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__9;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__15;
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1;
lean_object* l_Lean_instHashableLocalInstance___boxed(lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__3;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__9;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__7;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__8;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_UnificationHints_discrTree___default___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedUnificationHints___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205_(lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_unificationHintExtension;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Meta_instToFormatUnificationHints___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3(lean_object*, lean_object*);
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__2;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__12;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__3;
static lean_object* l_panic___at_Lean_Meta_UnificationHints_add___spec__13___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_UnificationHints_config___closed__1;
lean_object* l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__13;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__4;
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__13;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__5;
static lean_object* l_List_forM___at___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___spec__1___closed__1;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__11;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedUnificationHints;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967_(lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__2;
lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__14;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt_x21___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addUnificationHint___lambda__1___closed__3;
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2763_(lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2;
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__7;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__14;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17;
static lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__6;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4;
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2;
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__11;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_discrTree___default;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__2;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1;
lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instBEqArray___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_config;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__8;
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2763____closed__1;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_UnificationHints_add___spec__10(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__12;
static lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__5;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__7;
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
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
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return x_1;
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
x_1 = l_Lean_Meta_instInhabitedUnificationHints___closed__3;
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
x_2 = lean_alloc_ctor(3, 1, 0);
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
x_2 = lean_alloc_ctor(3, 1, 0);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_Meta_DiscrTree_Key_format(x_7);
x_10 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(x_8);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
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
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Meta_DiscrTree_Key_format(x_27);
x_30 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__2;
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2(x_28);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = 0;
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_box(1);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_2);
x_1 = x_26;
x_2 = x_44;
goto _start;
}
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
x_7 = 1;
x_8 = l_Lean_Name_toString(x_4, x_7);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_2 = x_10;
x_3 = x_5;
goto _start;
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
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = 1;
x_11 = l_Lean_Name_toString(x_9, x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_List_foldl___at_Lean_Meta_instToFormatUnificationHints___spec__6(x_2, x_12, x_4);
return x_13;
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
x_2 = lean_alloc_ctor(3, 1, 0);
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
x_2 = lean_alloc_ctor(3, 1, 0);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_3 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__5;
x_4 = l_Std_Format_joinSep___at_Lean_Meta_instToFormatUnificationHints___spec__5(x_1, x_3);
x_5 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__9;
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__11;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4___closed__8;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
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
x_2 = lean_alloc_ctor(3, 1, 0);
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
x_2 = lean_alloc_ctor(3, 1, 0);
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
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Array_isEmpty___rarg(x_2);
x_5 = lean_array_to_list(lean_box(0), x_3);
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3(x_5, x_6);
x_8 = l_Std_Format_join(x_7);
if (x_4 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_9 = lean_array_to_list(lean_box(0), x_2);
x_10 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(x_9);
x_11 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__6;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__4;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__2;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_27 = l_Lean_Meta_DiscrTree_Trie_format___at_Lean_Meta_instToFormatUnificationHints___spec__2___closed__7;
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__6;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__8;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_List_mapTR_loop___at_Lean_Meta_instToFormatUnificationHints___spec__3___closed__5;
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = 0;
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_35);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_instToFormatUnificationHints___spec__7(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_UnificationHints_config___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_3);
lean_ctor_set_uint8(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_UnificationHints_config() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_UnificationHints_config___closed__1;
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
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_5, x_9);
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
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2;
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
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_3, x_11);
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
x_23 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_UnificationHints_add___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
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
x_18 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_3, x_17);
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
x_21 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_4, x_19);
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
x_28 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_4, x_26);
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
x_63 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_4, x_60);
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
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_5, x_8, x_9, x_2, x_3);
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
x_18 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6(x_13, x_16, x_17, x_2, x_3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_9);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_15, x_14);
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
lean_dec(x_2);
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
x_41 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_40);
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_11);
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
lean_dec(x_2);
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
x_35 = l_Lean_Meta_DiscrTree_Key_lt(x_34, x_11);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_34);
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
lean_dec(x_2);
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
x_61 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_60);
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
x_66 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_65);
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
x_71 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_5);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_push(x_6, x_72);
return x_73;
}
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedUnificationHintEntry___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_UnificationHints_add___spec__10(x_7, x_2, x_11);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_fget(x_1, x_4);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1;
lean_inc(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(x_1, x_2, x_3, x_4, x_13, x_8, x_15);
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
x_19 = lean_array_get_size(x_1);
x_20 = lean_nat_dec_lt(x_4, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_UnificationHints_add___spec__10(x_17, x_2, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_array_fget(x_1, x_4);
x_25 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1;
lean_inc(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(x_1, x_2, x_3, x_4, x_24, x_18, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_UnificationHints_add___spec__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_box(0));
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
x_3 = lean_unsigned_to_nat(438u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_10 = l___private_Init_Util_0__outOfBounds___rarg(x_9);
lean_inc(x_10);
lean_inc(x_1);
x_11 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_12);
lean_dec(x_2);
x_14 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(x_1, x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_2, x_3, x_4, x_16, x_15);
lean_dec(x_2);
x_18 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(x_1, x_10, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_2, x_7);
lean_inc(x_19);
lean_inc(x_1);
x_20 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_UnificationHints_add___spec__2(x_1, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_21);
lean_dec(x_2);
x_23 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(x_1, x_19, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_unsigned_to_nat(1u);
x_26 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_2, x_3, x_4, x_25, x_24);
lean_dec(x_2);
x_27 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_UnificationHints_add___spec__5(x_1, x_19, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___closed__4;
x_29 = l_panic___at_Lean_Meta_UnificationHints_add___spec__13(x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_UnificationHints_config;
x_6 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(x_1, x_3, x_4, x_5);
return x_6;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_UnificationHints_add___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_binInsertM___at_Lean_Meta_UnificationHints_add___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_UnificationHints_add___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unificationHintExtension", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_UnificationHints_add), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__4;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__5;
x_3 = l_Lean_Meta_UnificationHints_discrTree___default___closed__1;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__6;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__7;
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqLocalInstance___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__6;
x_2 = lean_alloc_closure((void*)(l_Array_instBEqArray___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__7;
x_2 = l_Lean_Expr_instBEqExpr;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashableLocalInstance___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__9;
x_2 = lean_alloc_closure((void*)(l_instHashableArray___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__10;
x_2 = l_Lean_Expr_instHashableExpr;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__12() {
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
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__13() {
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
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__14() {
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
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__15() {
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
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__15;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__3;
x_2 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__5;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__12;
x_4 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__16;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
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
x_19 = lean_st_ref_take(x_5, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_20, 1);
lean_dec(x_23);
x_24 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17;
lean_ctor_set(x_20, 1, x_24);
x_25 = lean_st_ref_set(x_5, x_20, x_21);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 2);
x_34 = lean_ctor_get(x_20, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_35 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17;
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
x_37 = lean_st_ref_set(x_5, x_36, x_21);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
x_44 = lean_ctor_get(x_10, 2);
x_45 = lean_ctor_get(x_10, 3);
x_46 = lean_ctor_get(x_10, 5);
x_47 = lean_ctor_get(x_10, 6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_48 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_42, x_2);
x_49 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
x_50 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_43);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_49);
lean_ctor_set(x_50, 5, x_46);
lean_ctor_set(x_50, 6, x_47);
x_51 = lean_st_ref_set(x_7, x_50, x_11);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_take(x_5, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 3);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
x_60 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17;
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 4, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_57);
lean_ctor_set(x_61, 3, x_58);
x_62 = lean_st_ref_set(x_5, x_61, x_55);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
case 1:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_6);
x_67 = lean_st_ref_take(x_7, x_8);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_71 = lean_ctor_get(x_68, 0);
x_72 = lean_ctor_get(x_68, 4);
lean_dec(x_72);
x_73 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_71, x_2);
x_74 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
lean_ctor_set(x_68, 4, x_74);
lean_ctor_set(x_68, 0, x_73);
x_75 = lean_st_ref_set(x_7, x_68, x_69);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_take(x_5, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_78, 1);
lean_dec(x_81);
x_82 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17;
lean_ctor_set(x_78, 1, x_82);
x_83 = lean_st_ref_set(x_5, x_78, x_79);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
x_86 = lean_box(0);
lean_ctor_set(x_83, 0, x_86);
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_90 = lean_ctor_get(x_78, 0);
x_91 = lean_ctor_get(x_78, 2);
x_92 = lean_ctor_get(x_78, 3);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_78);
x_93 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17;
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_91);
lean_ctor_set(x_94, 3, x_92);
x_95 = lean_st_ref_set(x_5, x_94, x_79);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_100 = lean_ctor_get(x_68, 0);
x_101 = lean_ctor_get(x_68, 1);
x_102 = lean_ctor_get(x_68, 2);
x_103 = lean_ctor_get(x_68, 3);
x_104 = lean_ctor_get(x_68, 5);
x_105 = lean_ctor_get(x_68, 6);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_68);
x_106 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_100, x_2);
x_107 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
x_108 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_101);
lean_ctor_set(x_108, 2, x_102);
lean_ctor_set(x_108, 3, x_103);
lean_ctor_set(x_108, 4, x_107);
lean_ctor_set(x_108, 5, x_104);
lean_ctor_set(x_108, 6, x_105);
x_109 = lean_st_ref_set(x_7, x_108, x_69);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_st_ref_take(x_5, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 x_117 = x_112;
} else {
 lean_dec_ref(x_112);
 x_117 = lean_box(0);
}
x_118 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 4, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_115);
lean_ctor_set(x_119, 3, x_116);
x_120 = lean_st_ref_set(x_5, x_119, x_113);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
}
default: 
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_6, 6);
lean_inc(x_125);
lean_dec(x_6);
x_126 = lean_st_ref_take(x_7, x_8);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = !lean_is_exclusive(x_127);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_130 = lean_ctor_get(x_127, 0);
x_131 = lean_ctor_get(x_127, 4);
lean_dec(x_131);
x_132 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_130, x_125, x_2);
x_133 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
lean_ctor_set(x_127, 4, x_133);
lean_ctor_set(x_127, 0, x_132);
x_134 = lean_st_ref_set(x_7, x_127, x_128);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_st_ref_take(x_5, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = !lean_is_exclusive(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_140 = lean_ctor_get(x_137, 1);
lean_dec(x_140);
x_141 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17;
lean_ctor_set(x_137, 1, x_141);
x_142 = lean_st_ref_set(x_5, x_137, x_138);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_142, 0);
lean_dec(x_144);
x_145 = lean_box(0);
lean_ctor_set(x_142, 0, x_145);
return x_142;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
lean_dec(x_142);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_149 = lean_ctor_get(x_137, 0);
x_150 = lean_ctor_get(x_137, 2);
x_151 = lean_ctor_get(x_137, 3);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_137);
x_152 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17;
x_153 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_150);
lean_ctor_set(x_153, 3, x_151);
x_154 = lean_st_ref_set(x_5, x_153, x_138);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
x_157 = lean_box(0);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_159 = lean_ctor_get(x_127, 0);
x_160 = lean_ctor_get(x_127, 1);
x_161 = lean_ctor_get(x_127, 2);
x_162 = lean_ctor_get(x_127, 3);
x_163 = lean_ctor_get(x_127, 5);
x_164 = lean_ctor_get(x_127, 6);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_127);
x_165 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_159, x_125, x_2);
x_166 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__2;
x_167 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_160);
lean_ctor_set(x_167, 2, x_161);
lean_ctor_set(x_167, 3, x_162);
lean_ctor_set(x_167, 4, x_166);
lean_ctor_set(x_167, 5, x_163);
lean_ctor_set(x_167, 6, x_164);
x_168 = lean_st_ref_set(x_7, x_167, x_128);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = lean_st_ref_take(x_5, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 3);
lean_inc(x_175);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 x_176 = x_171;
} else {
 lean_dec_ref(x_171);
 x_176 = lean_box(0);
}
x_177 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17;
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(0, 4, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_173);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set(x_178, 2, x_174);
lean_ctor_set(x_178, 3, x_175);
x_179 = lean_st_ref_set(x_5, x_178, x_172);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
x_182 = lean_box(0);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Meta_UnificationHints_config;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_Meta_DiscrTree_mkPath(x_26, x_27, x_3, x_4, x_5, x_6, x_19);
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lambda__1___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = 0;
x_11 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_2);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_2);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__2() {
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__3;
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__1;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__6;
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__8() {
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__9() {
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__8;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__9;
x_4 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__1;
x_5 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__10;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__5;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Attribute_Builtin_ensureNoArgs(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__11;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__7;
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attribute cannot be erased", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__2;
x_6 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__4;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__6;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("UnificationHint", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__10;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__12;
x_2 = lean_unsigned_to_nat(967u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unification_hint", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unification hint", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__13;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__15;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__16;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__17;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__18;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__19;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__20;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2(x_1, x_2, x_3, x_4);
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
lean_ctor_set_uint8(x_9, 9, x_11);
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get_uint8(x_9, 0);
x_22 = lean_ctor_get_uint8(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, 2);
x_24 = lean_ctor_get_uint8(x_9, 3);
x_25 = lean_ctor_get_uint8(x_9, 4);
x_26 = lean_ctor_get_uint8(x_9, 5);
x_27 = lean_ctor_get_uint8(x_9, 6);
x_28 = lean_ctor_get_uint8(x_9, 7);
x_29 = lean_ctor_get_uint8(x_9, 8);
x_30 = lean_ctor_get_uint8(x_9, 10);
x_31 = lean_ctor_get_uint8(x_9, 11);
lean_dec(x_9);
x_32 = 2;
x_33 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_33, 0, x_21);
lean_ctor_set_uint8(x_33, 1, x_22);
lean_ctor_set_uint8(x_33, 2, x_23);
lean_ctor_set_uint8(x_33, 3, x_24);
lean_ctor_set_uint8(x_33, 4, x_25);
lean_ctor_set_uint8(x_33, 5, x_26);
lean_ctor_set_uint8(x_33, 6, x_27);
lean_ctor_set_uint8(x_33, 7, x_28);
lean_ctor_set_uint8(x_33, 8, x_29);
lean_ctor_set_uint8(x_33, 9, x_32);
lean_ctor_set_uint8(x_33, 10, x_30);
lean_ctor_set_uint8(x_33, 11, x_31);
lean_ctor_set(x_3, 0, x_33);
x_34 = lean_is_expr_def_eq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_41 = x_34;
} else {
 lean_dec_ref(x_34);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_ctor_get(x_3, 1);
x_45 = lean_ctor_get(x_3, 2);
x_46 = lean_ctor_get(x_3, 3);
x_47 = lean_ctor_get(x_3, 4);
x_48 = lean_ctor_get(x_3, 5);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_3);
x_49 = lean_ctor_get_uint8(x_43, 0);
x_50 = lean_ctor_get_uint8(x_43, 1);
x_51 = lean_ctor_get_uint8(x_43, 2);
x_52 = lean_ctor_get_uint8(x_43, 3);
x_53 = lean_ctor_get_uint8(x_43, 4);
x_54 = lean_ctor_get_uint8(x_43, 5);
x_55 = lean_ctor_get_uint8(x_43, 6);
x_56 = lean_ctor_get_uint8(x_43, 7);
x_57 = lean_ctor_get_uint8(x_43, 8);
x_58 = lean_ctor_get_uint8(x_43, 10);
x_59 = lean_ctor_get_uint8(x_43, 11);
if (lean_is_exclusive(x_43)) {
 x_60 = x_43;
} else {
 lean_dec_ref(x_43);
 x_60 = lean_box(0);
}
x_61 = 2;
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 0, 12);
} else {
 x_62 = x_60;
}
lean_ctor_set_uint8(x_62, 0, x_49);
lean_ctor_set_uint8(x_62, 1, x_50);
lean_ctor_set_uint8(x_62, 2, x_51);
lean_ctor_set_uint8(x_62, 3, x_52);
lean_ctor_set_uint8(x_62, 4, x_53);
lean_ctor_set_uint8(x_62, 5, x_54);
lean_ctor_set_uint8(x_62, 6, x_55);
lean_ctor_set_uint8(x_62, 7, x_56);
lean_ctor_set_uint8(x_62, 8, x_57);
lean_ctor_set_uint8(x_62, 9, x_61);
lean_ctor_set_uint8(x_62, 10, x_58);
lean_ctor_set_uint8(x_62, 11, x_59);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_44);
lean_ctor_set(x_63, 2, x_45);
lean_ctor_set(x_63, 3, x_46);
lean_ctor_set(x_63, 4, x_47);
lean_ctor_set(x_63, 5, x_48);
x_64 = lean_is_expr_def_eq(x_1, x_2, x_63, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
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
x_41 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_37, x_40);
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
x_79 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_74, x_78);
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
x_125 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_120, x_124);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__1;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = lean_box(0);
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" succeeded, applying constraints", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = l_Lean_Meta_saveState___rarg(x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_7, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_50; lean_object* x_51; lean_object* x_74; 
x_26 = lean_ctor_get(x_21, 5);
lean_dec(x_26);
x_27 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
lean_ctor_set(x_21, 5, x_27);
x_28 = lean_st_ref_set(x_7, x_20, x_22);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
lean_inc(x_3);
x_74 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_ConstantInfo_levelParams(x_75);
x_78 = lean_box(0);
x_79 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_77, x_78, x_6, x_7, x_8, x_9, x_76);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_9);
lean_inc(x_8);
x_82 = l_Lean_Core_instantiateValueLevelParams(x_75, x_80, x_8, x_9, x_81);
lean_dec(x_75);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_124; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_box(0);
lean_inc(x_6);
x_86 = l_Lean_Meta_lambdaMetaTelescope(x_83, x_85, x_6, x_7, x_8, x_9, x_84);
lean_dec(x_83);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_124 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_92);
if (lean_obj_tag(x_124) == 0)
{
lean_dec(x_124);
lean_dec(x_2);
lean_dec(x_1);
x_93 = x_85;
x_94 = x_89;
goto block_123;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_125 = lean_ctor_get(x_6, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_ctor_get(x_6, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_6, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_6, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_6, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_6, 5);
lean_inc(x_131);
x_132 = !lean_is_exclusive(x_125);
if (x_132 == 0)
{
uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = 0;
lean_ctor_set_uint8(x_125, 5, x_133);
x_134 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_127);
lean_ctor_set(x_134, 2, x_128);
lean_ctor_set(x_134, 3, x_129);
lean_ctor_set(x_134, 4, x_130);
lean_ctor_set(x_134, 5, x_131);
x_135 = lean_ctor_get(x_126, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_134);
x_137 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_136, x_1, x_134, x_7, x_8, x_9, x_89);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_126);
lean_dec(x_2);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_93 = x_85;
x_94 = x_140;
goto block_123;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
lean_dec(x_135);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_143 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_142, x_2, x_134, x_7, x_8, x_9, x_141);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_unbox(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_126);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_93 = x_85;
x_94 = x_146;
goto block_123;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_126);
x_93 = x_148;
x_94 = x_147;
goto block_123;
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_126);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_3);
x_149 = lean_ctor_get(x_143, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_143, 1);
lean_inc(x_150);
lean_dec(x_143);
x_34 = x_149;
x_35 = x_150;
goto block_49;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_126);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_151 = lean_ctor_get(x_137, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_137, 1);
lean_inc(x_152);
lean_dec(x_137);
x_34 = x_151;
x_35 = x_152;
goto block_49;
}
}
else
{
uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_153 = lean_ctor_get_uint8(x_125, 0);
x_154 = lean_ctor_get_uint8(x_125, 1);
x_155 = lean_ctor_get_uint8(x_125, 2);
x_156 = lean_ctor_get_uint8(x_125, 3);
x_157 = lean_ctor_get_uint8(x_125, 4);
x_158 = lean_ctor_get_uint8(x_125, 6);
x_159 = lean_ctor_get_uint8(x_125, 7);
x_160 = lean_ctor_get_uint8(x_125, 8);
x_161 = lean_ctor_get_uint8(x_125, 9);
x_162 = lean_ctor_get_uint8(x_125, 10);
x_163 = lean_ctor_get_uint8(x_125, 11);
lean_dec(x_125);
x_164 = 0;
x_165 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_165, 0, x_153);
lean_ctor_set_uint8(x_165, 1, x_154);
lean_ctor_set_uint8(x_165, 2, x_155);
lean_ctor_set_uint8(x_165, 3, x_156);
lean_ctor_set_uint8(x_165, 4, x_157);
lean_ctor_set_uint8(x_165, 5, x_164);
lean_ctor_set_uint8(x_165, 6, x_158);
lean_ctor_set_uint8(x_165, 7, x_159);
lean_ctor_set_uint8(x_165, 8, x_160);
lean_ctor_set_uint8(x_165, 9, x_161);
lean_ctor_set_uint8(x_165, 10, x_162);
lean_ctor_set_uint8(x_165, 11, x_163);
x_166 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_127);
lean_ctor_set(x_166, 2, x_128);
lean_ctor_set(x_166, 3, x_129);
lean_ctor_set(x_166, 4, x_130);
lean_ctor_set(x_166, 5, x_131);
x_167 = lean_ctor_get(x_126, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_166);
x_169 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_168, x_1, x_166, x_7, x_8, x_9, x_89);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_126);
lean_dec(x_2);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_93 = x_85;
x_94 = x_172;
goto block_123;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
lean_dec(x_169);
x_174 = lean_ctor_get(x_167, 1);
lean_inc(x_174);
lean_dec(x_167);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_175 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_174, x_2, x_166, x_7, x_8, x_9, x_173);
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
lean_dec(x_126);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
x_93 = x_85;
x_94 = x_178;
goto block_123;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
lean_dec(x_175);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_126);
x_93 = x_180;
x_94 = x_179;
goto block_123;
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_126);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_3);
x_181 = lean_ctor_get(x_175, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_175, 1);
lean_inc(x_182);
lean_dec(x_175);
x_34 = x_181;
x_35 = x_182;
goto block_49;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_126);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_183 = lean_ctor_get(x_169, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_169, 1);
lean_inc(x_184);
lean_dec(x_169);
x_34 = x_183;
x_35 = x_184;
goto block_49;
}
}
}
block_123:
{
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_95; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_4);
lean_dec(x_3);
x_95 = 0;
x_50 = x_95;
x_51 = x_94;
goto block_73;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
lean_inc(x_4);
x_97 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_94);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_4);
lean_dec(x_3);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_102 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_96, x_85, x_91, x_90, x_101, x_6, x_7, x_8, x_9, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_unbox(x_103);
lean_dec(x_103);
x_50 = x_105;
x_51 = x_104;
goto block_73;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_31);
x_106 = lean_ctor_get(x_102, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
lean_dec(x_102);
x_34 = x_106;
x_35 = x_107;
goto block_49;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_108 = lean_ctor_get(x_97, 1);
lean_inc(x_108);
lean_dec(x_97);
x_109 = l_Lean_MessageData_ofName(x_3);
x_110 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__6;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_113, x_6, x_7, x_8, x_9, x_108);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_117 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_96, x_85, x_91, x_90, x_115, x_6, x_7, x_8, x_9, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_unbox(x_118);
lean_dec(x_118);
x_50 = x_120;
x_51 = x_119;
goto block_73;
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_31);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
lean_dec(x_117);
x_34 = x_121;
x_35 = x_122;
goto block_49;
}
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = lean_ctor_get(x_82, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_82, 1);
lean_inc(x_186);
lean_dec(x_82);
x_34 = x_185;
x_35 = x_186;
goto block_49;
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_187 = lean_ctor_get(x_74, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_74, 1);
lean_inc(x_188);
lean_dec(x_74);
x_34 = x_187;
x_35 = x_188;
goto block_49;
}
block_49:
{
uint8_t x_36; 
x_36 = l_Lean_Exception_isRuntime(x_34);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
lean_dec(x_33);
x_37 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_34);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_33)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_33;
 lean_ctor_set_tag(x_43, 1);
}
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_35);
return x_43;
}
else
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_33);
x_44 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_34);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
block_73:
{
if (x_50 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_33);
lean_dec(x_31);
x_52 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
x_11 = x_54;
x_12 = x_53;
goto block_15;
}
else
{
uint8_t x_55; lean_object* x_56; 
x_55 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_56 = l_Lean_Meta_processPostponed(x_5, x_55, x_6, x_7, x_8, x_9, x_51);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_33);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_31);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
x_11 = x_62;
x_12 = x_61;
goto block_15;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_17);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec(x_56);
x_64 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_PersistentArray_append___rarg(x_31, x_65);
x_68 = l_Lean_Meta_setPostponed(x_67, x_6, x_7, x_8, x_9, x_66);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4;
x_11 = x_70;
x_12 = x_69;
goto block_15;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_31);
x_71 = lean_ctor_get(x_56, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_56, 1);
lean_inc(x_72);
lean_dec(x_56);
x_34 = x_71;
x_35 = x_72;
goto block_49;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_217; lean_object* x_218; lean_object* x_241; 
x_189 = lean_ctor_get(x_21, 0);
x_190 = lean_ctor_get(x_21, 1);
x_191 = lean_ctor_get(x_21, 2);
x_192 = lean_ctor_get(x_21, 3);
x_193 = lean_ctor_get(x_21, 4);
x_194 = lean_ctor_get(x_21, 6);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_21);
x_195 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
x_196 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_196, 0, x_189);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 3, x_192);
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 5, x_195);
lean_ctor_set(x_196, 6, x_194);
lean_ctor_set(x_20, 1, x_196);
x_197 = lean_st_ref_set(x_7, x_20, x_22);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_202 = x_199;
} else {
 lean_dec_ref(x_199);
 x_202 = lean_box(0);
}
lean_inc(x_3);
x_241 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_201);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_ConstantInfo_levelParams(x_242);
x_245 = lean_box(0);
x_246 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_244, x_245, x_6, x_7, x_8, x_9, x_243);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
lean_inc(x_9);
lean_inc(x_8);
x_249 = l_Lean_Core_instantiateValueLevelParams(x_242, x_247, x_8, x_9, x_248);
lean_dec(x_242);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_291; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_box(0);
lean_inc(x_6);
x_253 = l_Lean_Meta_lambdaMetaTelescope(x_250, x_252, x_6, x_7, x_8, x_9, x_251);
lean_dec(x_250);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
lean_dec(x_253);
x_257 = lean_ctor_get(x_254, 0);
lean_inc(x_257);
lean_dec(x_254);
x_258 = lean_ctor_get(x_255, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_dec(x_255);
x_291 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_259);
if (lean_obj_tag(x_291) == 0)
{
lean_dec(x_291);
lean_dec(x_2);
lean_dec(x_1);
x_260 = x_252;
x_261 = x_256;
goto block_290;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; uint8_t x_300; uint8_t x_301; uint8_t x_302; uint8_t x_303; uint8_t x_304; uint8_t x_305; uint8_t x_306; uint8_t x_307; uint8_t x_308; uint8_t x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_292 = lean_ctor_get(x_6, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 0);
lean_inc(x_293);
lean_dec(x_291);
x_294 = lean_ctor_get(x_6, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_6, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_6, 3);
lean_inc(x_296);
x_297 = lean_ctor_get(x_6, 4);
lean_inc(x_297);
x_298 = lean_ctor_get(x_6, 5);
lean_inc(x_298);
x_299 = lean_ctor_get_uint8(x_292, 0);
x_300 = lean_ctor_get_uint8(x_292, 1);
x_301 = lean_ctor_get_uint8(x_292, 2);
x_302 = lean_ctor_get_uint8(x_292, 3);
x_303 = lean_ctor_get_uint8(x_292, 4);
x_304 = lean_ctor_get_uint8(x_292, 6);
x_305 = lean_ctor_get_uint8(x_292, 7);
x_306 = lean_ctor_get_uint8(x_292, 8);
x_307 = lean_ctor_get_uint8(x_292, 9);
x_308 = lean_ctor_get_uint8(x_292, 10);
x_309 = lean_ctor_get_uint8(x_292, 11);
if (lean_is_exclusive(x_292)) {
 x_310 = x_292;
} else {
 lean_dec_ref(x_292);
 x_310 = lean_box(0);
}
x_311 = 0;
if (lean_is_scalar(x_310)) {
 x_312 = lean_alloc_ctor(0, 0, 12);
} else {
 x_312 = x_310;
}
lean_ctor_set_uint8(x_312, 0, x_299);
lean_ctor_set_uint8(x_312, 1, x_300);
lean_ctor_set_uint8(x_312, 2, x_301);
lean_ctor_set_uint8(x_312, 3, x_302);
lean_ctor_set_uint8(x_312, 4, x_303);
lean_ctor_set_uint8(x_312, 5, x_311);
lean_ctor_set_uint8(x_312, 6, x_304);
lean_ctor_set_uint8(x_312, 7, x_305);
lean_ctor_set_uint8(x_312, 8, x_306);
lean_ctor_set_uint8(x_312, 9, x_307);
lean_ctor_set_uint8(x_312, 10, x_308);
lean_ctor_set_uint8(x_312, 11, x_309);
x_313 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_294);
lean_ctor_set(x_313, 2, x_295);
lean_ctor_set(x_313, 3, x_296);
lean_ctor_set(x_313, 4, x_297);
lean_ctor_set(x_313, 5, x_298);
x_314 = lean_ctor_get(x_293, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_313);
x_316 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_315, x_1, x_313, x_7, x_8, x_9, x_256);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; uint8_t x_318; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_unbox(x_317);
lean_dec(x_317);
if (x_318 == 0)
{
lean_object* x_319; 
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_293);
lean_dec(x_2);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
lean_dec(x_316);
x_260 = x_252;
x_261 = x_319;
goto block_290;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_316, 1);
lean_inc(x_320);
lean_dec(x_316);
x_321 = lean_ctor_get(x_314, 1);
lean_inc(x_321);
lean_dec(x_314);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_322 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_321, x_2, x_313, x_7, x_8, x_9, x_320);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; uint8_t x_324; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_unbox(x_323);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; 
lean_dec(x_293);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
lean_dec(x_322);
x_260 = x_252;
x_261 = x_325;
goto block_290;
}
else
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_322, 1);
lean_inc(x_326);
lean_dec(x_322);
x_327 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_327, 0, x_293);
x_260 = x_327;
x_261 = x_326;
goto block_290;
}
}
else
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_293);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_200);
lean_dec(x_4);
lean_dec(x_3);
x_328 = lean_ctor_get(x_322, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_322, 1);
lean_inc(x_329);
lean_dec(x_322);
x_203 = x_328;
x_204 = x_329;
goto block_216;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_293);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_200);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_330 = lean_ctor_get(x_316, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_316, 1);
lean_inc(x_331);
lean_dec(x_316);
x_203 = x_330;
x_204 = x_331;
goto block_216;
}
}
block_290:
{
if (lean_obj_tag(x_260) == 0)
{
uint8_t x_262; 
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_4);
lean_dec(x_3);
x_262 = 0;
x_217 = x_262;
x_218 = x_261;
goto block_240;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_263 = lean_ctor_get(x_260, 0);
lean_inc(x_263);
lean_dec(x_260);
lean_inc(x_4);
x_264 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_261);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_unbox(x_265);
lean_dec(x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_4);
lean_dec(x_3);
x_267 = lean_ctor_get(x_264, 1);
lean_inc(x_267);
lean_dec(x_264);
x_268 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_269 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_263, x_252, x_258, x_257, x_268, x_6, x_7, x_8, x_9, x_267);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_unbox(x_270);
lean_dec(x_270);
x_217 = x_272;
x_218 = x_271;
goto block_240;
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_200);
x_273 = lean_ctor_get(x_269, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_269, 1);
lean_inc(x_274);
lean_dec(x_269);
x_203 = x_273;
x_204 = x_274;
goto block_216;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_275 = lean_ctor_get(x_264, 1);
lean_inc(x_275);
lean_dec(x_264);
x_276 = l_Lean_MessageData_ofName(x_3);
x_277 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_278 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__6;
x_280 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_280, x_6, x_7, x_8, x_9, x_275);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_284 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_263, x_252, x_258, x_257, x_282, x_6, x_7, x_8, x_9, x_283);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_unbox(x_285);
lean_dec(x_285);
x_217 = x_287;
x_218 = x_286;
goto block_240;
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_200);
x_288 = lean_ctor_get(x_284, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_284, 1);
lean_inc(x_289);
lean_dec(x_284);
x_203 = x_288;
x_204 = x_289;
goto block_216;
}
}
}
}
}
else
{
lean_object* x_332; lean_object* x_333; 
lean_dec(x_200);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_332 = lean_ctor_get(x_249, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_249, 1);
lean_inc(x_333);
lean_dec(x_249);
x_203 = x_332;
x_204 = x_333;
goto block_216;
}
}
else
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_200);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_334 = lean_ctor_get(x_241, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_241, 1);
lean_inc(x_335);
lean_dec(x_241);
x_203 = x_334;
x_204 = x_335;
goto block_216;
}
block_216:
{
uint8_t x_205; 
x_205 = l_Lean_Exception_isRuntime(x_203);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_202);
x_206 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_204);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
 lean_ctor_set_tag(x_209, 1);
}
lean_ctor_set(x_209, 0, x_203);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
else
{
uint8_t x_210; 
x_210 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
if (x_210 == 0)
{
lean_object* x_211; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_202)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_202;
 lean_ctor_set_tag(x_211, 1);
}
lean_ctor_set(x_211, 0, x_203);
lean_ctor_set(x_211, 1, x_204);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_202);
x_212 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_204);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
 lean_ctor_set_tag(x_215, 1);
}
lean_ctor_set(x_215, 0, x_203);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
}
block_240:
{
if (x_217 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_202);
lean_dec(x_200);
x_219 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_218);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
x_11 = x_221;
x_12 = x_220;
goto block_15;
}
else
{
uint8_t x_222; lean_object* x_223; 
x_222 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_223 = l_Lean_Meta_processPostponed(x_5, x_222, x_6, x_7, x_8, x_9, x_218);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; uint8_t x_225; 
lean_dec(x_202);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_unbox(x_224);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_200);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec(x_223);
x_227 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_226);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
x_11 = x_229;
x_12 = x_228;
goto block_15;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_17);
x_230 = lean_ctor_get(x_223, 1);
lean_inc(x_230);
lean_dec(x_223);
x_231 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_230);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = l_Lean_PersistentArray_append___rarg(x_200, x_232);
x_235 = l_Lean_Meta_setPostponed(x_234, x_6, x_7, x_8, x_9, x_233);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_237 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4;
x_11 = x_237;
x_12 = x_236;
goto block_15;
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_200);
x_238 = lean_ctor_get(x_223, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_223, 1);
lean_inc(x_239);
lean_dec(x_223);
x_203 = x_238;
x_204 = x_239;
goto block_216;
}
}
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_369; lean_object* x_370; lean_object* x_393; 
x_336 = lean_ctor_get(x_20, 0);
x_337 = lean_ctor_get(x_20, 2);
x_338 = lean_ctor_get(x_20, 3);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_20);
x_339 = lean_ctor_get(x_21, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_21, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_21, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_21, 3);
lean_inc(x_342);
x_343 = lean_ctor_get(x_21, 4);
lean_inc(x_343);
x_344 = lean_ctor_get(x_21, 6);
lean_inc(x_344);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 lean_ctor_release(x_21, 6);
 x_345 = x_21;
} else {
 lean_dec_ref(x_21);
 x_345 = lean_box(0);
}
x_346 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
if (lean_is_scalar(x_345)) {
 x_347 = lean_alloc_ctor(0, 7, 0);
} else {
 x_347 = x_345;
}
lean_ctor_set(x_347, 0, x_339);
lean_ctor_set(x_347, 1, x_340);
lean_ctor_set(x_347, 2, x_341);
lean_ctor_set(x_347, 3, x_342);
lean_ctor_set(x_347, 4, x_343);
lean_ctor_set(x_347, 5, x_346);
lean_ctor_set(x_347, 6, x_344);
x_348 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_348, 0, x_336);
lean_ctor_set(x_348, 1, x_347);
lean_ctor_set(x_348, 2, x_337);
lean_ctor_set(x_348, 3, x_338);
x_349 = lean_st_ref_set(x_7, x_348, x_22);
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
lean_dec(x_349);
x_351 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_350);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_354 = x_351;
} else {
 lean_dec_ref(x_351);
 x_354 = lean_box(0);
}
lean_inc(x_3);
x_393 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_353);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = l_Lean_ConstantInfo_levelParams(x_394);
x_397 = lean_box(0);
x_398 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_396, x_397, x_6, x_7, x_8, x_9, x_395);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
lean_inc(x_9);
lean_inc(x_8);
x_401 = l_Lean_Core_instantiateValueLevelParams(x_394, x_399, x_8, x_9, x_400);
lean_dec(x_394);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_443; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_box(0);
lean_inc(x_6);
x_405 = l_Lean_Meta_lambdaMetaTelescope(x_402, x_404, x_6, x_7, x_8, x_9, x_403);
lean_dec(x_402);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_406, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
lean_dec(x_405);
x_409 = lean_ctor_get(x_406, 0);
lean_inc(x_409);
lean_dec(x_406);
x_410 = lean_ctor_get(x_407, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_407, 1);
lean_inc(x_411);
lean_dec(x_407);
x_443 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_411);
if (lean_obj_tag(x_443) == 0)
{
lean_dec(x_443);
lean_dec(x_2);
lean_dec(x_1);
x_412 = x_404;
x_413 = x_408;
goto block_442;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; uint8_t x_452; uint8_t x_453; uint8_t x_454; uint8_t x_455; uint8_t x_456; uint8_t x_457; uint8_t x_458; uint8_t x_459; uint8_t x_460; uint8_t x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_444 = lean_ctor_get(x_6, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 0);
lean_inc(x_445);
lean_dec(x_443);
x_446 = lean_ctor_get(x_6, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_6, 2);
lean_inc(x_447);
x_448 = lean_ctor_get(x_6, 3);
lean_inc(x_448);
x_449 = lean_ctor_get(x_6, 4);
lean_inc(x_449);
x_450 = lean_ctor_get(x_6, 5);
lean_inc(x_450);
x_451 = lean_ctor_get_uint8(x_444, 0);
x_452 = lean_ctor_get_uint8(x_444, 1);
x_453 = lean_ctor_get_uint8(x_444, 2);
x_454 = lean_ctor_get_uint8(x_444, 3);
x_455 = lean_ctor_get_uint8(x_444, 4);
x_456 = lean_ctor_get_uint8(x_444, 6);
x_457 = lean_ctor_get_uint8(x_444, 7);
x_458 = lean_ctor_get_uint8(x_444, 8);
x_459 = lean_ctor_get_uint8(x_444, 9);
x_460 = lean_ctor_get_uint8(x_444, 10);
x_461 = lean_ctor_get_uint8(x_444, 11);
if (lean_is_exclusive(x_444)) {
 x_462 = x_444;
} else {
 lean_dec_ref(x_444);
 x_462 = lean_box(0);
}
x_463 = 0;
if (lean_is_scalar(x_462)) {
 x_464 = lean_alloc_ctor(0, 0, 12);
} else {
 x_464 = x_462;
}
lean_ctor_set_uint8(x_464, 0, x_451);
lean_ctor_set_uint8(x_464, 1, x_452);
lean_ctor_set_uint8(x_464, 2, x_453);
lean_ctor_set_uint8(x_464, 3, x_454);
lean_ctor_set_uint8(x_464, 4, x_455);
lean_ctor_set_uint8(x_464, 5, x_463);
lean_ctor_set_uint8(x_464, 6, x_456);
lean_ctor_set_uint8(x_464, 7, x_457);
lean_ctor_set_uint8(x_464, 8, x_458);
lean_ctor_set_uint8(x_464, 9, x_459);
lean_ctor_set_uint8(x_464, 10, x_460);
lean_ctor_set_uint8(x_464, 11, x_461);
x_465 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_446);
lean_ctor_set(x_465, 2, x_447);
lean_ctor_set(x_465, 3, x_448);
lean_ctor_set(x_465, 4, x_449);
lean_ctor_set(x_465, 5, x_450);
x_466 = lean_ctor_get(x_445, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_465);
x_468 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_467, x_1, x_465, x_7, x_8, x_9, x_408);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; uint8_t x_470; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_unbox(x_469);
lean_dec(x_469);
if (x_470 == 0)
{
lean_object* x_471; 
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_445);
lean_dec(x_2);
x_471 = lean_ctor_get(x_468, 1);
lean_inc(x_471);
lean_dec(x_468);
x_412 = x_404;
x_413 = x_471;
goto block_442;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_468, 1);
lean_inc(x_472);
lean_dec(x_468);
x_473 = lean_ctor_get(x_466, 1);
lean_inc(x_473);
lean_dec(x_466);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_474 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_473, x_2, x_465, x_7, x_8, x_9, x_472);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; uint8_t x_476; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_unbox(x_475);
lean_dec(x_475);
if (x_476 == 0)
{
lean_object* x_477; 
lean_dec(x_445);
x_477 = lean_ctor_get(x_474, 1);
lean_inc(x_477);
lean_dec(x_474);
x_412 = x_404;
x_413 = x_477;
goto block_442;
}
else
{
lean_object* x_478; lean_object* x_479; 
x_478 = lean_ctor_get(x_474, 1);
lean_inc(x_478);
lean_dec(x_474);
x_479 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_479, 0, x_445);
x_412 = x_479;
x_413 = x_478;
goto block_442;
}
}
else
{
lean_object* x_480; lean_object* x_481; 
lean_dec(x_445);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_352);
lean_dec(x_4);
lean_dec(x_3);
x_480 = lean_ctor_get(x_474, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_474, 1);
lean_inc(x_481);
lean_dec(x_474);
x_355 = x_480;
x_356 = x_481;
goto block_368;
}
}
}
else
{
lean_object* x_482; lean_object* x_483; 
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_445);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_352);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_482 = lean_ctor_get(x_468, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_468, 1);
lean_inc(x_483);
lean_dec(x_468);
x_355 = x_482;
x_356 = x_483;
goto block_368;
}
}
block_442:
{
if (lean_obj_tag(x_412) == 0)
{
uint8_t x_414; 
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_4);
lean_dec(x_3);
x_414 = 0;
x_369 = x_414;
x_370 = x_413;
goto block_392;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_415 = lean_ctor_get(x_412, 0);
lean_inc(x_415);
lean_dec(x_412);
lean_inc(x_4);
x_416 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_413);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_unbox(x_417);
lean_dec(x_417);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_4);
lean_dec(x_3);
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
lean_dec(x_416);
x_420 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_421 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_415, x_404, x_410, x_409, x_420, x_6, x_7, x_8, x_9, x_419);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = lean_unbox(x_422);
lean_dec(x_422);
x_369 = x_424;
x_370 = x_423;
goto block_392;
}
else
{
lean_object* x_425; lean_object* x_426; 
lean_dec(x_352);
x_425 = lean_ctor_get(x_421, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_421, 1);
lean_inc(x_426);
lean_dec(x_421);
x_355 = x_425;
x_356 = x_426;
goto block_368;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_427 = lean_ctor_get(x_416, 1);
lean_inc(x_427);
lean_dec(x_416);
x_428 = l_Lean_MessageData_ofName(x_3);
x_429 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_430 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
x_431 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__6;
x_432 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
x_433 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_432, x_6, x_7, x_8, x_9, x_427);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_436 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_415, x_404, x_410, x_409, x_434, x_6, x_7, x_8, x_9, x_435);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; uint8_t x_439; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_439 = lean_unbox(x_437);
lean_dec(x_437);
x_369 = x_439;
x_370 = x_438;
goto block_392;
}
else
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_352);
x_440 = lean_ctor_get(x_436, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_436, 1);
lean_inc(x_441);
lean_dec(x_436);
x_355 = x_440;
x_356 = x_441;
goto block_368;
}
}
}
}
}
else
{
lean_object* x_484; lean_object* x_485; 
lean_dec(x_352);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_484 = lean_ctor_get(x_401, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_401, 1);
lean_inc(x_485);
lean_dec(x_401);
x_355 = x_484;
x_356 = x_485;
goto block_368;
}
}
else
{
lean_object* x_486; lean_object* x_487; 
lean_dec(x_352);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_486 = lean_ctor_get(x_393, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_393, 1);
lean_inc(x_487);
lean_dec(x_393);
x_355 = x_486;
x_356 = x_487;
goto block_368;
}
block_368:
{
uint8_t x_357; 
x_357 = l_Lean_Exception_isRuntime(x_355);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_354);
x_358 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_356);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_360 = x_358;
} else {
 lean_dec_ref(x_358);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
 lean_ctor_set_tag(x_361, 1);
}
lean_ctor_set(x_361, 0, x_355);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
else
{
uint8_t x_362; 
x_362 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
if (x_362 == 0)
{
lean_object* x_363; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_354)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_354;
 lean_ctor_set_tag(x_363, 1);
}
lean_ctor_set(x_363, 0, x_355);
lean_ctor_set(x_363, 1, x_356);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_354);
x_364 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_356);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_366 = x_364;
} else {
 lean_dec_ref(x_364);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_367 = x_366;
 lean_ctor_set_tag(x_367, 1);
}
lean_ctor_set(x_367, 0, x_355);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
}
}
block_392:
{
if (x_369 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_354);
lean_dec(x_352);
x_371 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_370);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
lean_dec(x_371);
x_373 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
x_11 = x_373;
x_12 = x_372;
goto block_15;
}
else
{
uint8_t x_374; lean_object* x_375; 
x_374 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_375 = l_Lean_Meta_processPostponed(x_5, x_374, x_6, x_7, x_8, x_9, x_370);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; uint8_t x_377; 
lean_dec(x_354);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_unbox(x_376);
lean_dec(x_376);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_352);
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
lean_dec(x_375);
x_379 = l_Lean_Meta_SavedState_restore(x_17, x_6, x_7, x_8, x_9, x_378);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
x_380 = lean_ctor_get(x_379, 1);
lean_inc(x_380);
lean_dec(x_379);
x_381 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
x_11 = x_381;
x_12 = x_380;
goto block_15;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_17);
x_382 = lean_ctor_get(x_375, 1);
lean_inc(x_382);
lean_dec(x_375);
x_383 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_382);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = l_Lean_PersistentArray_append___rarg(x_352, x_384);
x_387 = l_Lean_Meta_setPostponed(x_386, x_6, x_7, x_8, x_9, x_385);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_389 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4;
x_11 = x_389;
x_12 = x_388;
goto block_15;
}
}
else
{
lean_object* x_390; lean_object* x_391; 
lean_dec(x_352);
x_390 = lean_ctor_get(x_375, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_375, 1);
lean_inc(x_391);
lean_dec(x_375);
x_355 = x_390;
x_356 = x_391;
goto block_368;
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
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
x_1 = lean_mk_string_from_bytes(" =\?= ", 5);
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
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__2;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
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
x_16 = l_Lean_Meta_UnificationHints_config;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Lean_Meta_DiscrTree_getMatch___rarg(x_15, x_1, x_16, x_4, x_5, x_6, x_7, x_11);
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
x_10 = lean_ctor_get_uint8(x_9, 5);
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
x_16 = l_Lean_MessageData_ofExpr(x_1);
x_17 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_tryUnificationHints_tryCandidate___lambda__1___closed__6;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_2);
x_21 = l_Lean_MessageData_ofExpr(x_2);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2763____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__12;
x_2 = lean_unsigned_to_nat(2763u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2763_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2763____closed__1;
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
l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__2 = _init_l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_format___at_Lean_Meta_instToFormatUnificationHints___spec__1___closed__2);
l_Lean_Meta_UnificationHints_config___closed__1 = _init_l_Lean_Meta_UnificationHints_config___closed__1();
lean_mark_persistent(l_Lean_Meta_UnificationHints_config___closed__1);
l_Lean_Meta_UnificationHints_config = _init_l_Lean_Meta_UnificationHints_config();
lean_mark_persistent(l_Lean_Meta_UnificationHints_config);
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_UnificationHints_add___spec__6___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_UnificationHints_add___spec__9___closed__1);
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
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205____closed__7);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_205_(lean_io_mk_world());
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
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__11 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__11();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__11);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__12 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__12();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__12);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__13 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__13();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__13);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__14 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__14();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__14);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__15 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__15();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__15);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__16 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__16();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__16);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addUnificationHint___spec__1___closed__17);
l_Lean_Meta_addUnificationHint___lambda__1___closed__1 = _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_addUnificationHint___lambda__1___closed__1);
l_Lean_Meta_addUnificationHint___lambda__1___closed__2 = _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_addUnificationHint___lambda__1___closed__2);
l_Lean_Meta_addUnificationHint___lambda__1___closed__3 = _init_l_Lean_Meta_addUnificationHint___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_addUnificationHint___lambda__1___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1___closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__2___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__13);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__14 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__14();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__14);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__15 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__15();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__15);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__16 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__16();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__16);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__17 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__17();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__17);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__18 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__18();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__18);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__19 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__19();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__19);
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__20 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__20();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__20);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1 = _init_l_List_forIn_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__2___closed__1();
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
l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4 = _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4();
lean_mark_persistent(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4);
l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__5 = _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__5();
lean_mark_persistent(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__5);
l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__6 = _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__6();
lean_mark_persistent(l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__6);
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
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2763____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2763____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2763____closed__1);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2763_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
