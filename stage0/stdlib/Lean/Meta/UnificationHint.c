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
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2757____closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2757_(lean_object*);
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
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_UnificationHints_add___spec__3___closed__1;
lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instBEqArray___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_config;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__8;
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" succeeded, applying constraints", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__3;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_36; lean_object* x_37; lean_object* x_76; 
x_21 = lean_ctor_get(x_16, 5);
lean_dec(x_21);
x_22 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
lean_ctor_set(x_16, 5, x_22);
x_23 = lean_st_ref_set(x_7, x_15, x_17);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_3);
x_76 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_ConstantInfo_levelParams(x_77);
x_80 = lean_box(0);
x_81 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_79, x_80, x_6, x_7, x_8, x_9, x_78);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_9);
lean_inc(x_8);
x_84 = l_Lean_Core_instantiateValueLevelParams(x_77, x_82, x_8, x_9, x_83);
lean_dec(x_77);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_126; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_box(0);
lean_inc(x_6);
x_88 = l_Lean_Meta_lambdaMetaTelescope(x_85, x_87, x_6, x_7, x_8, x_9, x_86);
lean_dec(x_85);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_126 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_94);
if (lean_obj_tag(x_126) == 0)
{
lean_dec(x_126);
lean_dec(x_2);
lean_dec(x_1);
x_95 = x_87;
x_96 = x_91;
goto block_125;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_127 = lean_ctor_get(x_6, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_6, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_6, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_6, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_6, 4);
lean_inc(x_132);
x_133 = lean_ctor_get(x_6, 5);
lean_inc(x_133);
x_134 = !lean_is_exclusive(x_127);
if (x_134 == 0)
{
uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = 0;
lean_ctor_set_uint8(x_127, 5, x_135);
x_136 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_129);
lean_ctor_set(x_136, 2, x_130);
lean_ctor_set(x_136, 3, x_131);
lean_ctor_set(x_136, 4, x_132);
lean_ctor_set(x_136, 5, x_133);
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_136);
x_139 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_138, x_1, x_136, x_7, x_8, x_9, x_91);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_128);
lean_dec(x_2);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_95 = x_87;
x_96 = x_142;
goto block_125;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_ctor_get(x_137, 1);
lean_inc(x_144);
lean_dec(x_137);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_145 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_144, x_2, x_136, x_7, x_8, x_9, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_128);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_95 = x_87;
x_96 = x_148;
goto block_125;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_145, 1);
lean_inc(x_149);
lean_dec(x_145);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_128);
x_95 = x_150;
x_96 = x_149;
goto block_125;
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_128);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
x_151 = lean_ctor_get(x_145, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_145, 1);
lean_inc(x_152);
lean_dec(x_145);
x_28 = x_151;
x_29 = x_152;
goto block_35;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_128);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_153 = lean_ctor_get(x_139, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_139, 1);
lean_inc(x_154);
lean_dec(x_139);
x_28 = x_153;
x_29 = x_154;
goto block_35;
}
}
else
{
uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_155 = lean_ctor_get_uint8(x_127, 0);
x_156 = lean_ctor_get_uint8(x_127, 1);
x_157 = lean_ctor_get_uint8(x_127, 2);
x_158 = lean_ctor_get_uint8(x_127, 3);
x_159 = lean_ctor_get_uint8(x_127, 4);
x_160 = lean_ctor_get_uint8(x_127, 6);
x_161 = lean_ctor_get_uint8(x_127, 7);
x_162 = lean_ctor_get_uint8(x_127, 8);
x_163 = lean_ctor_get_uint8(x_127, 9);
x_164 = lean_ctor_get_uint8(x_127, 10);
x_165 = lean_ctor_get_uint8(x_127, 11);
lean_dec(x_127);
x_166 = 0;
x_167 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_167, 0, x_155);
lean_ctor_set_uint8(x_167, 1, x_156);
lean_ctor_set_uint8(x_167, 2, x_157);
lean_ctor_set_uint8(x_167, 3, x_158);
lean_ctor_set_uint8(x_167, 4, x_159);
lean_ctor_set_uint8(x_167, 5, x_166);
lean_ctor_set_uint8(x_167, 6, x_160);
lean_ctor_set_uint8(x_167, 7, x_161);
lean_ctor_set_uint8(x_167, 8, x_162);
lean_ctor_set_uint8(x_167, 9, x_163);
lean_ctor_set_uint8(x_167, 10, x_164);
lean_ctor_set_uint8(x_167, 11, x_165);
x_168 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_129);
lean_ctor_set(x_168, 2, x_130);
lean_ctor_set(x_168, 3, x_131);
lean_ctor_set(x_168, 4, x_132);
lean_ctor_set(x_168, 5, x_133);
x_169 = lean_ctor_get(x_128, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_168);
x_171 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_170, x_1, x_168, x_7, x_8, x_9, x_91);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_128);
lean_dec(x_2);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_95 = x_87;
x_96 = x_174;
goto block_125;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
lean_dec(x_171);
x_176 = lean_ctor_get(x_169, 1);
lean_inc(x_176);
lean_dec(x_169);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_177 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_176, x_2, x_168, x_7, x_8, x_9, x_175);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_unbox(x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
lean_dec(x_128);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
x_95 = x_87;
x_96 = x_180;
goto block_125;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
lean_dec(x_177);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_128);
x_95 = x_182;
x_96 = x_181;
goto block_125;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_128);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
x_183 = lean_ctor_get(x_177, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_177, 1);
lean_inc(x_184);
lean_dec(x_177);
x_28 = x_183;
x_29 = x_184;
goto block_35;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_128);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_185 = lean_ctor_get(x_171, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_171, 1);
lean_inc(x_186);
lean_dec(x_171);
x_28 = x_185;
x_29 = x_186;
goto block_35;
}
}
}
block_125:
{
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_97; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_3);
x_97 = 0;
x_36 = x_97;
x_37 = x_96;
goto block_75;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
lean_dec(x_95);
lean_inc(x_4);
x_99 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_96);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_4);
lean_dec(x_3);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_104 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_98, x_87, x_93, x_92, x_103, x_6, x_7, x_8, x_9, x_102);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_unbox(x_105);
lean_dec(x_105);
x_36 = x_107;
x_37 = x_106;
goto block_75;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_26);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
lean_dec(x_104);
x_28 = x_108;
x_29 = x_109;
goto block_35;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_110 = lean_ctor_get(x_99, 1);
lean_inc(x_110);
lean_dec(x_99);
x_111 = l_Lean_MessageData_ofName(x_3);
x_112 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_115, x_6, x_7, x_8, x_9, x_110);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_119 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_98, x_87, x_93, x_92, x_117, x_6, x_7, x_8, x_9, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_unbox(x_120);
lean_dec(x_120);
x_36 = x_122;
x_37 = x_121;
goto block_75;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_26);
x_123 = lean_ctor_get(x_119, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_28 = x_123;
x_29 = x_124;
goto block_35;
}
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_187 = lean_ctor_get(x_84, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_84, 1);
lean_inc(x_188);
lean_dec(x_84);
x_28 = x_187;
x_29 = x_188;
goto block_35;
}
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lean_ctor_get(x_76, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_76, 1);
lean_inc(x_190);
lean_dec(x_76);
x_28 = x_189;
x_29 = x_190;
goto block_35;
}
block_35:
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
block_75:
{
if (x_36 == 0)
{
lean_object* x_38; uint8_t x_39; 
lean_dec(x_26);
x_38 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = 0;
x_42 = lean_box(x_41);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
else
{
uint8_t x_47; lean_object* x_48; 
x_47 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_48 = l_Lean_Meta_processPostponed(x_5, x_47, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_26);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = lean_box(x_47);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_box(x_47);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_12);
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_dec(x_48);
x_60 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_PersistentArray_append___rarg(x_26, x_61);
x_64 = l_Lean_Meta_setPostponed(x_63, x_6, x_7, x_8, x_9, x_62);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = 1;
x_68 = lean_box(x_67);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = 1;
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_26);
x_73 = lean_ctor_get(x_48, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_48, 1);
lean_inc(x_74);
lean_dec(x_48);
x_28 = x_73;
x_29 = x_74;
goto block_35;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_211; lean_object* x_212; lean_object* x_243; 
x_191 = lean_ctor_get(x_16, 0);
x_192 = lean_ctor_get(x_16, 1);
x_193 = lean_ctor_get(x_16, 2);
x_194 = lean_ctor_get(x_16, 3);
x_195 = lean_ctor_get(x_16, 4);
x_196 = lean_ctor_get(x_16, 6);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_16);
x_197 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
x_198 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_198, 0, x_191);
lean_ctor_set(x_198, 1, x_192);
lean_ctor_set(x_198, 2, x_193);
lean_ctor_set(x_198, 3, x_194);
lean_ctor_set(x_198, 4, x_195);
lean_ctor_set(x_198, 5, x_197);
lean_ctor_set(x_198, 6, x_196);
lean_ctor_set(x_15, 1, x_198);
x_199 = lean_st_ref_set(x_7, x_15, x_17);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_201 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_3);
x_243 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_203);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = l_Lean_ConstantInfo_levelParams(x_244);
x_247 = lean_box(0);
x_248 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_246, x_247, x_6, x_7, x_8, x_9, x_245);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
lean_inc(x_9);
lean_inc(x_8);
x_251 = l_Lean_Core_instantiateValueLevelParams(x_244, x_249, x_8, x_9, x_250);
lean_dec(x_244);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_293; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_box(0);
lean_inc(x_6);
x_255 = l_Lean_Meta_lambdaMetaTelescope(x_252, x_254, x_6, x_7, x_8, x_9, x_253);
lean_dec(x_252);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_255, 1);
lean_inc(x_258);
lean_dec(x_255);
x_259 = lean_ctor_get(x_256, 0);
lean_inc(x_259);
lean_dec(x_256);
x_260 = lean_ctor_get(x_257, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_257, 1);
lean_inc(x_261);
lean_dec(x_257);
x_293 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_261);
if (lean_obj_tag(x_293) == 0)
{
lean_dec(x_293);
lean_dec(x_2);
lean_dec(x_1);
x_262 = x_254;
x_263 = x_258;
goto block_292;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; uint8_t x_302; uint8_t x_303; uint8_t x_304; uint8_t x_305; uint8_t x_306; uint8_t x_307; uint8_t x_308; uint8_t x_309; uint8_t x_310; uint8_t x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_294 = lean_ctor_get(x_6, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 0);
lean_inc(x_295);
lean_dec(x_293);
x_296 = lean_ctor_get(x_6, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_6, 2);
lean_inc(x_297);
x_298 = lean_ctor_get(x_6, 3);
lean_inc(x_298);
x_299 = lean_ctor_get(x_6, 4);
lean_inc(x_299);
x_300 = lean_ctor_get(x_6, 5);
lean_inc(x_300);
x_301 = lean_ctor_get_uint8(x_294, 0);
x_302 = lean_ctor_get_uint8(x_294, 1);
x_303 = lean_ctor_get_uint8(x_294, 2);
x_304 = lean_ctor_get_uint8(x_294, 3);
x_305 = lean_ctor_get_uint8(x_294, 4);
x_306 = lean_ctor_get_uint8(x_294, 6);
x_307 = lean_ctor_get_uint8(x_294, 7);
x_308 = lean_ctor_get_uint8(x_294, 8);
x_309 = lean_ctor_get_uint8(x_294, 9);
x_310 = lean_ctor_get_uint8(x_294, 10);
x_311 = lean_ctor_get_uint8(x_294, 11);
if (lean_is_exclusive(x_294)) {
 x_312 = x_294;
} else {
 lean_dec_ref(x_294);
 x_312 = lean_box(0);
}
x_313 = 0;
if (lean_is_scalar(x_312)) {
 x_314 = lean_alloc_ctor(0, 0, 12);
} else {
 x_314 = x_312;
}
lean_ctor_set_uint8(x_314, 0, x_301);
lean_ctor_set_uint8(x_314, 1, x_302);
lean_ctor_set_uint8(x_314, 2, x_303);
lean_ctor_set_uint8(x_314, 3, x_304);
lean_ctor_set_uint8(x_314, 4, x_305);
lean_ctor_set_uint8(x_314, 5, x_313);
lean_ctor_set_uint8(x_314, 6, x_306);
lean_ctor_set_uint8(x_314, 7, x_307);
lean_ctor_set_uint8(x_314, 8, x_308);
lean_ctor_set_uint8(x_314, 9, x_309);
lean_ctor_set_uint8(x_314, 10, x_310);
lean_ctor_set_uint8(x_314, 11, x_311);
x_315 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_296);
lean_ctor_set(x_315, 2, x_297);
lean_ctor_set(x_315, 3, x_298);
lean_ctor_set(x_315, 4, x_299);
lean_ctor_set(x_315, 5, x_300);
x_316 = lean_ctor_get(x_295, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_315);
x_318 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_317, x_1, x_315, x_7, x_8, x_9, x_258);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; uint8_t x_320; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_unbox(x_319);
lean_dec(x_319);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_295);
lean_dec(x_2);
x_321 = lean_ctor_get(x_318, 1);
lean_inc(x_321);
lean_dec(x_318);
x_262 = x_254;
x_263 = x_321;
goto block_292;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
lean_dec(x_318);
x_323 = lean_ctor_get(x_316, 1);
lean_inc(x_323);
lean_dec(x_316);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_324 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_323, x_2, x_315, x_7, x_8, x_9, x_322);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; uint8_t x_326; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_unbox(x_325);
lean_dec(x_325);
if (x_326 == 0)
{
lean_object* x_327; 
lean_dec(x_295);
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
lean_dec(x_324);
x_262 = x_254;
x_263 = x_327;
goto block_292;
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_324, 1);
lean_inc(x_328);
lean_dec(x_324);
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_295);
x_262 = x_329;
x_263 = x_328;
goto block_292;
}
}
else
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_295);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_202);
lean_dec(x_4);
lean_dec(x_3);
x_330 = lean_ctor_get(x_324, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_324, 1);
lean_inc(x_331);
lean_dec(x_324);
x_204 = x_330;
x_205 = x_331;
goto block_210;
}
}
}
else
{
lean_object* x_332; lean_object* x_333; 
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_295);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_202);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_332 = lean_ctor_get(x_318, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_318, 1);
lean_inc(x_333);
lean_dec(x_318);
x_204 = x_332;
x_205 = x_333;
goto block_210;
}
}
block_292:
{
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_264; 
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_4);
lean_dec(x_3);
x_264 = 0;
x_211 = x_264;
x_212 = x_263;
goto block_242;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_265 = lean_ctor_get(x_262, 0);
lean_inc(x_265);
lean_dec(x_262);
lean_inc(x_4);
x_266 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_263);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_unbox(x_267);
lean_dec(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_4);
lean_dec(x_3);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
lean_dec(x_266);
x_270 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_271 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_265, x_254, x_260, x_259, x_270, x_6, x_7, x_8, x_9, x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_unbox(x_272);
lean_dec(x_272);
x_211 = x_274;
x_212 = x_273;
goto block_242;
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_202);
x_275 = lean_ctor_get(x_271, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_271, 1);
lean_inc(x_276);
lean_dec(x_271);
x_204 = x_275;
x_205 = x_276;
goto block_210;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_277 = lean_ctor_get(x_266, 1);
lean_inc(x_277);
lean_dec(x_266);
x_278 = l_Lean_MessageData_ofName(x_3);
x_279 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_280 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
x_281 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4;
x_282 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_282, x_6, x_7, x_8, x_9, x_277);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_286 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_265, x_254, x_260, x_259, x_284, x_6, x_7, x_8, x_9, x_285);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_unbox(x_287);
lean_dec(x_287);
x_211 = x_289;
x_212 = x_288;
goto block_242;
}
else
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_202);
x_290 = lean_ctor_get(x_286, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_286, 1);
lean_inc(x_291);
lean_dec(x_286);
x_204 = x_290;
x_205 = x_291;
goto block_210;
}
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_202);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_334 = lean_ctor_get(x_251, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_251, 1);
lean_inc(x_335);
lean_dec(x_251);
x_204 = x_334;
x_205 = x_335;
goto block_210;
}
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_202);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_336 = lean_ctor_get(x_243, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_243, 1);
lean_inc(x_337);
lean_dec(x_243);
x_204 = x_336;
x_205 = x_337;
goto block_210;
}
block_210:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_205);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
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
lean_ctor_set(x_209, 0, x_204);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
block_242:
{
if (x_211 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_202);
x_213 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_212);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_215 = x_213;
} else {
 lean_dec_ref(x_213);
 x_215 = lean_box(0);
}
x_216 = 0;
x_217 = lean_box(x_216);
if (lean_is_scalar(x_215)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_215;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_214);
return x_218;
}
else
{
uint8_t x_219; lean_object* x_220; 
x_219 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_220 = l_Lean_Meta_processPostponed(x_5, x_219, x_6, x_7, x_8, x_9, x_212);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_202);
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
x_224 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_223);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
x_227 = lean_box(x_219);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_12);
x_229 = lean_ctor_get(x_220, 1);
lean_inc(x_229);
lean_dec(x_220);
x_230 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_229);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = l_Lean_PersistentArray_append___rarg(x_202, x_231);
x_234 = l_Lean_Meta_setPostponed(x_233, x_6, x_7, x_8, x_9, x_232);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_236 = x_234;
} else {
 lean_dec_ref(x_234);
 x_236 = lean_box(0);
}
x_237 = 1;
x_238 = lean_box(x_237);
if (lean_is_scalar(x_236)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_236;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_235);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_202);
x_240 = lean_ctor_get(x_220, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_220, 1);
lean_inc(x_241);
lean_dec(x_220);
x_204 = x_240;
x_205 = x_241;
goto block_210;
}
}
}
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_363; lean_object* x_364; lean_object* x_395; 
x_338 = lean_ctor_get(x_15, 0);
x_339 = lean_ctor_get(x_15, 2);
x_340 = lean_ctor_get(x_15, 3);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_15);
x_341 = lean_ctor_get(x_16, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_16, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_16, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_16, 3);
lean_inc(x_344);
x_345 = lean_ctor_get(x_16, 4);
lean_inc(x_345);
x_346 = lean_ctor_get(x_16, 6);
lean_inc(x_346);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 lean_ctor_release(x_16, 6);
 x_347 = x_16;
} else {
 lean_dec_ref(x_16);
 x_347 = lean_box(0);
}
x_348 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__2;
if (lean_is_scalar(x_347)) {
 x_349 = lean_alloc_ctor(0, 7, 0);
} else {
 x_349 = x_347;
}
lean_ctor_set(x_349, 0, x_341);
lean_ctor_set(x_349, 1, x_342);
lean_ctor_set(x_349, 2, x_343);
lean_ctor_set(x_349, 3, x_344);
lean_ctor_set(x_349, 4, x_345);
lean_ctor_set(x_349, 5, x_348);
lean_ctor_set(x_349, 6, x_346);
x_350 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_350, 0, x_338);
lean_ctor_set(x_350, 1, x_349);
lean_ctor_set(x_350, 2, x_339);
lean_ctor_set(x_350, 3, x_340);
x_351 = lean_st_ref_set(x_7, x_350, x_17);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec(x_351);
x_353 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_352);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
lean_inc(x_3);
x_395 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_6, x_7, x_8, x_9, x_355);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = l_Lean_ConstantInfo_levelParams(x_396);
x_399 = lean_box(0);
x_400 = l_List_mapM_loop___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__1(x_398, x_399, x_6, x_7, x_8, x_9, x_397);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
lean_inc(x_9);
lean_inc(x_8);
x_403 = l_Lean_Core_instantiateValueLevelParams(x_396, x_401, x_8, x_9, x_402);
lean_dec(x_396);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_445; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_406 = lean_box(0);
lean_inc(x_6);
x_407 = l_Lean_Meta_lambdaMetaTelescope(x_404, x_406, x_6, x_7, x_8, x_9, x_405);
lean_dec(x_404);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_407, 1);
lean_inc(x_410);
lean_dec(x_407);
x_411 = lean_ctor_get(x_408, 0);
lean_inc(x_411);
lean_dec(x_408);
x_412 = lean_ctor_get(x_409, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_409, 1);
lean_inc(x_413);
lean_dec(x_409);
x_445 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_413);
if (lean_obj_tag(x_445) == 0)
{
lean_dec(x_445);
lean_dec(x_2);
lean_dec(x_1);
x_414 = x_406;
x_415 = x_410;
goto block_444;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; uint8_t x_454; uint8_t x_455; uint8_t x_456; uint8_t x_457; uint8_t x_458; uint8_t x_459; uint8_t x_460; uint8_t x_461; uint8_t x_462; uint8_t x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_446 = lean_ctor_get(x_6, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 0);
lean_inc(x_447);
lean_dec(x_445);
x_448 = lean_ctor_get(x_6, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_6, 2);
lean_inc(x_449);
x_450 = lean_ctor_get(x_6, 3);
lean_inc(x_450);
x_451 = lean_ctor_get(x_6, 4);
lean_inc(x_451);
x_452 = lean_ctor_get(x_6, 5);
lean_inc(x_452);
x_453 = lean_ctor_get_uint8(x_446, 0);
x_454 = lean_ctor_get_uint8(x_446, 1);
x_455 = lean_ctor_get_uint8(x_446, 2);
x_456 = lean_ctor_get_uint8(x_446, 3);
x_457 = lean_ctor_get_uint8(x_446, 4);
x_458 = lean_ctor_get_uint8(x_446, 6);
x_459 = lean_ctor_get_uint8(x_446, 7);
x_460 = lean_ctor_get_uint8(x_446, 8);
x_461 = lean_ctor_get_uint8(x_446, 9);
x_462 = lean_ctor_get_uint8(x_446, 10);
x_463 = lean_ctor_get_uint8(x_446, 11);
if (lean_is_exclusive(x_446)) {
 x_464 = x_446;
} else {
 lean_dec_ref(x_446);
 x_464 = lean_box(0);
}
x_465 = 0;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(0, 0, 12);
} else {
 x_466 = x_464;
}
lean_ctor_set_uint8(x_466, 0, x_453);
lean_ctor_set_uint8(x_466, 1, x_454);
lean_ctor_set_uint8(x_466, 2, x_455);
lean_ctor_set_uint8(x_466, 3, x_456);
lean_ctor_set_uint8(x_466, 4, x_457);
lean_ctor_set_uint8(x_466, 5, x_465);
lean_ctor_set_uint8(x_466, 6, x_458);
lean_ctor_set_uint8(x_466, 7, x_459);
lean_ctor_set_uint8(x_466, 8, x_460);
lean_ctor_set_uint8(x_466, 9, x_461);
lean_ctor_set_uint8(x_466, 10, x_462);
lean_ctor_set_uint8(x_466, 11, x_463);
x_467 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_448);
lean_ctor_set(x_467, 2, x_449);
lean_ctor_set(x_467, 3, x_450);
lean_ctor_set(x_467, 4, x_451);
lean_ctor_set(x_467, 5, x_452);
x_468 = lean_ctor_get(x_447, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_467);
x_470 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_469, x_1, x_467, x_7, x_8, x_9, x_410);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; uint8_t x_472; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_unbox(x_471);
lean_dec(x_471);
if (x_472 == 0)
{
lean_object* x_473; 
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_447);
lean_dec(x_2);
x_473 = lean_ctor_get(x_470, 1);
lean_inc(x_473);
lean_dec(x_470);
x_414 = x_406;
x_415 = x_473;
goto block_444;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_474 = lean_ctor_get(x_470, 1);
lean_inc(x_474);
lean_dec(x_470);
x_475 = lean_ctor_get(x_468, 1);
lean_inc(x_475);
lean_dec(x_468);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_476 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_475, x_2, x_467, x_7, x_8, x_9, x_474);
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
lean_dec(x_447);
x_479 = lean_ctor_get(x_476, 1);
lean_inc(x_479);
lean_dec(x_476);
x_414 = x_406;
x_415 = x_479;
goto block_444;
}
else
{
lean_object* x_480; lean_object* x_481; 
x_480 = lean_ctor_get(x_476, 1);
lean_inc(x_480);
lean_dec(x_476);
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_447);
x_414 = x_481;
x_415 = x_480;
goto block_444;
}
}
else
{
lean_object* x_482; lean_object* x_483; 
lean_dec(x_447);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_354);
lean_dec(x_4);
lean_dec(x_3);
x_482 = lean_ctor_get(x_476, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_476, 1);
lean_inc(x_483);
lean_dec(x_476);
x_356 = x_482;
x_357 = x_483;
goto block_362;
}
}
}
else
{
lean_object* x_484; lean_object* x_485; 
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_447);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_354);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_484 = lean_ctor_get(x_470, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_470, 1);
lean_inc(x_485);
lean_dec(x_470);
x_356 = x_484;
x_357 = x_485;
goto block_362;
}
}
block_444:
{
if (lean_obj_tag(x_414) == 0)
{
uint8_t x_416; 
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_4);
lean_dec(x_3);
x_416 = 0;
x_363 = x_416;
x_364 = x_415;
goto block_394;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_417 = lean_ctor_get(x_414, 0);
lean_inc(x_417);
lean_dec(x_414);
lean_inc(x_4);
x_418 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_6, x_7, x_8, x_9, x_415);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_unbox(x_419);
lean_dec(x_419);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_4);
lean_dec(x_3);
x_421 = lean_ctor_get(x_418, 1);
lean_inc(x_421);
lean_dec(x_418);
x_422 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_423 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_417, x_406, x_412, x_411, x_422, x_6, x_7, x_8, x_9, x_421);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; uint8_t x_426; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = lean_unbox(x_424);
lean_dec(x_424);
x_363 = x_426;
x_364 = x_425;
goto block_394;
}
else
{
lean_object* x_427; lean_object* x_428; 
lean_dec(x_354);
x_427 = lean_ctor_get(x_423, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_423, 1);
lean_inc(x_428);
lean_dec(x_423);
x_356 = x_427;
x_357 = x_428;
goto block_362;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_429 = lean_ctor_get(x_418, 1);
lean_inc(x_429);
lean_dec(x_418);
x_430 = l_Lean_MessageData_ofName(x_3);
x_431 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__6;
x_432 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_430);
x_433 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___closed__4;
x_434 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
x_435 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_434, x_6, x_7, x_8, x_9, x_429);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_438 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__4___lambda__3(x_417, x_406, x_412, x_411, x_436, x_6, x_7, x_8, x_9, x_437);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; uint8_t x_441; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_441 = lean_unbox(x_439);
lean_dec(x_439);
x_363 = x_441;
x_364 = x_440;
goto block_394;
}
else
{
lean_object* x_442; lean_object* x_443; 
lean_dec(x_354);
x_442 = lean_ctor_get(x_438, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_438, 1);
lean_inc(x_443);
lean_dec(x_438);
x_356 = x_442;
x_357 = x_443;
goto block_362;
}
}
}
}
}
else
{
lean_object* x_486; lean_object* x_487; 
lean_dec(x_354);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_486 = lean_ctor_get(x_403, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_403, 1);
lean_inc(x_487);
lean_dec(x_403);
x_356 = x_486;
x_357 = x_487;
goto block_362;
}
}
else
{
lean_object* x_488; lean_object* x_489; 
lean_dec(x_354);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_488 = lean_ctor_get(x_395, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_395, 1);
lean_inc(x_489);
lean_dec(x_395);
x_356 = x_488;
x_357 = x_489;
goto block_362;
}
block_362:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_358 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_357);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
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
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
block_394:
{
if (x_363 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_354);
x_365 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_364);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_367 = x_365;
} else {
 lean_dec_ref(x_365);
 x_367 = lean_box(0);
}
x_368 = 0;
x_369 = lean_box(x_368);
if (lean_is_scalar(x_367)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_367;
}
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_366);
return x_370;
}
else
{
uint8_t x_371; lean_object* x_372; 
x_371 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_372 = l_Lean_Meta_processPostponed(x_5, x_371, x_6, x_7, x_8, x_9, x_364);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; uint8_t x_374; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_unbox(x_373);
lean_dec(x_373);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_354);
x_375 = lean_ctor_get(x_372, 1);
lean_inc(x_375);
lean_dec(x_372);
x_376 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_375);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_378 = x_376;
} else {
 lean_dec_ref(x_376);
 x_378 = lean_box(0);
}
x_379 = lean_box(x_371);
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_377);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_12);
x_381 = lean_ctor_get(x_372, 1);
lean_inc(x_381);
lean_dec(x_372);
x_382 = l_Lean_Meta_getPostponed___rarg(x_7, x_8, x_9, x_381);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
x_385 = l_Lean_PersistentArray_append___rarg(x_354, x_383);
x_386 = l_Lean_Meta_setPostponed(x_385, x_6, x_7, x_8, x_9, x_384);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_387 = lean_ctor_get(x_386, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_388 = x_386;
} else {
 lean_dec_ref(x_386);
 x_388 = lean_box(0);
}
x_389 = 1;
x_390 = lean_box(x_389);
if (lean_is_scalar(x_388)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_388;
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_387);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; 
lean_dec(x_354);
x_392 = lean_ctor_get(x_372, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_372, 1);
lean_inc(x_393);
lean_dec(x_372);
x_356 = x_392;
x_357 = x_393;
goto block_362;
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2757____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_967____closed__12;
x_2 = lean_unsigned_to_nat(2757u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2757_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2757____closed__1;
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
l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2757____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2757____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2757____closed__1);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2757_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
